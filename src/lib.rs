#![doc = include_str!("../README.md")]
#![cfg_attr(feature = "nightly", feature(generic_associated_types))]

use std::cell::Cell;
use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::null_mut;
use std::sync::Arc;

use parking_lot::{Mutex, MutexGuard};

type Inner = Arc<Mutex<*mut u8>>;

/// A `'static` handle through which a value with a covariant lifetime parameter can
/// temporarily be accessed.
///
/// `Lifelink<C>` implements [`Send`] and [`Sync`] when the wrapped values produced by
/// `C` are [`Send`].
///
/// See [`Lifelink::new`] for an example.
pub struct Lifelink<C: Ctor> {
    inner: Inner,
    _marker: PhantomData<C::Ty<'static>>,
}

// SAFETY: Inner is a Mutex, and `get` requires &mut self, so it's impossible to obtain
// multiple references to a Send-only type by Sending the Lifelink itself.
unsafe impl<C: SendCtor> Send for Lifelink<C> {}
unsafe impl<C: SendCtor> Sync for Lifelink<C> {}

impl<C: Ctor> Lifelink<C> {
    /// Create a pair of [`Lifelink`] and [`Deathtouch`] values wrapping `thing`, which
    /// will be kept alive and accessible through `Lifelink` until the [`Deathtouch`]
    /// is dropped.
    ///
    /// Calling [`Lifelink::new`] is safe as long as `C::Ty` values are covariant over the
    /// lifetime parameter.
    ///
    /// # Example
    ///
    /// ```rust
    /// #![feature(generic_associated_types)]
    ///
    /// use std::thread::spawn;
    /// use std::sync::atomic::{AtomicUsize, Ordering};
    /// use lifelink::{Lifelink, RefCtor};
    ///
    /// let answer = AtomicUsize::new(0);
    ///
    /// let (mut lifelink, deathtouch) = Lifelink::<RefCtor<AtomicUsize>>::new(&answer);
    ///
    /// {
    ///     let guard = lifelink.get().unwrap();
    ///     assert_eq!(0, guard.load(Ordering::Relaxed));
    ///     guard.store(42, Ordering::Release);
    /// }
    ///
    /// assert_eq!(42, deathtouch.unwrap().load(Ordering::Acquire));
    /// ```
    #[allow(clippy::needless_lifetimes)] // False positive
    pub fn new<'a>(thing: C::Ty<'a>) -> (Lifelink<C>, Deathtouch<'a, C>) {
        let thing = Box::new(thing);
        let ptr = Box::into_raw(thing) as *mut u8;
        let inner = Arc::new(Mutex::new(ptr));

        let lifelink = Lifelink {
            inner: Arc::clone(&inner),
            _marker: PhantomData,
        };

        let deathtouch = Deathtouch {
            inner,
            _marker: PhantomData,
        };

        (lifelink, deathtouch)
    }

    /// Returns a guard value that implements [`Deref`] to the wrapped value. Care must be taken
    /// to ensure that this value is dropped properly. Leaking the guard value may lead to a
    /// deadlock.
    pub fn get(&mut self) -> Option<Guard<'_, C>> {
        let lock = self.inner.lock();
        if lock.is_null() {
            None
        } else {
            Some(Guard {
                lock,
                _marker: PhantomData,
            })
        }
    }
}

/// A guard value that provides temporary access to the wrapped value. Care must be taken
/// to ensure that this value is dropped properly. Leaking the guard value may lead to a
/// deadlock.
///
/// `Guard<'_, C>` implements [`Send`] and [`Sync`] when the wrapped values produced by
/// `C` are [`Sync`].
pub struct Guard<'a, C: Ctor> {
    lock: MutexGuard<'a, *mut u8>,
    _marker: PhantomData<C::Ty<'static>>,
}

// SAFETY: Shared references are Send / Sync when and only when the value referred to is
// Sync.
unsafe impl<'a, C: SyncCtor> Send for Guard<'a, C> {}
unsafe impl<'a, C: SyncCtor> Sync for Guard<'a, C> {}

impl<'a, C> Deref for Guard<'a, C>
where
    C: Ctor + Cov,
{
    type Target = C::Ty<'a>;
    fn deref(&self) -> &Self::Target {
        let ptr: *mut u8 = *self.lock;
        // SAFETY: User promised so by implementing `Cov`.
        unsafe { &*(ptr as *const C::Ty<'a>) }
    }
}

/// A guard value that preserves compile-time lifetime information from the value passed
/// to [`Lifelink::new`].
///
/// This will block the calling thread when unwrapped or dropped, until all [`Guard`]s
/// currently alive go out of the scope. The value can then no longer be accessed from the
/// corresponding [`Lifelink`].
///
/// Note that Unlike `cryo`, this does *not* attempt to wait until the [`Lifelink`] handle
/// itself is dropped, only the [`Guard`] values it produces.  See the Caveats section of
/// README for more details.
pub struct Deathtouch<'a, C: Ctor> {
    inner: Inner,

    /// Invariant over 'a
    _marker: PhantomData<Cell<&'a C::Ty<'a>>>,
}

// SAFETY: The only public interfaces of this type takes `self`, and waits until there are
// no other Guards alive.
unsafe impl<'a, C: SendCtor> Send for Deathtouch<'a, C> {}

impl<'a, C: Ctor> Deathtouch<'a, C> {
    fn extract(&mut self) -> Option<C::Ty<'a>> {
        let mut lock = self.inner.lock();
        let ptr: *mut u8 = std::mem::replace(&mut *lock, null_mut());
        if ptr.is_null() {
            None
        } else {
            // SAFETY: this pointer is produced in Lifelink::new with Box::into_raw, and
            // the Deathtouch type itself is invariant over 'a
            unsafe { Some(*Box::from_raw(ptr as *mut C::Ty<'a>)) }
        }
    }

    /// Unwrap the contained value and return it. This will block until there is no
    /// other references to the value, so that compile-time lifetime invariants hold.
    ///
    /// See the module-level documentation for examples.
    pub fn unwrap(mut self) -> C::Ty<'a> {
        self.extract().unwrap()
    }
}

impl<'a, C: Ctor> Drop for Deathtouch<'a, C> {
    fn drop(&mut self) {
        self.extract();
    }
}

/// Trait for type constructors that take one single lifetime parameter. See also
/// [`Cov`] for [`Deref`] on [`Guard`].
pub trait Ctor {
    type Ty<'a>;
}

/// Trait for type constructors that produce types whose references are covariant over the
/// lifetime parameter.
///
/// For most valid types, this could simply be implemented by returning the input reference
/// to `cov` and letting Rust figure out the rest:
///
/// ```rust
/// #![feature(generic_associated_types)]
/// # use lifelink::*;
///
/// struct FooCtor;
/// struct Foo<'a>(&'a u8);
/// impl Ctor for FooCtor {
///     type Ty<'a> = Foo<'a>;
/// }
///
/// unsafe impl Cov for FooCtor {
///     fn cov<'r, 'a, 'b>(r: &'r Self::Ty<'a>) -> &'r Self::Ty<'b>
///     where
///         'a: 'b,
///     {
///         r
///     }
/// }
/// ```
///
/// # Safety
///
/// References to types produced by this type constructor must be covariant over the lifetime
/// parameter.
///
/// This trait is `unsafe` for the reason that it is trivial to write a type-checking
/// implementation of `cov` that is unsound, for every type out there, simply by writing
/// `panic!()`. The trait method is never actually called by the library. It's only here because
/// it's helpful for detecting bugs.
pub unsafe trait Cov: Ctor {
    fn cov<'r, 'a, 'b>(r: &'r Self::Ty<'a>) -> &'r Self::Ty<'b>
    where
        'a: 'b;
}

/// Marker trait implemented for [`Ctor`]s where the constructed types are `Send`.
pub trait SendCtor: Ctor {}
impl<C> SendCtor for C
where
    C: Ctor,
    for<'a> C::Ty<'a>: Send,
{
}

/// Marker trait implemented for [`Ctor`]s where the constructed types are [`Sync`].
pub trait SyncCtor: Ctor {}
impl<C> SyncCtor for C
where
    C: Ctor,
    for<'a> C::Ty<'a>: Sync,
{
}

/// Constructor of references to `'static` values, that implements [`Ctor`] and [`Cov`].
///
/// This is provided for convenience, although if all you need is this, consider using the
/// [`cryo`](https://crates.io/crates/cryo) crate, which is much more mature and compiles on
/// stable today!
pub struct RefCtor<T> {
    _marker: PhantomData<T>,
}

impl<T: 'static> Ctor for RefCtor<T> {
    type Ty<'a> = &'a T;
}

// SAFETY: &'a T is covariant over 'a when T is 'static
unsafe impl<T: 'static> Cov for RefCtor<T> {
    fn cov<'r, 'a, 'b>(r: &'r Self::Ty<'a>) -> &'r Self::Ty<'b>
    where
        'a: 'b,
    {
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    #[test]
    fn local() {
        let answer = AtomicUsize::new(0);
        let mut leaked;

        {
            let (mut lifelink, _deathtouch) = Lifelink::<RefCtor<AtomicUsize>>::new(&answer);
            assert_eq!(
                Some(0),
                lifelink.get().map(|foo| foo.load(Ordering::Relaxed))
            );
            leaked = lifelink;
        }

        assert!(leaked.get().is_none());
    }

    #[test]
    fn sync() {
        use std::sync::mpsc::channel;
        use std::thread::spawn;

        let answer = AtomicUsize::new(0);

        let (mut lifelink, deathtouch) = Lifelink::<RefCtor<AtomicUsize>>::new(&answer);
        let (send, recv) = channel();

        spawn(move || {
            let guard = lifelink.get().unwrap();
            assert_eq!(0, guard.load(Ordering::Relaxed));
            guard.store(42, Ordering::Release);
            send.send(()).unwrap();
        });

        recv.recv_timeout(Duration::from_millis(20)).unwrap();

        assert_eq!(42, deathtouch.unwrap().load(Ordering::Acquire));
    }
}
