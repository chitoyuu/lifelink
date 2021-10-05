#![cfg_attr(feature = "nightly", feature(generic_associated_types))]

use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::null_mut;
use std::sync::Arc;

use parking_lot::{Mutex, MutexGuard};

type Inner = Arc<Mutex<*mut u8>>;

pub struct Lifelink<C: Ctor> {
    inner: Inner,
    _marker: PhantomData<C::Ty<'static>>,
}

unsafe impl<C: SendCtor> Send for Lifelink<C> {}
unsafe impl<C: SendCtor> Sync for Lifelink<C> {}

impl<C: Ctor> Clone for Lifelink<C> {
    fn clone(&self) -> Self {
        Lifelink {
            inner: Arc::clone(&self.inner),
            _marker: PhantomData,
        }
    }
}

impl<C: Ctor> Lifelink<C> {
    pub fn get(&self) -> Option<Guard<'_, C>> {
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

pub struct Guard<'a, C: Ctor> {
    lock: MutexGuard<'a, *mut u8>,
    _marker: PhantomData<C::Ty<'static>>,
}

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

pub struct Deathtouch<'a, C: Ctor> {
    inner: Inner,
    _marker: PhantomData<C::Ty<'a>>,
}

impl<'a, C: Ctor> Drop for Deathtouch<'a, C> {
    fn drop(&mut self) {
        let mut lock = self.inner.lock();
        let ptr: *mut u8 = std::mem::replace(&mut *lock, null_mut());
        unsafe { drop(Box::from_raw(ptr as *mut C::Ty<'a>)) };
    }
}

/// Create a pair of `Lifelink` and `Deathtouch` values wrapping `thing`, which
/// will be kept alive and accessible through `Lifelink` until the `Deathtouch` is dropped.
#[allow(clippy::needless_lifetimes)] // False positive
pub fn link<'a, C: Ctor>(thing: C::Ty<'a>) -> (Lifelink<C>, Deathtouch<'a, C>) {
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

/// Trait for type constructors that take one single lifetime parameter. See also
/// [`Cov`] for `Deref` on `Guard`.
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
/// #use lifelink::*;
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
/// implementation of `cov` that is unsound, for every type out there, by writing `panic!()`.
/// The trait method is never actually called by the library. It's only here because it's
/// helpful for detecting bugs.
pub unsafe trait Cov: Ctor {
    fn cov<'r, 'a, 'b>(r: &'r Self::Ty<'a>) -> &'r Self::Ty<'b>
    where
        'a: 'b;
}

/// Marker trait implemented for `Ctor`s where the constructed types are `Send`.
pub trait SendCtor: Ctor {}
impl<C> SendCtor for C
where
    C: Ctor,
    for<'a> C::Ty<'a>: Send,
{
}

/// Marker trait implemented for `Ctor`s where the constructed types are `Sync`.
pub trait SyncCtor: Ctor {}
impl<C> SyncCtor for C
where
    C: Ctor,
    for<'a> C::Ty<'a>: Sync,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Foo<'a> {
        _marker: PhantomData<&'a ()>,
    }

    struct FooCtor;
    impl Ctor for FooCtor {
        type Ty<'a> = Foo<'a>;
    }

    #[test]
    fn it_works() {
        let leaked;

        {
            let (lifelink, _deathtouch) = link::<FooCtor>(Foo {
                _marker: PhantomData,
            });
            assert!(lifelink.get().is_some());
            leaked = lifelink;
        }

        assert!(leaked.get().is_none());
    }
}
