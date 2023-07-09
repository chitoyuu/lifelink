# lifelink

Erase covariant lifetime parameters from anything, with generic associated types.

```toml
[dependencies]
lifelink = { version = "0.1.1" }
```

Like `cryo`, `lifelink` allows you to use the resulting types in dynamic environments where lifetime is unpredictable, like runtimes of garbage-collected scripting languages, or where `Any` is required. Unlike `cryo`, the interface is not restricted to primitive references: it works on everything with covariant lifetime parameters though GATs.

The `generic_associated_types` feature has been stabilized in Rust 1.65. If a pinned nightly compiler before the stabilization release is required, the `nightly` feature can be enabled which adds the appropriate `feature` attribute.

## Examples

Simple case with just a reference:

```rust
use std::thread::spawn;
use std::sync::atomic::{AtomicUsize, Ordering};
use lifelink::{lifelink, Lifelink, RefCtor};

let answer = AtomicUsize::new(0);

lifelink!(lifelink: RefCtor<AtomicUsize> = &answer);

{
    let guard = lifelink.get().unwrap();
    assert_eq!(0, guard.load(Ordering::Relaxed));
    guard.store(42, Ordering::Release);
}

assert_eq!(42, answer.load(Ordering::Acquire));
```

A more involved example with multiple lifetime parameters, unrelated type parameters. and threads:

```rust
use std::thread::spawn;
use std::time::Duration;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::channel;
use std::marker::PhantomData;
use lifelink::{lifelink, Lifelink, Ctor, Cov};

#[derive(Copy, Clone)]
struct Answers<'a, 'b, 'c, T> {
    first: &'a AtomicUsize,
    second: &'b AtomicUsize,
    third: &'c AtomicUsize,
    rest: T,
}

struct AnswersCtor<T> {
    _marker: PhantomData<T>,
}

impl<T: 'static> Ctor for AnswersCtor<T> {
    // The lifetimes can be unified here, due to covariance
    type Ty<'a> = Answers<'a, 'a, 'a, T>;
}

// An invocation of `lifelink::cov!` on the constructor type is required
// to prove covariance to the type system. This only compiles for types that
// can be proved by Rust to be covariant. See docs on the Cov trait for more
// details.
lifelink::cov!(<T: 'static> AnswersCtor<T>);

fn compute<'a, 'b, 'c>(answers: Answers<'a, 'b, 'c, ()>) {
    lifelink!(lifelink: AnswersCtor<()> = answers);
    let (send, recv) = channel();
    
    spawn(move || {
        let guard = lifelink.get().unwrap();
        guard.first.store(42, Ordering::Release);
        guard.second.store(42, Ordering::Release);
        guard.third.store(42, Ordering::Release);
        send.send(()).unwrap();
    });

    // Unlike `cryo`, `lifelink` does *not* attempt to wait until the `'static`
    // handle is dropped. As such, a way to wait for task completion external
    // to `lifelink` is required. See the Caveats section of README for more
    // details, and the rationale behind this decision.
    recv.recv_timeout(Duration::from_millis(20)).unwrap();

    assert_eq!(42, answers.first.load(Ordering::Acquire));
    assert_eq!(42, answers.second.load(Ordering::Acquire));
    assert_eq!(42, answers.third.load(Ordering::Acquire));
}

let first = AtomicUsize::new(0);
let second = AtomicUsize::new(0);
let third = AtomicUsize::new(0);

compute(Answers {
    first: &first,
    second: &second,
    third: &third,
    rest: (),
});
```

## Caveats

`Lifelink` can only ever give out shared / immutable references. This is because Rust allows moves by default, making mutable references to types with lifetime parameters too hard to reason about, and almost impossible to use correctly unless reduced to uselessness. Instead, users have to use interior mutability in a way that maintains covariance (which, thankfully, Rust will help prove in a `Cov` impl).

Unlike `cryo`, `lifelink` does *not* attempt to wait until the `'static` handle is dropped. It's more than happy to drop or unwrap a `Deathtouch`, if there isn't a `Guard` in scope somewhere that *precise moment*. This may come as surprising, but is a conscious decision to make `lifelink` work in tandem with environments where lifetime is unpredictable, e.g. a garbage collected scripting language, where it's much better to get a error than a deadlock from a misbehaving script. As such, a way to wait for task completion external to `lifelink` is required.

## Feature flags

- `nightly` - Adds `feature(generic_associated_types)` to the top of the crate, which would allow the crate to compile on a nightly compiler earlier than 1.65 (when the feature was stabilized).

## License

MIT OR Apache-2.0