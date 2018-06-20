# boxext

## Extensions to the `Box` type

This crate provides extra initializer methods for `Box`, working around the
current (as of writing) shortcomings from `Box::new`:

* Since Rust 1.12, constructs such as `Box::new([0; 4096])` first create a
temporary object on the stack before copying it into the newly allocated
space (e.g. [issue #50047]).

* Constructs such as `Box::new(some_function_call())` first get the result
from the function call on the stack before copying it into the newly
allocated space.

[issue #50047]: https://github.com/rust-lang/rust/issues/50047

Both can be worked around with some contortion but with caveats. This crate
provides helpers doing those contortions for you, but can't deal with the
caveats. Those caveats are essentially the same as why the unstable
placement features were removed in nightly 1.27, namely that there are no
guarantees that things will actually happen in place (and they don't in
debug builds).

The crates adds the following helper methods to the `Box` type:

* [`new_with`], which takes a function or closure returning the object that
will be placed in the Box.

* [`new_zeroed`], which creates an object filled with zeroes, possibly
using [`calloc`]/[`HeapAlloc(..., HEAP_ZERO_MEMORY, ...)`]/
[`mallocx(..., MALLOCX_ZERO)`] under the hood.

* [`try_new`], [`try_new_with`], and [`try_new_zeroed`], which are equivalent
to `new`, `new_with` and `new_zeroed`, but don't panic on allocation
failure.

[`new_with`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.new_with
[`new_zeroed`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.new_zeroed
[`try_new`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.try_new
[`try_new_with`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.try_new_with
[`try_new_zeroed`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.try_new_zeroed
[`calloc`]: http://pubs.opengroup.org/onlinepubs/009695399/functions/calloc.html
[`HeapAlloc(..., HEAP_ZERO_MEMORY, ...)`]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa366597(v=vs.85).aspx#HEAP_ZERO_MEMORY
[`mallocx(..., MALLOCX_ZERO)`]: http://jemalloc.net/jemalloc.3.html#MALLOCX_ZERO

### Examples

```rust
extern crate boxext;
use boxext::BoxExt;

struct Foo(usize, usize);

impl Foo {
    fn new(a: usize, b: usize) -> Self {
        Foo(a, b)
   }
}

impl Default for Foo {
    fn default() -> Self {
        Foo::new(0, 1)
    }
}

fn main() {
    // equivalent to `Box::new(Foo(1, 2))`
    let buf = Box::new_with(|| Foo(1, 2));

    // equivalent to `Box::new(Foo::new(2, 3))`
    let buf = Box::new_with(|| Foo::new(2, 3));

    // equivalent to `Box::new(Foo::default())`
    let buf = Box::new_with(Foo::default);

    // equivalent to `Box::new([0usize; 64])`
    let buf: Box<[usize; 64]> = Box::new_zeroed();
}
```

### Features

* `std` (enabled by default): Uses libstd. Can be disabled to allow use
with `no_std` code, in which case `allocator_api` needs to be enabled.

* `allocator_api`: Add similar helpers to the `Box` type from the
`allocator_api` crate.

License: Apache-2.0/MIT
