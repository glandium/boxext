# boxext

## Extensions to the `Box` type

This crate provides extra initializer methods for `Box`, working around the
current (as of writing) shortcomings from `Box::new`:

* Since Rust 1.12, constructs such as `Box::new(SomeType { data })` or
`Box::new([0; 4096])` first create a temporary object on the stack before
copying it into the newly allocated space (e.g. [issue #50047]).

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

[`new_with`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.new_with
[`new_zeroed`]: https://docs.rs/boxext/0.1.0/boxext/trait.BoxExt.html#tymethod.new_zeroed
[`calloc`]: http://pubs.opengroup.org/onlinepubs/009695399/functions/calloc.html
[`HeapAlloc(..., HEAP_ZERO_MEMORY, ...)`]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa366597(v=vs.85).aspx#HEAP_ZERO_MEMORY
[`mallocx(..., MALLOCX_ZERO)`]: http://jemalloc.net/jemalloc.3.html#MALLOCX_ZERO

### Features

* `std` (enabled by default): Uses libstd. Can be disabled to allow use
with `no_std` code, in which case `allocator_api` needs to be enabled.

* `allocator_api`: Add similar helpers to the `Box` type from the
`allocator_api` crate.

* `unstable-rust`: Use unstable rust features to more reliably use `calloc`
and co. for `new_zeroed`.

License: Apache-2.0/MIT
