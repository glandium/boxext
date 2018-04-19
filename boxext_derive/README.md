## Custom Derive for the `boxext::Zero` trait

Add `#[derive(Zero)]` on your types to automatically derive the `boxext::Zero` trait.
Only structs aggregating types implementing the `boxext::Zero` trait are valid to use this with.

### Example

```rust
extern crate boxext;
#[macro_use]
extern crate boxext_derive;
use boxext::BoxExt;

#[derive(Zero)]
struct Foo {
    a: usize,
    b: f64,
    c: [usize; 4],
}

// #[derive(Zero)]
//             ^ the trait `boxext::Zero` is not implemented for `std::boxed::Box<Foo>`
// struct Bar {
//    a: usize,
//    b: Box<Foo>,
// }

fn main() {
    // equivalent to Box::new(Foo { a: 0, b: 0.0, c: [0; 4] })
    let buf: Box<Foo> = Box::new_zeroed();
}
```
