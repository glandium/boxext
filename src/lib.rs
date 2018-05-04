// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(missing_docs)]

//! # Extensions to the `Box` type
//!
//! This crate provides extra initializer methods for `Box`, working around the
//! current (as of writing) shortcomings from `Box::new`:
//!
//! * Since Rust 1.12, constructs such as `Box::new([0; 4096])` first create a
//! temporary object on the stack before copying it into the newly allocated
//! space (e.g. [issue #50047]).
//!
//! * Constructs such as `Box::new(some_function_call())` first get the result
//! from the function call on the stack before copying it into the newly
//! allocated space.
//!
//! [issue #50047]: https://github.com/rust-lang/rust/issues/50047
//!
//! Both can be worked around with some contortion but with caveats. This crate
//! provides helpers doing those contortions for you, but can't deal with the
//! caveats. Those caveats are essentially the same as why the unstable
//! placement features were removed in nightly 1.27, namely that there are no
//! guarantees that things will actually happen in place (and they don't in
//! debug builds).
//!
//! The crates adds the following helper methods to the `Box` type:
//!
//! * [`new_with`], which takes a function or closure returning the object that
//! will be placed in the Box.
//!
//! * [`new_zeroed`], which creates an object filled with zeroes, possibly
//! using [`calloc`]/[`HeapAlloc(..., HEAP_ZERO_MEMORY, ...)`]/
//! [`mallocx(..., MALLOCX_ZERO)`] under the hood.
//!
//! [`new_with`]: trait.BoxExt.html#tymethod.new_with
//! [`new_zeroed`]: trait.BoxExt.html#tymethod.new_zeroed
//! [`calloc`]: http://pubs.opengroup.org/onlinepubs/009695399/functions/calloc.html
//! [`HeapAlloc(..., HEAP_ZERO_MEMORY, ...)`]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa366597(v=vs.85).aspx#HEAP_ZERO_MEMORY
//! [`mallocx(..., MALLOCX_ZERO)`]: http://jemalloc.net/jemalloc.3.html#MALLOCX_ZERO
//!
//! ## Features
//!
//! * `std` (enabled by default): Uses libstd. Can be disabled to allow use
//! with `no_std` code, in which case `allocator_api` needs to be enabled.
//!
//! * `allocator_api`: Add similar helpers to the `Box` type from the
//! `allocator_api` crate.
//!
//! * `unstable-rust`: Use unstable rust features to more reliably use `calloc`
//! and co. for `new_zeroed`.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "unstable-rust", feature(alloc, allocator_api))]

#[cfg(all(feature = "std", feature = "unstable-rust"))]
extern crate alloc;
#[cfg(all(feature = "std", feature = "unstable-rust"))]
use alloc::alloc::{oom, Global, GlobalAlloc, Layout};

#[cfg(all(feature = "std", not(feature = "unstable-rust")))]
#[macro_use]
extern crate static_assertions;

#[cfg(feature = "allocator_api")]
extern crate allocator_api;

#[cfg(feature = "std")]
extern crate core;

#[cfg(feature = "std")]
use core::ptr;

#[cfg(all(feature = "std", not(feature = "unstable-rust")))]
use core::mem;

#[cfg(feature = "allocator_api")]
mod allocator_box;
#[cfg(feature = "allocator_api")]
pub use allocator_box::*;

/// Extensions to the `Box` type
pub trait BoxExt {
    /// Type contained inside the `Box`.
    type Inner;

    /// Allocates memory on the heap and then places the result of `f` into it.
    ///
    /// This doesn't actually allocate if `Self::Inner` is zero-sized.
    ///
    /// When building with optimization enabled, this is expected to avoid
    /// copies, contrary to `Box::new`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate boxext;
    /// use boxext::BoxExt;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Foo(usize, usize);
    ///
    /// impl Foo {
    ///     fn new(a: usize, b: usize) -> Self {
    ///         Foo(a, b)
    ///    }
    /// }
    ///
    /// impl Default for Foo {
    ///     fn default() -> Self {
    ///         Foo::new(0, 1)
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // equivalent to `Box::new(Foo(1, 2))`
    /// #   #[cfg(feature = "std")]
    ///     let buf = Box::new_with(|| Foo(1, 2));
    /// #   #[cfg(feature = "std")]
    ///     assert_eq!(*buf, Foo(1, 2));
    ///
    ///     // equivalent to `Box::new(Foo::new(2, 3))`
    /// #   #[cfg(feature = "std")]
    ///     let buf = Box::new_with(|| Foo::new(2, 3));
    /// #   #[cfg(feature = "std")]
    ///     assert_eq!(*buf, Foo(2, 3));
    ///
    ///     // equivalent to `Box::new(Foo::default())`
    /// #   #[cfg(feature = "std")]
    ///     let buf = Box::new_with(Foo::default);
    /// #   #[cfg(feature = "std")]
    ///     assert_eq!(*buf, Foo::default());
    /// }
    /// ```
    fn new_with<F: FnOnce() -> Self::Inner>(f: F) -> Self;

    /// Allocates zeroed memory on the heap.
    ///
    /// This doesn't actually allocate if `Self::Inner` is zero-sized.
    ///
    /// When possible, this will get zeroed memory directly from the
    /// allocator, through the use of [`calloc`], [`HeapAlloc(...,
    /// HEAP_ZERO_MEMORY, ...)`] or [`mallocx(..., MALLOCX_ZERO)`].
    ///
    /// [`calloc`]: http://pubs.opengroup.org/onlinepubs/009695399/functions/calloc.html
    /// [`HeapAlloc(..., HEAP_ZERO_MEMORY, ...)`]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa366597(v=vs.85).aspx#HEAP_ZERO_MEMORY
    /// [`mallocx(..., MALLOCX_ZERO)`]: http://jemalloc.net/jemalloc.3.html#MALLOCX_ZERO
    ///
    /// Practically speaking, it will use those when the alignment for
    /// `Self::Inner` is less the pointer size. Otherwise, this is
    /// equivalent to `Box::new_with(|| std::mem::zeroed())`.
    ///
    /// When the `unstable-rust` feature is enabled, zeroed memory is
    /// unconditionally obtained from the allocator.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate boxext;
    /// use boxext::BoxExt;
    ///
    /// fn main() {
    ///     // equivalent to `Box::new([0usize; 32])`
    /// #   #[cfg(feature = "std")]
    ///     let buf: Box<[usize; 32]> = Box::new_zeroed();
    /// #   #[cfg(feature = "std")]
    ///     assert_eq!(*buf, [0usize; 32]);
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// This method is only assumed safe for `Self::Inner` types implementing
    /// the [`Zero`] trait, and not available otherwise. See the definition
    /// of that trait.
    ///
    /// [`Zero`]: trait.Zero.html
    fn new_zeroed() -> Self
    where
        Self: Sized,
        Self::Inner: Zero;
}

#[cfg(all(feature = "std", feature = "unstable-rust"))]
unsafe fn new_box<T>(zeroed: bool) -> Box<T> {
    let layout = Layout::new::<T>();
    let raw = if layout.size() == 0 {
        ptr::NonNull::<T>::dangling().as_ptr()
    } else if zeroed {
        Global.alloc_zeroed(layout) as *mut T
    } else {
        Global.alloc(layout) as *mut T
    };
    if raw.is_null() {
        oom()
    }
    Box::from_raw(raw)
}

#[cfg(feature = "std")]
impl<T> BoxExt for Box<T> {
    type Inner = T;

    #[cfg(feature = "unstable-rust")]
    #[inline]
    fn new_with<F: FnOnce() -> T>(f: F) -> Box<T> {
        unsafe {
            let mut b = new_box::<T>(false);
            ptr::write(b.as_mut(), f());
            b
        }
    }

    #[cfg(not(feature = "unstable-rust"))]
    #[inline]
    fn new_with<F: FnOnce() -> T>(f: F) -> Box<T> {
        unsafe {
            let mut v = Vec::<T>::with_capacity(1);
            let raw: *mut T = v.as_mut_ptr();
            mem::forget(v);
            ptr::write(raw, f());
            Box::from_raw(raw)
        }
    }

    #[cfg(feature = "unstable-rust")]
    #[inline]
    fn new_zeroed() -> Box<T>
    where
        T: Zero,
    {
        unsafe { new_box(true) }
    }

    #[cfg(not(feature = "unstable-rust"))]
    #[inline]
    fn new_zeroed() -> Box<T>
    where
        T: Zero,
    {
        macro_rules! new_zeroed {
            ($t:ty, $align:expr, $size:expr) => {{
                const_assert_eq!(mem::align_of::<$t>(), $align);
                let mut v = vec![0 as $t; $size];
                let raw: *mut $t = v.as_mut_ptr();
                mem::forget(v);
                Box::from_raw(raw as *mut T)
            }};
        }

        unsafe {
            let size = mem::size_of::<T>();
            match mem::align_of::<T>() {
                // vec! has an optimization that uses calloc when using
                // vec![0; n], so use that when we can.
                1 => new_zeroed!(u8, 1, size),
                2 => new_zeroed!(u16, 2, (size + 1) / 2),
                #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
                4 => new_zeroed!(u32, 4, (size + 3) / 4),
                #[cfg(target_pointer_width = "64")]
                8 => new_zeroed!(u64, 8, (size + 7) / 8),
                _ => Box::new_with(|| mem::zeroed()),
            }
        }
    }
}

/// Trait indicating whether a value full of zeroes is valid.
///
/// This trait is used to enable the [`Box::new_zeroed`] method for types where
/// it's safe to use.
///
/// [`Box::new_zeroed`]: trait.BoxExt.html#tymethod::new_zeroed
///
/// # Safety
///
/// Do **not** implement this trait for types where a raw byte array of 0
/// doesn't represent a valid value for the type. Please double check it is
/// valid and corresponds to what you want.
///
/// # Examples
///
/// ```
/// extern crate boxext;
/// use boxext::{BoxExt, Zero};
///
/// #[derive(Debug, PartialEq)]
/// struct Foo(usize);
///
/// unsafe impl Zero for Foo {}
///
/// fn main() {
///     // equivalent to `Box::new(Foo(0))`
/// #   #[cfg(feature = "std")]
///     let buf: Box<Foo> = Box::new_zeroed();
/// #   #[cfg(feature = "std")]
///     assert_eq!(*buf, Foo(0));
/// }
/// ```
///
/// For convenience, a `boxext_derive` crate is provided that provides a
/// custom derive for `Zero`.
///
/// ```
/// extern crate boxext;
/// #[macro_use]
/// extern crate boxext_derive;
/// use boxext::BoxExt;
///
/// #[derive(Zero, Debug, PartialEq)]
/// struct Foo(usize);
///
/// fn main() {
///     // equivalent to `Box::new(Foo(0))`
/// #   #[cfg(feature = "std")]
///     let buf: Box<Foo> = Box::new_zeroed();
/// #   #[cfg(feature = "std")]
///     assert_eq!(*buf, Foo(0));
/// }
/// ```
///
/// ```compile_fail
/// extern crate boxext;
/// #[macro_use]
/// extern crate boxext_derive;
/// use boxext::BoxExt;
///
/// #[derive(Zero)]
/// //          ^ the trait `boxext::Zero` is not implemented for `Bar`
/// struct Foo(Bar);
///
/// struct Bar;
///
/// fn main() {
///     // equivalent to `Box::new(Foo(0))`
///     let buf: Box<Foo> = Box::new_zeroed();
/// }
/// ```
///
pub unsafe trait Zero: Sized {}

macro_rules! zero_num_impl {
    ($($t:ty)+) => { $(unsafe impl Zero for $t {})+ }
}

zero_num_impl! {
    u8 u16 u32 u64 usize
    i8 i16 i32 i64 isize
    f32 f64
}

unsafe impl<T> Zero for *mut T {}

unsafe impl<T> Zero for *const T {}

macro_rules! zero_array_impl {
    ($($n:expr)+) => {$(
        unsafe impl<T: Zero> Zero for [T; $n] {}
    )+};
}

zero_array_impl! {
    1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
    17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
    33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48
    49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64
    65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80
    81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96
    97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112
    113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128
    160 192 200 224 256 384 512 768 1024 2048 4096 8192 16384 32768
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
zero_array_impl! {
    65536 131072 262144 524288 1048576 2097152 4194304 8388608
    16777216 33554432 67108864 134217728 268435456 536870912
    1073741824 2147483648
}

#[cfg(target_pointer_width = "64")]
zero_array_impl! {
    4294967296
}

macro_rules! zero_tuple_impl {
    ($t:ident $($u:ident)+) => {
        zero_tuple_impl!(($t) $($u)+);
    };
    (($($t:ident)+) $u:ident $($v:ident)*) => {
        zero_tuple_impl!(($($t)+));
        zero_tuple_impl!(($($t)+ $u) $($v)*);
    };
    (($($t:ident)+)) => {
        unsafe impl<$($t: Zero),+> Zero for ($($t,)+) {}
    };
}

zero_tuple_impl! {
    A B C D E F G H I J K L
}
