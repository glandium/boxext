// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::ptr;
use allocator_api::{Alloc, Box, RawVec};
use {BoxExt, Zero};

/// Extensions to the `allocator_api::Box` type
pub trait BoxInExt<A: Alloc> {
    /// Type contained inside the `Box`.
    type Inner;

    /// Allocates memory in the given allocator and then places the result of
    /// `f` into it.
    ///
    /// This doesn't actually allocate if `Self::Inner` is zero-sized.
    ///
    /// When building with optimization enabled, this is expected to avoid
    /// copies, contrary to `Box::new_in`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate allocator_api;
    /// extern crate boxext;
    /// use allocator_api::Box;
    /// use boxext::BoxInExt;
    /// # include!("dummy.rs");
    ///
    /// struct Foo(usize, usize);
    ///
    /// impl Foo {
    ///     fn new(a: usize, b: usize) -> Self {
    ///         Foo(a, b)
    ///    }
    /// }
    ///
    /// impl Default for Foo {
    ///    fn default() -> Self {
    ///        Foo::new(0, 1)
    ///    }
    /// }
    ///
    /// fn main() {
    ///     // equivalent to `Box::new_in(Foo(1, 2), MyHeap)`
    ///     let buf = Box::new_in_with(|| Foo(1, 2), MyHeap);
    ///
    ///     // equivalent to `Box::new_in(Foo::new(2, 3), MyHeap)`
    ///     let buf = Box::new_in_with(|| Foo::new(2, 3), MyHeap);
    ///
    ///     // equivalent to `Box::<Foo>::new(Default::default())`
    ///     let buf = Box::<Foo, _>::new_in_with(Default::default, MyHeap);
    /// }
    /// ```
    fn new_in_with<F: FnOnce() -> Self::Inner>(f: F, a: A) -> Self;

    /// Allocates zeroed memory in the given allocator.
    ///
    /// This doesn't actually allocate if `Self::Inner` is zero-sized.
    ///
    /// This will get zeroed memory directly from the allocator.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate allocator_api;
    /// extern crate boxext;
    /// use allocator_api::Box;
    /// use boxext::BoxInExt;
    /// # include!("dummy.rs");
    ///
    /// fn main() {
    ///     // equivalent to `Box::new_in([0usize; 64], MyHeap)`
    ///     let buf: Box<[usize; 64], _> = Box::new_zeroed_in(MyHeap);
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
    fn new_zeroed_in(a: A) -> Self
    where
        Self: Sized,
        Self::Inner: Zero;
}

impl<T, A: Alloc + Clone> BoxInExt<A> for Box<T, A> {
    type Inner = T;

    #[inline]
    fn new_in_with<F: FnOnce() -> Self::Inner>(f: F, a: A) -> Self {
        unsafe {
            let v = RawVec::<T, A>::with_capacity_in(1, a.clone());
            let raw = Box::into_raw(v.into_box()) as *mut T;
            ptr::write(raw, f());
            Box::from_raw_in(raw, a)
        }
    }

    #[inline]
    fn new_zeroed_in(a: A) -> Self
    where
        T: Zero,
    {
        unsafe {
            let v = RawVec::<T, A>::with_capacity_zeroed_in(1, a.clone());
            let raw = Box::into_raw(v.into_box());
            Box::from_raw_in(raw as *mut T, a)
        }
    }
}

impl<T, A: Alloc + Clone + Default> BoxExt for Box<T, A> {
    type Inner = <Self as BoxInExt<A>>::Inner;

    /// Allocates memory in the given allocator and then places the result of
    /// `f` into it.
    ///
    /// This doesn't actually allocate if `Self::Inner` is zero-sized.
    ///
    /// When building with optimization enabled, this is expected to avoid
    /// copies, contrary to `allocator_api::Box::new_in`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate allocator_api;
    /// extern crate boxext;
    /// use allocator_api::Box;
    /// use boxext::BoxExt;
    /// # include!("dummy.rs");
    ///
    /// struct Foo(usize, usize);
    ///
    /// impl Foo {
    ///     fn new(a: usize, b: usize) -> Self {
    ///         Foo(a, b)
    ///    }
    /// }
    ///
    /// fn main() {
    ///     // equivalent to `Box::new_in(Foo(1, 2), MyHeap)`
    ///     let buf: Box<_, MyHeap> = Box::new_with(|| Foo(1, 2));
    ///
    ///     // equivalent to `Box::new_in(Foo::new(2, 3), MyHeap)`
    ///     let buf: Box<_, MyHeap> = Box::new_with(|| Foo::new(2, 3));
    /// }
    /// ```
    ///
    /// This is a convenience wrapper around [`allocator_api::Box::new_in_with`]
    /// when the allocator implements `Default`.
    ///
    /// [`allocator_api::Box::new_in_with`]: trait.BoxInExt.html#tymethod.new_in_with
    #[inline]
    fn new_with<F: FnOnce() -> Self::Inner>(f: F) -> Self {
        BoxInExt::new_in_with(f, Default::default())
    }

    /// Allocates zeroed memory in the given allocator.
    ///
    /// This doesn't actually allocate if `Self::Inner` is zero-sized.
    ///
    /// This will get zeroed memory directly from it.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate allocator_api;
    /// extern crate boxext;
    /// use allocator_api::Box;
    /// use boxext::BoxExt;
    /// # include!("dummy.rs");
    ///
    /// fn main() {
    ///     // equivalent to `Box::new_in([0usize; 64], MyHeap)`
    ///     let buf: Box<[usize; 64], MyHeap> = Box::new_zeroed();
    /// }
    /// ```
    ///
    /// This is a convenience wrapper around [`allocator_api::Box::new_zeroed_in`]
    /// when the allocator implements `Default`.
    ///
    /// [`allocator_api::Box::new_zeroed_in`]: trait.BoxInExt.html#tymethod.new_zeroed_in
    ///
    /// # Safety
    ///
    /// This method is only assumed safe for `Self::Inner` types implementing
    /// the [`Zero`] trait, and not available otherwise. See the definition
    /// of that trait.
    ///
    /// [`Zero`]: trait.Zero.html
    #[inline]
    fn new_zeroed() -> Self
    where
        T: Zero,
    {
        BoxInExt::new_zeroed_in(Default::default())
    }
}
