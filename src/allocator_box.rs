// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![cfg_attr(not(feature = "nonnull_cast"), allow(unstable_name_collision))]

use allocator_api::{Alloc, Box, Layout, handle_alloc_error};
#[cfg(not(feature = "nonnull_cast"))]
use allocator_api::NonNullCast;
use core::ptr::{self, NonNull};
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
    ///    fn default() -> Self {
    ///        Foo::new(0, 1)
    ///    }
    /// }
    ///
    /// fn main() {
    ///     // equivalent to `Box::new_in(Foo(1, 2), MyHeap)`
    ///     let buf = Box::new_in_with(|| Foo(1, 2), MyHeap);
    ///     assert_eq!(*buf, Foo(1, 2));
    ///
    ///     // equivalent to `Box::new_in(Foo::new(2, 3), MyHeap)`
    ///     let buf = Box::new_in_with(|| Foo::new(2, 3), MyHeap);
    ///     assert_eq!(*buf, Foo(2, 3));
    ///
    ///     // equivalent to `Box::new_in(Foo::default(), MyHeap)`
    ///     let buf = Box::new_in_with(Foo::default, MyHeap);
    ///     assert_eq!(*buf, Foo::default());
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
    ///     // equivalent to `Box::new_in([0usize; 32], MyHeap)`
    ///     let buf: Box<[usize; 32], _> = Box::new_zeroed_in(MyHeap);
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
    fn new_zeroed_in(a: A) -> Self
    where
        Self: Sized,
        Self::Inner: Zero;

    /// Fallible [`Box::new_in`]
    ///
    /// [`Box::new_in`]: https://docs.rs/allocator_api/*/allocator_api/boxed/struct.Box.html#method.new_in
    ///
    /// This returns `None` if memory couldn't be allocated.
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
    /// fn main() {
    ///     let five = Box::try_new_in(5, MyHeap).unwrap();
    ///     assert_eq!(*five, 5);
    /// }
    /// ```
    fn try_new_in(x: Self::Inner, a: A) -> Option<Self>
    where
        Self: Sized;

    /// Fallible [`Box::new_in_with`]
    ///
    /// [`Box::new_in_with`]: #method.new_in_with
    ///
    /// This returns `None` if memory couldn't be allocated.
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
    ///    fn default() -> Self {
    ///        Foo::new(0, 1)
    ///    }
    /// }
    ///
    /// fn main() {
    ///     // equivalent to `Box::try_new_in(Foo(1, 2), MyHeap)`
    ///     let buf = Box::try_new_in_with(|| Foo(1, 2), MyHeap).unwrap();
    ///     assert_eq!(*buf, Foo(1, 2));
    ///
    ///     // equivalent to `Box::try_new_in(Foo::new(2, 3), MyHeap)`
    ///     let buf = Box::try_new_in_with(|| Foo::new(2, 3), MyHeap).unwrap();
    ///     assert_eq!(*buf, Foo(2, 3));
    ///
    ///     // equivalent to `Box::new_in(Foo::default(), MyHeap)`
    ///     let buf = Box::try_new_in_with(Foo::default, MyHeap).unwrap();
    ///     assert_eq!(*buf, Foo::default());
    /// }
    /// ```
    fn try_new_in_with<F: FnOnce() -> Self::Inner>(f: F, a: A) -> Option<Self>
    where
        Self: Sized;

    /// Fallible [`Box::new_zeroed`]
    ///
    /// [`Box::new_zeroed`]: #method.new_zeroed
    ///
    /// This returns `None` if memory couldn't be allocated.
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
    ///     // equivalent to `Box::try_new_in([0usize; 32], MyHeap)`
    ///     let buf: Box<[usize; 32], _> = Box::try_new_zeroed_in(MyHeap).unwrap();
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
    fn try_new_zeroed_in(a: A) -> Option<Self>
    where
        Self: Sized;
}

// Creates a new box in the given allocator, for the given type.
// If the memory could be allocated, returns Ok(box). Otherwise, returns Err(layout),
// allowing the caller to access the layout that failed allocation.
unsafe fn new_box_in<T, A: Alloc>(mut a: A, zeroed: bool) -> Result<Box<T, A>, Layout> {
    let layout = Layout::new::<T>();
    let raw = if layout.size() == 0 {
        Ok(NonNull::<T>::dangling())
    } else if zeroed {
        a.alloc_zeroed(layout).map(NonNull::cast)
    } else {
        a.alloc(layout).map(NonNull::cast)
    };
    match raw {
        Ok(raw) => Ok(Box::from_raw_in(raw.as_ptr(), a)),
        Err(_) => Err(layout),
    }
}

impl<T, A: Alloc> BoxInExt<A> for Box<T, A> {
    type Inner = T;

    #[inline]
    fn new_in_with<F: FnOnce() -> T>(f: F, a: A) -> Self {
        unsafe {
            let mut b = new_box_in::<T, A>(a, false).unwrap_or_else(|l| handle_alloc_error(l));
            ptr::write(b.as_mut(), f());
            b
        }
    }

    #[inline]
    fn new_zeroed_in(a: A) -> Self
    where
        T: Zero,
    {
        unsafe { new_box_in::<T, A>(a, true).unwrap_or_else(|l| handle_alloc_error(l)) }
    }

    #[inline]
    fn try_new_in(x: T, mut a: A) -> Option<Self> {
        unsafe {
            let raw = a.alloc(Layout::new::<T>()).ok()?.cast().as_ptr();
            ptr::write(raw, x);
            Some(Box::from_raw_in(raw, a))
        }
    }

    #[inline]
    fn try_new_in_with<F: FnOnce() -> Self::Inner>(f: F, mut a: A) -> Option<Self> {
        unsafe {
            let raw = a.alloc(Layout::new::<T>()).ok()?.cast().as_ptr();
            ptr::write(raw, f());
            Some(Box::from_raw_in(raw, a))
        }
    }

    #[inline]
    fn try_new_zeroed_in(mut a: A) -> Option<Self> {
        unsafe {
            let raw = a.alloc_zeroed(Layout::new::<T>()).ok()?.cast();
            Some(Box::from_raw_in(raw.as_ptr(), a))
        }
    }
}

impl<T, A: Alloc + Default> BoxExt for Box<T, A> {
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
    /// #[derive(Debug, PartialEq)]
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
    ///     assert_eq!(*buf, Foo(1, 2));
    ///
    ///     // equivalent to `Box::new_in(Foo::new(2, 3), MyHeap)`
    ///     let buf: Box<_, MyHeap> = Box::new_with(|| Foo::new(2, 3));
    ///     assert_eq!(*buf, Foo(2, 3));
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
    ///     // equivalent to `Box::new_in([0usize; 32], MyHeap)`
    ///     let buf: Box<[usize; 32], MyHeap> = Box::new_zeroed();
    ///     assert_eq!(*buf, [0usize; 32]);
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

    /// Fallible [`Box::new`]
    ///
    /// [`Box::new`]: https://docs.rs/allocator_api/*/allocator_api/boxed/struct.Box.html#method.new
    ///
    /// This returns `None` if memory couldn't be allocated.
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
    /// fn main() {
    ///     // equivalent to `Box::try_new_in(5, MyHeap)`
    ///     let five: Box<_, MyHeap> = Box::try_new(5).unwrap();
    ///     assert_eq!(*five, 5);
    /// }
    /// ```
    ///
    /// This is a convenience wrapper around [`allocator_api::Box::try_new_in`]
    /// when the allocator implements `Default`.
    ///
    /// [`allocator_api::Box::try_new_in`]: trait.BoxInExt.html#tymethod.try_new_in
    #[inline]
    fn try_new(x: T) -> Option<Self> {
        BoxInExt::try_new_in(x, Default::default())
    }

    /// Fallible [`Box::new_with`]
    ///
    /// [`Box::new_with`]: #method.new_with
    ///
    /// This returns `None` if memory couldn't be allocated.
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
    ///     // equivalent to `Box::try_new_in(Foo(1, 2))`
    ///     let buf: Box<_, MyHeap> = Box::try_new_with(|| Foo(1, 2)).unwrap();
    ///     assert_eq!(*buf, Foo(1, 2));
    ///
    ///     // equivalent to `Box::try_new_in(Foo::new(2, 3))`
    ///     let buf: Box<_, MyHeap> = Box::try_new_with(|| Foo::new(2, 3)).unwrap();
    ///     assert_eq!(*buf, Foo(2, 3));
    ///
    ///     // equivalent to `Box::try_new_in(Foo::default())`
    ///     let buf: Box<_, MyHeap> = Box::try_new_with(Foo::default).unwrap();
    ///     assert_eq!(*buf, Foo::default());
    /// }
    /// ```
    ///
    /// This is a convenience wrapper around [`allocator_api::Box::try_new_in_with`]
    /// when the allocator implements `Default`.
    ///
    /// [`allocator_api::Box::try_new_in_with`]: trait.BoxInExt.html#tymethod.try_new_in_with
    #[inline]
    fn try_new_with<F: FnOnce() -> Self::Inner>(f: F) -> Option<Self> {
        BoxInExt::try_new_in_with(f, Default::default())
    }

    /// Fallible [`Box::new_zeroed`]
    ///
    /// [`Box::new_zeroed`]: #method.new_zeroed
    ///
    /// This returns `None` if memory couldn't be allocated.
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
    ///     // equivalent to `Box::try_new([0usize; 32])`
    ///     let buf: Box<[usize; 32], MyHeap> = Box::try_new_zeroed().unwrap();
    ///     assert_eq!(*buf, [0usize; 32]);
    /// }
    /// ```
    ///
    /// This is a convenience wrapper around [`allocator_api::Box::try_new_zeroed_in`]
    /// when the allocator implements `Default`.
    ///
    /// [`allocator_api::Box::try_new_zeroed_in`]: trait.BoxInExt.html#tymethod.try_new_zeroed_in
    ///
    ///
    /// # Safety
    ///
    /// This method is only assumed safe for `Self::Inner` types implementing
    /// the [`Zero`] trait, and not available otherwise. See the definition
    /// of that trait.
    ///
    /// [`Zero`]: trait.Zero.html
    #[inline]
    fn try_new_zeroed() -> Option<Self>
    where
        Self::Inner: Zero,
    {
        BoxInExt::try_new_zeroed_in(Default::default())
    }
}
