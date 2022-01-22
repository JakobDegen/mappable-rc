//! Provides mappable `Rc` and `Arc` implementations.
//!
//! This crate provides two types: [`Marc`] and [`Mrc`], corresponding to `std`'s [`Arc`] and [`Rc`]
//! types. For the most part, these types are near drop in replacements; they also provide shared
//! ownership via reference countings, many of the same methods, and almost all of the same trait
//! impls. The key difference is the existence of the `map` method on both types. For example, you
//! can use [`Mrc::map`] to subslice an `Mrc<[u32]>`:
//!
//! ```rust
//! use mappable_rc::Mrc;
//!
//! let m: Mrc<[u32]> = vec![1, 2, 3, 4].into();
//! assert_eq!(m.as_ref(), &[1, 2, 3, 4]);
//!
//! let m: Mrc<[u32]> = Mrc::map(m, |slice| &slice[1..=2]);
//! assert_eq!(m.as_ref(), &[2, 3]);
//! ```
//!
//! The `map` functions do not require preserving types. For example:
//!
//! ```rust
//! use mappable_rc::Mrc;
//!
//! struct S(u32);
//!
//! let m: Mrc<S> = Mrc::new(S(5));
//! let inner: Mrc<u32> = Mrc::map(m, |s| &s.0);
//!
//! assert_eq!(inner.as_ref(), &5);
//! ```
//!
//! You can use the types provided by this crate even if other code hands you an `Rc` or an `Arc`.
//! See the [`Mrc::from_rc`] and [`Marc::from_arc`] methods, and the corresponding `From` impls.
//!
//! ## Performance
//!
//! The performance characteristics of the types in this crate are very similar to the corresponding
//! `std` types. The data pointer is stored directly in the struct, and so the referenced data is
//! only one indirection away. The `Marc` implementation internally reuses the `Arc` from `std`, and
//! so the atomic operations are expected to be no more or less efficient.
//!
//! A number of the trait implementations in this crate are more efficient than the corresponding
//! `std` implementsions. `Mrc<[T]>: From<Vec<T>>` is implemented like this:
//!
//! ```rust
//! use mappable_rc::Mrc;
//!
//! let v = vec![1; 1000];
//! let m: Mrc<Vec<i32>> = Mrc::new(v);
//! let m: Mrc<[i32]> = Mrc::map(m, |v| &v[..]);
//! ```
//!
//! This means that the data in the `Vec` is never copied and only a small allocation is performed.
//! The same implementation for `Arc<[T]>` will perform a copy of the `Vec`'s data, to ensure that
//! the memory format complies with the more stringent requirements of `Arc`.
//!
//! The main performance downside of these types is that the size of `Mrc` and `Marc` is two
//! `usize`s greater than the size of the corresponding `std` type.
//!
//! ## `#![no_std]`
//!
//! This crate is `#![no_std]` by default, but of course depends on `alloc`. There is a non-default
//! `std` feature that provides implementations of `std::error::Error`, `From<OsString>` and
//! `From<PathBuf>`. Activating this feature introduces an `std` dependency.
//!
//! This crate has no other dependencies.

#![no_std]

use core::ptr::NonNull;
use core::{any::Any, ops::Deref};

use alloc::rc::Rc;
use alloc::sync::Arc;

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod std_impls;

pub struct Marc<T: ?Sized + 'static> {
    // SAFETY:
    //  - This is well aligned and points to a valid `T`
    //  - This is valid for at least as long as `alloc`
    data: NonNull<T>,
    alloc: Arc<dyn Any + Send>,
}

// SAFETY: A `Marc<T>` only gives shared access to a `T`. This impl does not have the `Send` bound
// that the std impl has; that's because we never hand out a `&mut T` (doing so would be UB anyway).
// The equivalent of the `Send` bound, is the `Send` requirement for the `alloc`.
unsafe impl<T: Sync> Send for Marc<T> {}

// SAFETY: A `Marc<T>` being `Sync` is basically equivalent to it being `Send`, so we require the
// same bounds.
unsafe impl<T: Sync> Sync for Marc<T> {}

pub struct Mrc<T: ?Sized + 'static> {
    // SAFETY:
    //  - This is well aligned and points to a valid `T`
    //  - This is valid for at least as long as `alloc`
    data: NonNull<T>,
    // Guarantees that we're non-`Send` and non-`Sync`
    alloc: Rc<dyn Any>,
}

macro_rules! impls {
    ($name:ident, $l:literal) => {
        impl<T: ?Sized> Deref for $name<T> {
            type Target = T;

            fn deref(&self) -> &T {
                // SAFETY: See safety comment on the field
                unsafe { self.data.as_ref() }
            }
        }

        impl<T: ?Sized> $name<T> {
            /// Returns a read-only pointer to the referred to data.
            ///
            /// The pointer is valid for as long as this value is alive.
            pub fn as_ptr(&self) -> *const T {
                self.data.as_ptr() as *const _
            }

            /// Maps the value to a new
            #[doc = concat!("`", $l, "`")]
            /// that refers to the data returned by the closure.
            ///
            /// This only changes what data *this particular*
            #[doc = concat!("`", $l, "`")]
            /// refers to. It does not introduce mutability - any
            #[doc = concat!("`", $l, "<T>`s")]
            /// you've cloned from this one in the past still point to the same thing. Of course, if
            /// you clone the value returned by this function, then the resulting
            #[doc = concat!("`", $l, "<U>`s")]
            /// will also point to the mapped value.
            ///
            /// This does not cause the `T` to be dropped early. Even if the `&U` refers to only a
            /// part of the `&T`, no part of the `T` is dropped until all references to or into the
            /// `T` are gone, at which point the entire `T` is dropped at once.
            pub fn map<U: ?Sized + 'static, F: FnOnce(&T) -> &U>(self_: Self, f: F) -> $name<U> {
                let r = self_.deref();
                // Panic safety: Panicking here only causes `orig` to be dropped
                let out = f(r) as *const _;
                // SAFETY: Pointer is the result of a reference, so not null.
                let data = unsafe { NonNull::new_unchecked(out as *mut _) };
                // SAFETY: The "actual" lifetime being passed to `f` should be understood to be the lifetime
                // of `self.alloc`. In other words the reference passed into `f` is valid as long as
                // `alloc` is. Hence it satisfies the safety requirements for `data`. Using a fake lifetime
                // here is ok because lifetime specilization is not possible.
                $name {
                    data,
                    alloc: self_.alloc,
                }
            }

            /// Attempts to map the
            #[doc = concat!("`", $l, "<T>`")]
            /// , returning the new value on success and the old value otherwise.
            ///
            /// This is simply a fallible version of
            #[doc = concat!("[`", $l, "::map`]")]
            /// , and generally has all the same properties.
            pub fn try_map<U: ?Sized + 'static, F: FnOnce(&T) -> Option<&U>>(
                self_: Self,
                f: F,
            ) -> Result<$name<U>, $name<T>> {
                let r = self_.deref();
                match f(r) {
                    Some(p) => {
                        // SAFETY: For all safety concerns, see `map`
                        let data = unsafe { NonNull::new_unchecked(p as *const _ as *mut _) };
                        Ok($name {
                            data,
                            alloc: self_.alloc,
                        })
                    }
                    None => Err(self_),
                }
            }

            /// Maps the value that the
            #[doc = concat!("`", $l, "`")]
            /// refers to, without taking ownership.
            ///
            /// This is equivalent to cloning, mapping, and then writing to `self`, except that it
            /// is slightly more efficient because it avoids the clone.
            ///
            /// `self` is left unchanged if `f` panics.
            pub fn map_in_place<F: FnOnce(&T) -> &T>(self_: &mut Self, f: F) {
                let r = self_.deref();
                // Panic safety: `self` is unmodified and the data pointer continues to be valid as
                // we only hand out immutable references.
                let out = f(r);
                // SAFETY: This is effectively the same operation as in `map`.
                self_.data = unsafe { NonNull::new_unchecked(out as *const _ as *mut _) };
            }
        }
    };
}

impls!(Marc, "Marc");
impls!(Mrc, "Mrc");

impl<T: Send + 'static> Marc<T> {
    /// Creates a new `Marc` from an [`Arc`] that shares ownership of the `Arc`'s data.
    ///
    /// Like [`Marc::new`], this method requires `T: Send + Sized + 'static`. If you have an
    /// `Arc<T>` where `T: ?Sized`, then you can create an `Marc<T>` via [`Marc::from_borrow`].
    ///
    /// As long as the returned `Marc` is alive, the strong count of the `Arc` will be at least one.
    /// This is also the case if any `Marc`'s derived from the return value via [`Clone`] and
    /// [`Marc::map`] are alive. The strong count of the input `Arc` could be observed by another
    /// `Arc` also sharing ownership of the data. It is not specified whether clones of the return
    /// value will be reflected in that strong count.
    ///
    /// This function is essentially free to call. After inlining, it will consist of one to two
    /// pointer copies.
    pub fn from_arc(arc: Arc<T>) -> Self {
        let p = Arc::as_ptr(&arc) as *mut T;
        // SAFETY: The pointer was returned by `Arc::as_ptr` and so is not null
        unsafe {
            Self {
                data: NonNull::new_unchecked(p),
                alloc: arc,
            }
        }
    }

    /// Creates a new `Marc` that provides shared ownership of the `T`.
    ///
    /// This method, like all ways of creating an `Marc`, has a `Send + 'static` bound that is not
    /// found on the corresponding `Arc` method. You can avoid the `Send` requirement by using
    /// [`Mrc::from_borrow`] to create an [`Mrc`] instead. The `'static` requirement is
    /// fundamentally necessary for the soundness of this type and cannot be circumvented.
    pub fn new(t: T) -> Self {
        Marc::from_arc(Arc::new(t))
    }
}

/// Creates a new `Marc<T>` sharing ownership of the same data.
impl<T: ?Sized> Clone for Marc<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data,
            alloc: Arc::clone(&self.alloc),
        }
    }
}

impl<T: Send + 'static> From<Arc<T>> for Marc<T> {
    fn from(a: Arc<T>) -> Self {
        Marc::from_arc(a)
    }
}

impl<T: 'static> Mrc<T> {
    /// Creates a new `Mrc` from an [`Rc`] that shares ownership of the `Rc`'s data.
    ///
    /// Like [`Mrc::new`], this method requires `T: Sized + 'static`. If you have an
    /// `Rc<T>` where `T: ?Sized`, then you can create an `Mrc<T>` via [`Mrc::from_borrow`].
    ///
    /// As long as the returned `Mrc` is alive, the strong count of the `Rc` will be at least one.
    /// This is also the case if any `Mrc`'s derived from the return value via [`Clone`] and
    /// [`Mrc::map`] are alive. The strong count of the input `Rc` could be observed by another `Rc`
    /// also sharing ownership of the data. It is not specified whether clones of the return value
    /// will be reflected in that strong count.
    ///
    /// This function is essentially free to call. After inlining, it will consist of one to two
    /// pointer copies.
    pub fn from_rc(rc: Rc<T>) -> Self {
        let p = Rc::as_ptr(&rc) as *mut T;
        // SAFETY: The pointer was returned by `Rc::as_ptr` and so is not null
        unsafe {
            Self {
                data: NonNull::new_unchecked(p),
                alloc: rc,
            }
        }
    }

    /// Creates a new `Mrc` that provides shared ownership of the `T`.
    ///
    /// This method, like all ways of creating an `Mrc`, has a `'static` bound that is not found on
    /// the corresponding `Rc` method. That requirement is fundamentally necessary for the soundness
    /// of this type and cannot be circumvented.
    pub fn new(t: T) -> Self {
        Mrc::from_rc(Rc::new(t))
    }
}

/// Creates a new `Mrc<T>` sharing ownership of the same data.
impl<T: ?Sized> Clone for Mrc<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data,
            alloc: Rc::clone(&self.alloc),
        }
    }
}

impl<T: 'static> From<Rc<T>> for Mrc<T> {
    fn from(a: Rc<T>) -> Self {
        Mrc::from_rc(a)
    }
}

#[cfg(test)]
mod tests {
    use core::{cell::RefCell, marker::PhantomData, ops::DerefMut, panic::AssertUnwindSafe};

    extern crate std;

    use std::panic::catch_unwind;

    use alloc::vec;

    use crate::*;

    fn is_send<T: Send>(_: &T) {}
    fn is_sync<T: Sync>(_: &T) {}

    #[test]
    fn clone_validity() {
        let v = Mrc::new(vec![1, 2, 3]);
        let c = v.clone();
        let c = Mrc::map(c, |c| &c[1..]);

        let v = v;
        let c = c;

        assert_eq!(&v[..], &[1, 2, 3]);
        assert_eq!(&c[..], &[2, 3]);
    }

    #[test]
    fn rc_validity() {
        let a = Rc::new(vec![1, 2, 3]);
        let m = Mrc::from_rc(Rc::clone(&a));
        let m = Mrc::map(m, |m| &m[1..]);

        let a = a;
        let m = m;

        assert_eq!(&a[..], &[1, 2, 3]);
        assert_eq!(&m[..], &[2, 3]);
    }

    #[test]
    fn init_correctness() {
        let a = Rc::new(5);
        assert_eq!(a.as_ref(), &5);

        let b: Mrc<[i32]> = Mrc::from_borrow(vec![1, 2, 3, 4]);
        assert_eq!(b.as_ref(), &[1, 2, 3, 4]);

        let c: Mrc<i32> = Mrc::from_rc(Rc::new(5));
        assert_eq!(c.as_ref(), &5);
    }

    // Ensures we get a compile error if we break this
    #[test]
    fn minimum_impls() {
        let a = Marc::new(5);
        is_send(&a);
        is_sync(&a);
    }

    #[test]
    fn mapped_sync() {
        // Send, not Sync
        struct S(i32, PhantomData<RefCell<i32>>);

        let m = Marc::new(S(10, PhantomData));
        let m = Marc::map(m, |s| &s.0);
        is_send(&m);
    }

    #[test]
    fn in_place_panic() {
        let mut m = Mrc::new(5);
        let mut r = AssertUnwindSafe(&mut m);
        catch_unwind(move || Mrc::map_in_place(r.deref_mut(), |_| panic!())).unwrap_err();
        assert_eq!(m.as_ref(), &5);
    }
}
