// This module contains lots of trait and function implementations for `Marc` and `Mrc` that are
// found in the corresponding `std` type. These implementions exclusively make use of other `pub`
// methods on the types, and all do not use `unsafe`. As such, if the types in general are sound,
// these impls are too.

#![forbid(unsafe_code)]

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter, Pointer};
use core::hash::{Hash, Hasher};
use core::ops::Deref;

use alloc::borrow::{Cow, ToOwned};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

use crate::Marc;
use crate::Mrc;

#[cfg(feature = "std")]
use std::{error::Error, ffi::OsStr, ffi::OsString, path::Path, path::PathBuf};

macro_rules! impls {
    ($name:ident, $l:literal, $($send:tt)*) => {
        impl<T: ?Sized> $name<T> {
            pub fn ptr_eq(this: &Self, other: &Self) -> bool {
                core::ptr::eq(this.as_ptr(), other.as_ptr())
            }

            /// Creates a
            #[doc = concat!("`", $l, "<T>`")]
            ///  from a value that borrows `T`.
            ///
            /// This is just implemented as
            #[doc = concat!("`", $l, "::map(", $l, "::new(c), |c| c.borrow())`.")]
            pub fn from_borrow<C>(c: C) -> Self
            where
                C: $($send)* Borrow<T> + 'static,
            {
                $name::map($name::new(c), |c| c.borrow())
            }
        }

        impl<T: ?Sized> AsRef<T> for $name<T> {
            fn as_ref(&self) -> &T {
                self.deref()
            }
        }

        impl<T: ?Sized> Borrow<T> for $name<T> {
            fn borrow(&self) -> &T {
                self.deref()
            }
        }

        impl<T: ?Sized + Debug> Debug for $name<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                self.deref().fmt(f)
            }
        }

        impl<T: $($send)* Default + 'static> Default for $name<T> {
            fn default() -> Self {
                $name::new(Default::default())
            }
        }

        impl<T: ?Sized + Display> Display for $name<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                self.deref().fmt(f)
            }
        }

        impl<T: ?Sized + Eq> Eq for $name<T> {}

        #[cfg(feature = "std")]
        impl<T: ?Sized + Error> Error for $name<T> {
            fn source(&self) -> Option<&(dyn Error + 'static)> {
                self.deref().source()
            }
        }

        impl<T: $($send)* Clone + 'static> From<&'_ [T]> for $name<[T]> {
            fn from(r: &[T]) -> Self {
                $name::from_borrow(r.to_vec())
            }
        }

        impl<T: $($send)* ?Sized + 'static> From<Box<T>> for $name<T> {
            fn from(b: Box<T>) -> $name<T> {
                $name::from_borrow(b)
            }
        }

        impl<'a, B> From<Cow<'a, B>> for $name<B>
        where
            B: ?Sized + ToOwned,
            &'a B: Into<$name<B>>,
            <B as ToOwned>::Owned: Into<$name<B>>,
        {
            fn from(b: Cow<'a, B>) -> $name<B> {
                match b {
                    Cow::Owned(b) => b.into(),
                    Cow::Borrowed(b) => b.into(),
                }
            }
        }

        #[cfg(feature = "std")]
        impl From<OsString> for $name<OsStr> {
            fn from(s: OsString) -> $name<OsStr> {
                $name::from_borrow(s)
            }
        }

        #[cfg(feature = "std")]
        impl From<PathBuf> for $name<Path> {
            fn from(p: PathBuf) -> $name<Path> {
                $name::from_borrow(p)
            }
        }

        impl From<String> for $name<str> {
            fn from(s: String) -> $name<str> {
                $name::from_borrow(s)
            }
        }

        impl<T: $($send)* 'static> From<T> for $name<T> {
            fn from(t: T) -> $name<T> {
                $name::new(t)
            }
        }

        impl<T: $($send)* 'static> From<Vec<T>> for $name<[T]> {
            fn from(v: Vec<T>) -> $name<[T]> {
                $name::from_borrow(v)
            }
        }

        impl<T: $($send)* 'static> FromIterator<T> for $name<[T]> {
            fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> $name<[T]> {
                iter.into_iter().collect::<Vec<T>>().into()
            }
        }

        impl<T: ?Sized + Hash> Hash for $name<T> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.deref().hash(state)
            }
        }

        impl<T: ?Sized + Ord> Ord for $name<T> {
            fn cmp(&self, other: &Self) -> Ordering {
                self.deref().cmp(other.deref())
            }
        }

        impl<T: ?Sized + PartialEq<T>> PartialEq<$name<T>> for $name<T> {
            fn eq(&self, other: &Self) -> bool {
                self.deref().eq(other.deref())
            }
        }

        impl<T: ?Sized + PartialOrd<T>> PartialOrd<$name<T>> for $name<T> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.deref().partial_cmp(other.deref())
            }
        }

        impl<T: ?Sized> Pointer for $name<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
                let t = self.deref();
                <&T as Pointer>::fmt(&t, f)
            }
        }

        impl<T, const N: usize> TryFrom<$name<[T]>> for $name<[T; N]> {
            type Error = $name<[T]>;

            fn try_from(s: $name<[T]>) -> Result<$name<[T; N]>, $name<[T]>> {
                $name::try_map(s, |s| s.try_into().ok())
            }
        }
    };
}

impls!(Marc, "Marc", Send+);

impls!(Mrc, "Mrc",);
