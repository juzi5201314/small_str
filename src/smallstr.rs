#![allow(unused_imports)]

#[doc(hidden)]
extern crate alloc;

use alloc::borrow::Cow;
use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::str;
use alloc::str::from_boxed_utf8_unchecked;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(all(feature = "unstable", not(feature = "std")))]
use core::error::Error;
use core::fmt;
use core::fmt::Write;
use core::ops::{self, Add, AddAssign};
use core::str::{FromStr, Utf8Error};
use core::{hash, slice};
#[cfg(feature = "std")]
use std::error::Error;

use smallvec::SmallVec;

pub use smallvec::CollectionAllocErr;

/// like `format!`
/// 
/// ```
/// use small_str::{format_smallstr, SmallString};
/// # extern crate alloc;
/// # use alloc::string::String;
/// 
/// let foo = "foo";
/// let bar = String::from("bar");
/// 
/// assert_eq!(format_smallstr!("{}{}", foo, bar), SmallString::from("foobar"));
/// ```
#[macro_export]
macro_rules! format_smallstr {
    ($($tt:tt)*) => {{
        use ::core::fmt::Write;
        let mut s = $crate::SmallStr::new();
        s.write_fmt(format_args!($($tt)*)).expect("a formatting trait implementation returned an error");
        s
    }};
}

#[cfg(target_pointer_width = "64")]
const _: () = assert!(core::mem::size_of::<SmallStr>() == core::mem::size_of::<String>());
/// `SmallString == SmallStr<16>`, on 64-bit platforms `size_of::<SmallString>()` == `size_of::<String>()`
pub type SmallString = SmallStr<16>;

#[derive(PartialEq, PartialOrd, Eq, Ord)]
pub struct SmallStr<const N: usize = 16> {
    vec: SmallVec<u8, N>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FromUtf8Error<const N: usize> {
    bytes: SmallVec<u8, N>,
    error: Utf8Error,
}

#[derive(Debug)]
pub struct FromUtf16Error(());

impl<const N: usize> SmallStr<N> {
    #[inline]
    pub fn new() -> SmallStr<N> {
        Self {
            vec: SmallVec::new(),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> SmallStr<N> {
        SmallStr {
            vec: SmallVec::with_capacity(capacity),
        }
    }

    #[inline]
    pub fn is_inlined(&self) -> bool {
        !self.vec.spilled()
    }

    #[inline]
    pub fn inline_size(&self) -> usize {
        N
    }

    #[inline]
    pub fn from_utf8(vec: SmallVec<u8, N>) -> Result<SmallStr<N>, FromUtf8Error<N>> {
        match str::from_utf8(&vec) {
            Ok(..) => Ok(SmallStr { vec }),
            Err(e) => Err(FromUtf8Error {
                bytes: vec,
                error: e,
            }),
        }
    }

    #[inline]
    pub fn from_utf8_vec(vec: Vec<u8>) -> Result<SmallStr<N>, FromUtf8Error<N>> {
        let vec = SmallVec::from_vec(vec);
        match str::from_utf8(&vec) {
            Ok(..) => Ok(SmallStr { vec }),
            Err(e) => Err(FromUtf8Error {
                bytes: vec,
                error: e,
            }),
        }
    }

    pub fn from_utf16(v: &[u16]) -> Result<SmallStr<N>, FromUtf16Error> {
        let mut ret = SmallStr::with_capacity(v.len());
        for c in char::decode_utf16(v.iter().cloned()) {
            if let Ok(c) = c {
                ret.push(c);
            } else {
                return Err(FromUtf16Error(()));
            }
        }
        Ok(ret)
    }

    #[inline]
    pub fn from_utf16_lossy(v: &[u16]) -> SmallStr<N> {
        char::decode_utf16(v.iter().cloned())
            .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect()
    }

    #[inline]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> SmallStr<N> {
        unsafe {
            SmallStr {
                vec: SmallVec::from_raw_parts(buf, length, capacity),
            }
        }
    }

    #[inline]
    pub unsafe fn from_utf8_unchecked(bytes: SmallVec<u8, N>) -> SmallStr<N> {
        SmallStr { vec: bytes }
    }

    /// Converts a `SmallStr` into a byte vector.
    ///
    /// This consumes the `SmallStr`, so we do not need to copy its contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let s = SmallString::from("hello");
    /// let bytes = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
    /// ```
    #[inline]
    pub fn into_bytes(self) -> SmallVec<u8, N> {
        self.vec
    }

    /// Extracts a string slice containing the entire `SmallStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let s = SmallStr::<4>::from("foo");
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        self
    }

    /// Converts a `SmallStr` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<4>::from("foobar");
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    /// Appends a given string slice onto the end of this `SmallStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<4>::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    pub fn push_str(&mut self, string: &str) {
        self.vec.extend_from_slice(string.as_bytes())
    }

    /// Returns this `SmallStr`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let s = SmallStr::<4>::with_capacity(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Reserves capacity for at least `additional` bytes more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<4>::new();
    ///
    /// s.reserve(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This might not actually increase the capacity:
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<4>::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of at least 10
    /// let capacity = s.capacity();
    /// assert_eq!(2, s.len());
    /// assert!(capacity >= 10);
    ///
    /// // Since we already have at least an extra 8 capacity, calling this...
    /// s.reserve(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(capacity, s.capacity());
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    /// Reserves the minimum capacity for at least `additional` bytes more than
    /// the current length. Unlike [`reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// [`reserve`]: SmallStr::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::new();
    ///
    /// s.reserve_exact(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This might not actually increase the capacity:
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<5>::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of at least 10
    /// let capacity = s.capacity();
    /// assert_eq!(2, s.len());
    /// assert!(capacity >= 10);
    ///
    /// // Since we already have at least an extra 8 capacity, calling this...
    /// s.reserve_exact(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(capacity, s.capacity());
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    /// Tries to reserve capacity for at least `additional` bytes more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `try_reserve`, capacity will be
    /// greater than or equal to `self.len() + additional` if it returns
    /// `Ok(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::{SmallStr, CollectionAllocErr};
    ///
    /// fn process_data(data: &str) -> Result<SmallStr<4>, CollectionAllocErr> {
    ///     let mut output = SmallStr::<4>::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr> {
        self.vec.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` bytes
    /// more than the current length. Unlike [`try_reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or
    /// equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: SmallStr::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::{SmallStr, CollectionAllocErr};
    ///
    /// fn process_data(data: &str) -> Result<SmallStr, CollectionAllocErr> {
    ///     let mut output = SmallStr::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), CollectionAllocErr> {
        self.vec.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `SmallStr` to match its length.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<1>::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit()
    }

    /// Appends the given [`char`] to the end of this `SmallStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!("abc123", s);
    /// ```
    #[inline]
    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.vec.push(ch as u8),
            _ => self
                .vec
                .extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    /// Returns a byte slice of this `SmallStr`'s contents.
    ///
    /// The inverse of this method is [`from_utf8`].
    ///
    /// [`from_utf8`]: SmallStr::from_utf8
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let s = SmallString::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Shortens this `SmallStr` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `SmallStr` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("abč");
    ///
    /// assert_eq!(s.pop(), Some('č'));
    /// assert_eq!(s.pop(), Some('b'));
    /// assert_eq!(s.pop(), Some('a'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    ///
    /// # Safety
    /// `newlen <= self.len()`
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(newlen);
        }
        Some(ch)
    }

    /// Removes a [`char`] from this `SmallStr` at a byte position and returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `SmallStr`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("abç");
    ///
    /// assert_eq!(s.remove(0), 'a');
    /// assert_eq!(s.remove(1), 'ç');
    /// assert_eq!(s.remove(0), 'b');
    /// ```
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        self.vec.drain(idx..next);
        ch
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place, visiting each character exactly once in the
    /// original order, and preserves the order of the retained characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("f_o_ob_ar");
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s, "foobar");
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("abcde");
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// s.retain(|_| *iter.next().unwrap());
    /// assert_eq!(s, "bce");
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        struct SetLenOnDrop<'a, const N: usize> {
            s: &'a mut SmallStr<N>,
            idx: usize,
            del_bytes: usize,
        }

        impl<'a, const N: usize> Drop for SetLenOnDrop<'a, N> {
            fn drop(&mut self) {
                let new_len = self.idx - self.del_bytes;
                debug_assert!(new_len <= self.s.len());
                unsafe { self.s.vec.set_len(new_len) };
            }
        }

        let len = self.len();
        let mut guard = SetLenOnDrop {
            s: self,
            idx: 0,
            del_bytes: 0,
        };

        while guard.idx < len {
            let ch =
                // SAFETY: `guard.idx` is positive-or-zero and less that len so the `get_unchecked`
                // is in bound. `self` is valid UTF-8 like string and the returned slice starts at
                // a unicode code point so the `Chars` always return one character.
                unsafe { guard.s.get_unchecked(guard.idx..len).chars().next().unwrap_unchecked() };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                guard.del_bytes += ch_len;
            } else if guard.del_bytes > 0 {
                // SAFETY: `guard.idx` is in bound and `guard.del_bytes` represent the number of
                // bytes that are erased from the string so the resulting `guard.idx -
                // guard.del_bytes` always represent a valid unicode code point.
                //
                // `guard.del_bytes` >= `ch.len_utf8()`, so taking a slice with `ch.len_utf8()` len
                // is safe.
                ch.encode_utf8(unsafe {
                    slice::from_raw_parts_mut(
                        guard.s.as_mut_ptr().add(guard.idx - guard.del_bytes),
                        ch.len_utf8(),
                    )
                });
            }

            // Point idx to the next char
            guard.idx += ch_len;
        }

        drop(guard);
    }

    /// Inserts a character into this `SmallStr` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `SmallStr`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::with_capacity(3);
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!("foo", s);
    /// ```
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();
        self.vec.insert_from_slice(idx, bits);
    }

    /// Inserts a string slice into this `SmallStr` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `SmallStr`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("bar");
    ///
    /// s.insert_str(0, "foo");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[inline]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));
        self.vec.insert_from_slice(idx, string.as_bytes());
    }

    /// Returns a mutable reference to the contents of this `SmallStr`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid UTF-8. If this constraint is violated, using
    /// the original `SmallStr` after dropping the `&mut Vec` may violate memory
    /// safety, as the rest of the standard library assumes that `SmallStr`s are
    /// valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut s = SmallString::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// ```
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut SmallVec<u8, N> {
        &mut self.vec
    }

    #[inline]
    pub fn as_vec(&self) -> &SmallVec<u8, N> {
        &self.vec
    }

    /// Returns the length of this `SmallStr`, in bytes, not [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let a = SmallString::from("foo");
    /// assert_eq!(a.len(), 3);
    ///
    /// let fancy_f = SmallString::from("ƒoo");
    /// assert_eq!(fancy_f.len(), 4);
    /// assert_eq!(fancy_f.chars().count(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if this `SmallStr` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let mut v = SmallString::new();
    /// assert!(v.is_empty());
    ///
    /// v.push('a');
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a newly allocated `SmallStr`. `self` contains bytes `[0, at)`, and
    /// the returned `SmallStr` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// # fn main() {
    /// let mut hello = SmallString::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// # }
    /// ```
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> SmallStr<N> {
        assert!(self.is_char_boundary(at));
        let other = self.vec.split_off(at);
        unsafe { SmallStr::from_utf8_unchecked(other) }
    }

    /// Truncates this `SmallStr`, removing all contents.
    ///
    /// While this means the `SmallStr` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let mut s = SmallStr::<0>::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    /// Converts this `SmallStr` into a <code>[Box]<[str]></code>.
    ///
    /// This will drop any excess capacity.
    ///
    /// [str]: prim@str "str"
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let s = SmallString::from("hello");
    ///
    /// let b = s.into_boxed_str();
    /// ```
    #[inline]
    pub fn into_boxed_str(self) -> Box<str> {
        let slice = self.vec.into_boxed_slice();
        unsafe { from_boxed_utf8_unchecked(slice) }
    }

    /// Consumes and leaks the `SmallStr`, returning a mutable reference to the contents,
    /// `&'a mut str`.
    ///
    /// The caller has free choice over the returned lifetime, including `'static`. Indeed,
    /// this function is ideally used for data that lives for the remainder of the program's life,
    /// as dropping the returned reference will cause a memory leak.
    ///
    /// It does not reallocate or shrink the `SmallStr`,
    /// so the leaked allocation may include unused capacity that is not part
    /// of the returned slice. If you don't want that, call [`into_boxed_str`],
    /// and then [`Box::leak`].
    ///
    /// [`into_boxed_str`]: Self::into_boxed_str
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// let x = SmallString::from("bucket");
    /// let static_ref: &'static mut str = x.leak();
    /// assert_eq!(static_ref, "bucket");
    /// # unsafe { Box::from_raw(static_ref); }
    /// ```
    #[inline]
    pub fn leak<'a>(self) -> &'a mut str {
        Box::leak(self.into_boxed_str())
    }
}

impl<const N: usize> FromUtf8Error<N> {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `SmallStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = SmallString::from_utf8_vec(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Returns the bytes that were attempted to convert to a `SmallStr`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = SmallString::from_utf8_vec(bytes);
    ///
    /// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes().into_vec());
    /// ```
    pub fn into_bytes(self) -> SmallVec<u8, N> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
    /// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
    /// an analogue to `FromUtf8Error`. See its documentation for more details
    /// on using it.
    ///
    /// [`std::str`]: core::str "std::str"
    /// [`&str`]: prim@str "&str"
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallString;
    ///
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let error = SmallString::from_utf8_vec(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<const N: usize> fmt::Display for FromUtf8Error<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("invalid utf-16: lone surrogate found", f)
    }
}

#[cfg(any(feature = "unstable", feature = "std"))]
impl<const N: usize> Error for FromUtf8Error<N> {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "invalid utf-8"
    }
}

#[cfg(any(feature = "unstable", feature = "std"))]
impl Error for FromUtf16Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "invalid utf-16"
    }
}

impl<const N: usize> Clone for SmallStr<N> {
    #[inline]
    fn clone(&self) -> Self {
        SmallStr {
            vec: self.vec.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.vec.clone_from(&source.vec);
    }
}

impl<const N: usize> FromIterator<char> for SmallStr<N> {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> SmallStr<N> {
        let mut buf = SmallStr::new();
        buf.extend(iter);
        buf
    }
}

impl<'a, const N: usize> FromIterator<&'a char> for SmallStr<N> {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> SmallStr<N> {
        let mut buf = SmallStr::new();
        buf.extend(iter);
        buf
    }
}

impl<'a, const N: usize> FromIterator<&'a str> for SmallStr<N> {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> SmallStr<N> {
        let mut buf = SmallStr::new();
        buf.extend(iter);
        buf
    }
}

impl<const N: usize> FromIterator<SmallStr<N>> for SmallStr<N> {
    fn from_iter<I: IntoIterator<Item = SmallStr<N>>>(iter: I) -> SmallStr<N> {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `SmallStr`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => SmallStr::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

impl<const N: usize> FromIterator<Box<str>> for SmallStr<N> {
    fn from_iter<I: IntoIterator<Item = Box<str>>>(iter: I) -> SmallStr<N> {
        let mut buf = SmallStr::new();
        buf.extend(iter);
        buf
    }
}

impl<'a, const N: usize> FromIterator<Cow<'a, str>> for SmallStr<N> {
    fn from_iter<I: IntoIterator<Item = Cow<'a, str>>>(iter: I) -> SmallStr<N> {
        let mut s = SmallStr::new();
        s.extend(iter);
        s
    }
}

impl<const N: usize> Extend<char> for SmallStr<N> {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_one(&mut self, c: char) {
        self.push(c);
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

impl<'a, const N: usize> Extend<&'a char> for SmallStr<N> {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_one(&mut self, &c: &'a char) {
        self.push(c);
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

impl<'a, const N: usize> Extend<&'a str> for SmallStr<N> {
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(s));
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_one(&mut self, s: &'a str) {
        self.push_str(s);
    }
}

impl<const N: usize> Extend<Box<str>> for SmallStr<N> {
    fn extend<I: IntoIterator<Item = Box<str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

impl<const N: usize> Extend<SmallStr<N>> for SmallStr<N> {
    fn extend<I: IntoIterator<Item = SmallStr<N>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_one(&mut self, s: SmallStr<N>) {
        self.push_str(&s);
    }
}

impl<'a, const N: usize> Extend<Cow<'a, str>> for SmallStr<N> {
    fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }

    #[inline]
    #[cfg(feature = "unstable")]
    fn extend_one(&mut self, s: Cow<'a, str>) {
        self.push_str(&s);
    }
}

impl<const N: usize> PartialEq<str> for SmallStr<N> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        PartialEq::eq(self.as_str(), &other[..])
    }
    #[inline]
    fn ne(&self, other: &str) -> bool {
        PartialEq::ne(self.as_str(), &other[..])
    }
}

impl<const N: usize> PartialEq<SmallStr<N>> for str {
    #[inline]
    fn eq(&self, other: &SmallStr<N>) -> bool {
        PartialEq::eq(&self[..], other.as_str())
    }
    #[inline]
    fn ne(&self, other: &SmallStr<N>) -> bool {
        PartialEq::ne(&self[..], other.as_str())
    }
}

impl<'a, const N: usize> PartialEq<&'a str> for SmallStr<N> {
    #[inline]
    fn eq(&self, other: &&'a str) -> bool {
        PartialEq::eq(self.as_str(), &other[..])
    }
    #[inline]
    fn ne(&self, other: &&'a str) -> bool {
        PartialEq::ne(self.as_str(), &other[..])
    }
}

impl<'a, const N: usize> PartialEq<SmallStr<N>> for &'a str {
    #[inline]
    fn eq(&self, other: &SmallStr<N>) -> bool {
        PartialEq::eq(&self[..], other.as_str())
    }
    #[inline]
    fn ne(&self, other: &SmallStr<N>) -> bool {
        PartialEq::ne(&self[..], other.as_str())
    }
}

impl<'a, const N: usize> PartialEq<SmallStr<N>> for Cow<'a, str> {
    #[inline]
    fn eq(&self, other: &SmallStr<N>) -> bool {
        PartialEq::eq(&self[..], other.as_str())
    }
    #[inline]
    fn ne(&self, other: &SmallStr<N>) -> bool {
        PartialEq::ne(&self[..], other.as_str())
    }
}

impl<'a, const N: usize> PartialEq<Cow<'a, str>> for SmallStr<N> {
    #[inline]
    fn eq(&self, other: &Cow<'a, str>) -> bool {
        PartialEq::eq(self.as_str(), &other[..])
    }
    #[inline]
    fn ne(&self, other: &Cow<'a, str>) -> bool {
        PartialEq::ne(self.as_str(), &other[..])
    }
}

impl<'a, const N: usize> PartialEq<SmallStr<N>> for String {
    #[inline]
    fn eq(&self, other: &SmallStr<N>) -> bool {
        PartialEq::eq(&self[..], other.as_str())
    }
    #[inline]
    fn ne(&self, other: &SmallStr<N>) -> bool {
        PartialEq::ne(&self[..], other.as_str())
    }
}

impl<'a, const N: usize> PartialEq<String> for SmallStr<N> {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        PartialEq::eq(self.as_str(), &other[..])
    }
    #[inline]
    fn ne(&self, other: &String) -> bool {
        PartialEq::ne(self.as_str(), &other[..])
    }
}

impl Default for SmallStr<16> {
    #[inline]
    fn default() -> SmallStr {
        SmallStr::new()
    }
}

impl<const N: usize> fmt::Display for SmallStr<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Debug for SmallStr<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> hash::Hash for SmallStr<N> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// ```
/// use small_str::SmallString;
///
/// let mut s = SmallString::from("foo");
/// s += "bar";
/// assert_eq!(s, "foobar");
/// ```
impl<const N: usize> Add<&str> for SmallStr<N> {
    type Output = SmallStr<N>;

    #[inline]
    fn add(mut self, other: &str) -> SmallStr<N> {
        self.push_str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `SmallStr`.
///
/// This has the same behavior as the [`push_str`][SmallStr::push_str] method.
impl<const N: usize> AddAssign<&str> for SmallStr<N> {
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}

impl<const N: usize, I> ops::Index<I> for SmallStr<N>
where
    I: slice::SliceIndex<str>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        &self.as_str()[index]
    }
}

impl<const N: usize, I> ops::IndexMut<I> for SmallStr<N>
where
    I: slice::SliceIndex<str>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        &mut self.as_mut_str()[index]
    }
}

impl<const N: usize> ops::Deref for SmallStr<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}

impl<const N: usize> ops::DerefMut for SmallStr<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

impl<const N: usize> FromStr for SmallStr<N> {
    type Err = core::convert::Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<SmallStr<N>, Self::Err> {
        Ok(SmallStr::from(s))
    }
}

impl<const N: usize> AsRef<str> for SmallStr<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for SmallStr<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> AsRef<[u8]> for SmallStr<N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> From<&str> for SmallStr<N> {
    /// Converts a `&str` into a [`SmallStr`].
    ///
    /// The result is allocated on the heap.
    #[inline]
    fn from(s: &str) -> Self {
        SmallStr {
            vec: SmallVec::from_slice(s.as_bytes()),
        }
    }
}

impl<const N: usize> From<&mut str> for SmallStr<N> {
    /// Converts a `&mut str` into a [`SmallStr`].
    ///
    /// The result is allocated on the heap.
    #[inline]
    fn from(s: &mut str) -> SmallStr<N> {
        SmallStr::from(&*s)
    }
}

impl<const N: usize, const N2: usize> From<&SmallStr<N>> for SmallStr<N2> {
    /// Converts a `&String` into a [`String`].
    ///
    /// This clones `s` and returns the clone.
    #[inline]
    fn from(s: &SmallStr<N>) -> SmallStr<N2> {
        SmallStr {
            vec: SmallVec::from_slice(&s.vec),
        }
    }
}

impl<const N: usize> From<Box<str>> for SmallStr<N> {
    /// Converts the given boxed `str` slice to a [`SmallStr`].
    /// It is notable that the `str` slice is owned.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let s1: SmallStr = SmallStr::from("hello world");
    /// let s2: Box<str> = s1.into_boxed_str();
    /// let s3: SmallStr = SmallStr::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: Box<str>) -> SmallStr<N> {
        SmallStr::from(s.as_ref())
    }
}

impl<const N: usize> From<SmallStr<N>> for Box<str> {
    /// Converts the given [`SmallStr`] to a boxed `str` slice that is owned.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let s1: SmallStr = SmallStr::from("hello world");
    /// let s2: Box<str> = Box::from(s1);
    /// let s3: SmallStr = SmallStr::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: SmallStr<N>) -> Box<str> {
        s.into_boxed_str()
    }
}

impl<'a, const N: usize> From<Cow<'a, str>> for SmallStr<N> {
    /// Converts a clone-on-write string to an owned
    /// instance of [`SmallStr`].
    ///
    /// This extracts the owned string,
    /// clones the string if it is not already owned.
    ///
    /// # Example
    ///
    /// ```
    /// use small_str::SmallStr;
    ///
    /// # use std::borrow::Cow;
    /// // If the string is not owned...
    /// let cow: Cow<'_, str> = Cow::Borrowed("eggplant");
    /// // It will allocate on the heap and copy the string.
    /// let owned: SmallStr = SmallStr::from(cow);
    /// assert_eq!(&owned[..], "eggplant");
    /// ```
    fn from(s: Cow<'a, str>) -> SmallStr<N> {
        match s {
            Cow::Borrowed(s) => SmallStr::from(s),
            Cow::Owned(owned) => SmallStr::from(owned),
        }
    }
}

impl<'a, const N: usize> From<SmallStr<N>> for Cow<'a, str> {
    /// Converts a [`SmallStr`] into an [`Owned`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// use small_str::{SmallStr, ToSmallStr};
    ///
    /// # use std::borrow::Cow;
    /// let s: SmallStr = "eggplant".to_smallstr();
    /// let s2 = "eggplant".to_string();
    /// assert_eq!(Cow::from(s), Cow::<'static, str>::Owned(s2));
    /// ```
    ///
    /// [`Owned`]: std::borrow::Cow::Owned "borrow::Cow::Owned"
    #[inline]
    fn from(s: SmallStr<N>) -> Cow<'a, str> {
        Cow::Owned(String::from(s))
    }
}

impl<'a, const N: usize> From<&'a SmallStr<N>> for Cow<'a, str> {
    /// Converts a [`SmallStr`] reference into a [`Borrowed`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// use small_str::{SmallStr, ToSmallStr};
    ///
    /// # use std::borrow::Cow;
    /// let s: SmallStr = "eggplant".to_smallstr();
    /// assert_eq!(Cow::from(&s), Cow::Borrowed("eggplant"));
    /// ```
    ///
    /// [`Borrowed`]: std::borrow::Cow::Borrowed "borrow::Cow::Borrowed"
    #[inline]
    fn from(s: &'a SmallStr<N>) -> Cow<'a, str> {
        Cow::Borrowed(s.as_str())
    }
}

impl<const N: usize> From<String> for SmallStr<N> {
    fn from(value: String) -> Self {
        SmallStr {
            vec: SmallVec::from_vec(value.into_bytes()),
        }
    }
}

impl<'a, const N: usize> From<&'a String> for SmallStr<N> {
    fn from(value: &'a String) -> Self {
        SmallStr::from(&**value)
    }
}

impl<const N: usize> From<SmallStr<N>> for String {
    fn from(value: SmallStr<N>) -> Self {
        unsafe { String::from_utf8_unchecked(value.vec.into_vec()) }
    }
}

impl<'a, const N: usize> From<&'a SmallStr<N>> for String {
    fn from(value: &'a SmallStr<N>) -> Self {
        value.as_str().to_owned()
    }
}

impl<const N: usize> From<char> for SmallStr<N> {
    /// Allocates an owned [`SmallStr`] from a single character.
    ///
    /// # Example
    /// ```
    /// use small_str::SmallStr;
    ///
    /// let c: char = 'a';
    /// let s: SmallStr = SmallStr::from(c);
    /// assert_eq!("a", &s[..]);
    /// ```
    #[inline]
    fn from(c: char) -> Self {
        let mut s = SmallStr::with_capacity(c.len_utf8());
        s.push(c);
        s
    }
}

impl<const N: usize> Write for SmallStr<N> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

pub trait ToSmallStr {
    /// Converts the given value to a `SmallStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_str::{SmallString, ToSmallStr};
    ///
    /// let i = 5;
    /// let five = SmallString::from("5");
    ///
    /// assert_eq!(five, i.to_smallstr());
    /// ```
    #[allow(dead_code)]
    fn to_smallstr<const N: usize>(&self) -> SmallStr<N>;
}

impl<T: fmt::Display + ?Sized> ToSmallStr for T {
    fn to_smallstr<const N: usize>(&self) -> SmallStr<N> {
        let mut buf = SmallStr::new();
        buf.write_fmt(format_args!("{}", self))
            .expect("a Display implementation returned an error unexpectedly");
        buf
    }
}

#[cfg(feature = "serde")]
use serde::de::{Error as SerdeError, Unexpected, Visitor};

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for SmallStr<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_str().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for SmallStr<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct SmallStrVisitor<const N: usize>;

        impl<'a, const N: usize> Visitor<'a> for SmallStrVisitor<N> {
            type Value = SmallStr<N>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a string")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: SerdeError,
            {
                Ok(SmallStr::from(v))
            }

            fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
            where
                E: SerdeError,
            {
                Ok(SmallStr::from(v))
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: SerdeError,
            {
                Ok(SmallStr::from(v))
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: SerdeError,
            {
                match core::str::from_utf8(v) {
                    Ok(s) => Ok(SmallStr::from(s)),
                    Err(_) => Err(SerdeError::invalid_value(Unexpected::Bytes(v), &self)),
                }
            }

            fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
            where
                E: SerdeError,
            {
                match core::str::from_utf8(v) {
                    Ok(s) => Ok(SmallStr::from(s)),
                    Err(_) => Err(SerdeError::invalid_value(Unexpected::Bytes(v), &self)),
                }
            }

            fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
            where
                E: SerdeError,
            {
                match String::from_utf8(v) {
                    Ok(s) => Ok(SmallStr::from(s)),
                    Err(e) => Err(SerdeError::invalid_value(
                        Unexpected::Bytes(&e.into_bytes()),
                        &self,
                    )),
                }
            }
        }

        deserializer.deserialize_str(SmallStrVisitor)
    }
}
