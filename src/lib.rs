//! Defines a cursor over a slice of bytes.

#![no_std]

#[cfg(feature = "std")]
extern crate std;

use core::mem;
use core::result;

/////////////////////////////////////////////////////////////////////////
// Definitions
/////////////////////////////////////////////////////////////////////////

/// A result type to use in this crate.
pub type Result<T> = result::Result<T, Error>;

/// A generic error that can occur while reading bytes.
#[derive(Debug, PartialEq)]
#[cfg_attr(
    feature = "std",
    derive(thiserror::Error),
    error("wanted {size} bytes but {} bytes remain", self.len - self.pos),
)]
pub struct Error {
    size: usize,
    len: usize,
    pos: usize,
}

/// A cursor over a slice of bytes.
#[derive(Debug, Clone)]
pub struct Bytes<'a> {
    inner: &'a [u8],
    pos: usize,
}

/// Fallible conversion of bytes to a new type.
///
/// # Examples
///
/// ```
/// use frombytes::{Bytes, Error, FromBytes};
///
/// struct MyStruct {
///     a: u32,
///     b: i16,
/// }
///
/// impl FromBytes for MyStruct {
///     // we simply use the same error that primitives use
///     // but any error could be used
///     type Error = Error;
///
///     fn from_bytes(bytes: &mut Bytes) -> Result<Self, Self::Error> {
///         // uses type inference to know to read a `u32`
///         let a = bytes.read()?;
///         // uses type inference to know to read a `i16`
///         let b = bytes.read()?;
///         Ok(Self { a, b })
///     }
/// }
/// ```
pub trait FromBytes: Sized {
    /// The associated error which can be returned from parsing.
    ///
    /// All primitive types as well as radiotap fields implementing this trait
    /// set this error to [`Error`](struct.Error.html).
    type Error;

    /// Construct a type from bytes.
    ///
    /// This method is often used implicitly through
    /// [`Bytes`](struct.Bytes.html)'s [`read`](struct.Bytes.html#method.read)
    /// method.
    fn from_bytes(bytes: &mut Bytes) -> result::Result<Self, Self::Error>;
}

/////////////////////////////////////////////////////////////////////////
// Implementations
/////////////////////////////////////////////////////////////////////////

impl<'a> From<&'a [u8]> for Bytes<'a> {
    fn from(bytes: &'a [u8]) -> Self {
        Self::from_slice(bytes)
    }
}

impl<'a> Bytes<'a> {
    /// Returns a new cursor over a slice of bytes.
    pub const fn from_slice(bytes: &'a [u8]) -> Self {
        Self {
            inner: bytes,
            pos: 0,
        }
    }

    /// Consumes the `Bytes` and returns the underlying data.
    pub const fn into_inner(self) -> &'a [u8] {
        self.inner
    }

    /// Returns the current position of the `Bytes`.
    pub const fn position(&self) -> usize {
        self.pos
    }

    /// Returns the total length of the original underlying buffer.
    const fn len(&self) -> usize {
        self.inner.len()
    }

    fn checked_pos(&self, new_pos: usize) -> Result<usize> {
        let pos = self.pos;
        let len = self.len();
        if new_pos > self.len() {
            Err(Error {
                size: new_pos - pos,
                len,
                pos,
            })
        } else {
            Ok(new_pos)
        }
    }

    fn set_position(&mut self, new_pos: usize) -> Result<()> {
        self.pos = self.checked_pos(new_pos)?;
        Ok(())
    }

    /// Advances the position in the bytes.
    pub fn advance(&mut self, size: usize) -> Result<()> {
        self.set_position(self.pos + size)
    }

    /// Aligns the bytes to a particular word.
    ///
    /// # Panics
    ///
    /// If the align size is a not one of the following powers of two: 1, 2, 4,
    /// 8, or 16.
    pub fn align(&mut self, align: usize) -> Result<()> {
        assert!(matches!(align, 1 | 2 | 4 | 8 | 16));
        self.set_position((self.pos + align - 1) & !(align - 1))
    }

    fn read_slice(&mut self, size: usize) -> Result<&'a [u8]> {
        let start = self.pos;
        self.pos = self.checked_pos(start + size)?;
        Ok(&self.inner[start..self.pos])
    }

    /// Allows types implementing [`FromBytes`](trait.FromBytes.html) to be
    /// easily read from these bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use frombytes::*;
    /// let mut bytes = Bytes::from_slice(&[0x78, 0x56, 0x34, 0x12]);
    /// let value: u32 = bytes.read().unwrap();
    /// assert_eq!(value, 0x12345678);
    /// ```
    pub fn read<T: FromBytes>(&mut self) -> result::Result<T, <T as FromBytes>::Error> {
        T::from_bytes(self)
    }
}

macro_rules! impl_primitive {
    ($Type:ty) => {
        impl FromBytes for $Type {
            type Error = Error;

            fn from_bytes(bytes: &mut Bytes) -> Result<Self> {
                const COUNT: usize = mem::size_of::<$Type>();
                let mut buf = [0; COUNT];
                buf.copy_from_slice(bytes.read_slice(COUNT)?);
                Ok(Self::from_le_bytes(buf))
            }
        }
    };
}

impl_primitive!(u8);
impl_primitive!(u16);
impl_primitive!(u32);
impl_primitive!(u64);
impl_primitive!(u128);

impl_primitive!(i8);
impl_primitive!(i16);
impl_primitive!(i32);
impl_primitive!(i64);
impl_primitive!(i128);

macro_rules! impl_array {
    ($SIZE:expr) => {
        impl<T, E> FromBytes for [T; $SIZE]
        where
            T: FromBytes<Error = E> + Default,
        {
            type Error = E;

            fn from_bytes(bytes: &mut Bytes) -> result::Result<Self, E> {
                let mut buf = Self::default();
                for i in 0..$SIZE {
                    buf[i] = bytes.read()?;
                }
                Ok(buf)
            }
        }
    };
}

impl_array!(1);
impl_array!(2);
impl_array!(3);
impl_array!(4);

/////////////////////////////////////////////////////////////////////////
// Unit tests
/////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bytes_align() {
        fn check_align(align: usize, expected_pos: usize) {
            let mut bytes = Bytes {
                inner: &[0; 25],
                pos: 13,
            };
            bytes.align(align).unwrap();
            assert_eq!(bytes.pos, expected_pos);
        }

        check_align(1, 13);
        check_align(2, 14);
        check_align(4, 16);
        check_align(8, 16);
        check_align(16, 16);
    }

    #[test]
    fn bytes_read_primitive_x8() {
        let mut bytes = Bytes::from_slice(&[1, !2 + 1]);
        assert_eq!(bytes.read::<u8>().unwrap(), 1);
        assert_eq!(bytes.read::<i8>().unwrap(), -2);
    }

    #[test]
    fn bytes_read_primitive_x16() {
        let mut bytes = Bytes::from_slice(&[0xfb, 0xfa, 0xff, 0xff]);
        assert_eq!(bytes.read::<u16>().unwrap(), 0xfafb);
        assert_eq!(bytes.read::<i16>().unwrap(), -0x0001);
    }

    #[test]
    fn bytes_read_array_primitives() {
        let mut bytes = Bytes::from_slice(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
        assert_eq!(
            bytes.read::<[u32; 3]>().unwrap(),
            [0x04030201, 0x08070605, 0x0C0B0A09]
        );
    }

    #[test]
    fn bytes_read_array_newtype() {
        #[derive(Debug, Default, PartialEq)]
        struct NewType(i16);

        impl FromBytes for NewType {
            type Error = Error;

            fn from_bytes(bytes: &mut Bytes) -> Result<Self> {
                bytes.read().map(Self)
            }
        }

        let mut bytes = Bytes::from_slice(&[1, 2, 3, 4, 5, 6]);
        assert_eq!(
            bytes.read::<[NewType; 3]>().unwrap(),
            [NewType(0x0201), NewType(0x0403), NewType(0x0605)]
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn error_display() {
        let mut bytes = Bytes::from_slice(&[]);
        let err = bytes.read::<u8>().unwrap_err();
        assert_eq!(
            std::string::ToString::to_string(&err),
            "wanted 1 bytes but 0 bytes remain"
        );
    }
}
