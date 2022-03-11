use std::io;
use std::io::prelude::*;
use std::mem;

use crate::Bytes;

mod private {
    pub trait Sealed: Sized {}
}

pub trait FromLeBytes: private::Sealed {
    fn from_le(bytes: &mut Bytes<'_>) -> io::Result<Self>;
}

pub trait FromBeBytes: private::Sealed {
    fn from_be(bytes: &mut Bytes<'_>) -> io::Result<Self>;
}

macro_rules! impl_from_bytes {
    ($($ty:ident)+) => ($(
        impl FromLeBytes for $ty {
            fn from_le(bytes: &mut Bytes<'_>) -> io::Result<Self> {
                let mut buf = [0; mem::size_of::<Self>()];
                bytes.read_exact(&mut buf)?;
                Ok(Self::from_le_bytes(buf))
            }
        }

        impl FromBeBytes for $ty {
            fn from_be(bytes: &mut Bytes<'_>) -> io::Result<Self> {
                let mut buf = [0; mem::size_of::<Self>()];
                bytes.read_exact(&mut buf)?;
                Ok(Self::from_be_bytes(buf))
            }
        }

        impl private::Sealed for $ty {}
    )+)
}

impl_from_bytes! { u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 }
