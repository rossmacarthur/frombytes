//! Just a little crate to test that `frombytes` compiles in a `no_std` context.
//!
//! Should be run in CI like: `cargo test --manifest-path tests/no_std/Cargo.toml`

#![no_std]

#[test]
fn basic() {
    let mut bytes = frombytes::Bytes::from_slice(&[77]);
    assert_eq!(bytes.read::<u8>().unwrap(), 77);
}
