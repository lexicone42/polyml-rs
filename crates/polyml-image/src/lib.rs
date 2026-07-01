//! PolyML heap-image formats.
//!
//! Two formats, one object model: the legacy `pexport` text format
//! produced by upstream PolyML (`vendor/polyml/libpolyml/pexport.cpp`),
//! and the compact binary `bicimage` format (endian-neutral on the wire,
//! roughly half the size, loads + runs identically). `poly bic` converts
//! between them; `poly run` auto-detects the format.

pub mod bicimage;
pub mod pexport;

use thiserror::Error;

pub use bicimage::{BicError, is_bicimage};
pub use pexport::{Image, Object, ObjectBody, ObjectId, ParseError, Value};

/// Error from [`parse_auto`]: the detected format's reader error.
#[derive(Debug, Error)]
pub enum ParseAutoError {
    /// The bytes carried the bicimage magic but failed the binary reader.
    #[error(transparent)]
    Bic(#[from] BicError),
    /// The bytes were read as pexport text and failed that parser.
    #[error(transparent)]
    Pexport(#[from] ParseError),
}

/// Parse image bytes, auto-detecting the binary bicimage format (by its
/// magic prefix) vs the pexport text format.
///
/// Every consumer that accepts an image path (`poly run` / `inspect` /
/// `bic`, embedding sessions) accepts either form through this one
/// detector.
pub fn parse_auto(bytes: &[u8]) -> Result<Image, ParseAutoError> {
    if is_bicimage(bytes) {
        Ok(Image::read_bic(bytes)?)
    } else {
        Ok(Image::parse(bytes)?)
    }
}
