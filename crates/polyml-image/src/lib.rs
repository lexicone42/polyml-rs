//! PolyML heap-image formats.
//!
//! Two formats, one object model: the legacy `pexport` text format
//! produced by upstream PolyML (`vendor/polyml/libpolyml/pexport.cpp`),
//! and the compact binary `bicimage` format (endian-neutral on the wire,
//! roughly half the size, loads + runs identically). `poly bic` converts
//! between them; `poly run` auto-detects the format.

pub mod bicimage;
pub mod pexport;

pub use bicimage::{BicError, is_bicimage};
pub use pexport::{Image, Object, ObjectBody, ObjectId, Value};
