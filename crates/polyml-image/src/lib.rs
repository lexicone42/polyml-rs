//! PolyML heap-image formats.
//!
//! Stage 2 starts with the legacy `pexport` text format produced by
//! upstream PolyML (`vendor/polyml/libpolyml/pexport.cpp`). Eventually
//! this crate will also implement the new `bicimage` format described
//! in `notes/hard-problems.md` §5.

pub mod bicimage;
pub mod pexport;

pub use bicimage::{BicError, is_bicimage};
pub use pexport::{Image, Object, ObjectBody, ObjectId, Value};
