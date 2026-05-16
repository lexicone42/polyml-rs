//! PolyML runtime: heap, GC, scheduler, FFI, exceptions.
//!
//! See `notes/runtime-gc.md` and `notes/runtime-scheduler-ffi.md` for
//! the design background. This crate is the Rust reimplementation of
//! `vendor/polyml/libpolyml/`.
//!
//! Stage 2 status: just the value model and a heap-image loader so
//! far. No GC, no scheduler, no real execution.

pub mod length_word;
pub mod loader;
pub mod poly_word;
pub mod space;

pub use loader::{load_image, LoadError, LoadedImage};
pub use poly_word::PolyWord;
pub use space::{MemorySpace, SpaceKind};
