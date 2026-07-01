//! The Poly/ML runtime, reimplemented in Rust: the bytecode interpreter,
//! RTS (runtime-system) calls, exceptions, the copying (Cheney) GC, the
//! real-thread scheduler, and heap-image export. This crate is the Rust
//! port of `vendor/polyml/libpolyml/`; non-trivial interpreter opcode
//! handlers cite the upstream `bytecode.cpp` line ranges they port.
//!
//! It executes real Poly/ML end to end: boots the upstream bootstrap
//! image, self-compiles the full 7-stage compiler chain, and hosts HOL4
//! and Isabelle/Pure. Faithfulness + memory-safety methodology:
//! `docs/correctness-and-safety.md`; operational guide: the repo-root
//! `CLAUDE.md`.

pub mod env;
pub mod export;
pub mod gc;
pub mod interpreter;
pub mod interrupt;
pub mod jit_bridge;
pub mod length_word;
pub mod loader;
pub mod poly_word;
pub mod rts;
pub mod sched;
pub mod session;
pub mod space;

pub use env::env_flag;
pub use interpreter::{
    ExnCtxC, InterpError, Interpreter, JitEntry, RegionDispatchFn, RegionEntry, RegionRetC,
    StepResult, install_region_dispatch,
};
pub use interrupt::{clear_interrupt, interrupt_pending, request_interrupt, take_interrupt};
pub use jit_bridge::{
    JIT_INTERP, jit_dispatch_alloc, jit_dispatch_alloc_bytes, jit_dispatch_alloc_mut_closure,
    jit_dispatch_closure_alloc, jit_dispatch_closure_call, jit_dispatch_dynamic_call,
    jit_dispatch_get_thread_id, with_jit_interp,
};
pub use loader::{LoadError, LoadedImage, load_image};
pub use poly_word::PolyWord;
pub use rts::{RtsFn, RtsTable, patch_entry_points};
pub use session::{RunOutcome, RunResult, Session, SessionConfig, SessionError};
pub use space::{MemorySpace, SpaceKind};
