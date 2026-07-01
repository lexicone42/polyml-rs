//! Safe embedding facade: load and run a Poly/ML heap image without
//! touching the unsafe interpreter plumbing.
//!
//! [`Session`] owns the whole load-and-run ritual the `poly run` CLI
//! performs — parse (either image format), load, runnability gate, RTS
//! table + entry-point patching, root extraction, image-mutable-space
//! GC-root registration, and entry-frame seeding — behind a safe
//! constructor. Omitting any single step of that ritual is a
//! correctness or memory-safety hazard; skipping the GC-root
//! registration in particular is a use-after-free (the image's global
//! namespace hashtable holds pointers into the alloc space the GC
//! would otherwise not forward — see the post-mortem in
//! `examples/gc_tiny_heap_stress.rs`). Encapsulating the ritual here
//! keeps every embedder off that path.
//!
//! The defaults ([`SessionConfig::default`]) match the CLI exactly:
//! 1M-word ML stack, 1.6 GB heap (`POLYML_HEAP_BYTES` overrides),
//! empty `CommandLine.arguments`, trusted mode. A bootstrap image run
//! through a default `Session` is byte-identical to `poly run`.
//!
//! Signal handling is NOT installed here (it is process-global policy,
//! so it belongs to the embedder): wire your own SIGINT handler to
//! [`crate::request_interrupt`] if you want Ctrl-C to raise the SML
//! `Interrupt` exception the way the CLI does.
//!
//! ```no_run
//! use polyml_runtime::{RunOutcome, Session, SessionConfig};
//!
//! let bytes = std::fs::read("bootstrap64.txt").unwrap();
//! let mut session = Session::from_bytes(&bytes, SessionConfig::default()).unwrap();
//! let result = session.run(5_000_000);
//! println!("{} step(s) -> {:?}", result.steps, result.outcome);
//! ```

use std::sync::Arc;

use polyml_image::Image;
use thiserror::Error;

use crate::interpreter::{InterpError, Interpreter, StepResult};
use crate::loader::{LoadError, LoadedImage, load_image};
use crate::poly_word::PolyWord;
use crate::rts::{RtsTable, patch_entry_points};

/// Configuration for a [`Session`]. `Default` matches the `poly run`
/// CLI (see field docs), so the default session reproduces the CLI's
/// execution byte-for-byte.
#[derive(Debug, Clone)]
pub struct SessionConfig {
    /// ML stack capacity in words. CLI default: 1M words (8 MB).
    pub stack_words: usize,
    /// Alloc-space (heap) capacity in bytes. The default reads
    /// `POLYML_HEAP_BYTES`, falling back to 1.6 GB — small enough that
    /// the GC auto-fires at 80% and keeps peak RSS bounded (a *larger*
    /// heap can postpone GC past a workload's working set and OOM).
    pub heap_bytes: usize,
    /// Arguments visible to SML via `CommandLine.arguments()`. Process-
    /// global (like the CLI's `-- ARGS`); the constructor publishes them.
    pub args: Vec<String>,
    /// Run in UNTRUSTED (typed-deref safe) mode — for images of foreign
    /// provenance. Also enabled when the loader marked the image
    /// untrusted. The trusted default is byte-identical to `poly run`.
    pub untrusted: bool,
}

impl Default for SessionConfig {
    fn default() -> Self {
        let heap_bytes = std::env::var("POLYML_HEAP_BYTES")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(1_600 * 1024 * 1024);
        Self {
            stack_words: 1024 * 1024,
            heap_bytes,
            args: Vec::new(),
            untrusted: false,
        }
    }
}

/// Why a [`Session`] could not be constructed.
#[derive(Debug, Error)]
pub enum SessionError {
    /// The bytes parsed as neither image format.
    #[error("image parse: {0}")]
    Parse(#[from] polyml_image::ParseAutoError),
    /// The parsed image failed to load into heap spaces.
    #[error("image load: {0}")]
    Load(#[from] LoadError),
    /// The image loaded but its root is not a runnable closure — running
    /// it would wild-deref (a loader-fuzz finding; see
    /// [`LoadedImage::runnable`]).
    #[error("image is not runnable: {0}")]
    NotRunnable(&'static str),
}

/// How a [`Session::run`] call ended.
#[derive(Debug, Clone)]
pub enum RunOutcome {
    /// The root function returned this value. `Tagged(0)` is the clean
    /// exit (the PolyFinish convention carries a process exit code).
    Returned(PolyWord),
    /// The step budget ran out with the image still running. Call
    /// [`Session::run`] again to continue.
    StepBudgetExhausted,
    /// The interpreter reached an opcode it does not implement.
    Unimplemented {
        /// The opcode byte.
        op: u8,
        /// Whether it was an ESCAPE-prefixed extended opcode.
        extended: bool,
    },
    /// The interpreter halted with a runtime error.
    Halted(InterpError),
}

/// What a [`Session::run`] call executed and how it ended.
#[derive(Debug, Clone)]
pub struct RunResult {
    /// Bytecode steps executed by THIS call (reported on both the clean
    /// and the halted path).
    pub steps: u64,
    /// The terminal state.
    pub outcome: RunOutcome,
}

/// A loaded Poly/ML heap image plus an interpreter seeded on its root
/// closure, ready to [`run`](Self::run).
pub struct Session {
    // Field order is load-bearing: `interp` holds raw pointers into
    // `loaded`'s spaces, so it must drop first.
    interp: Interpreter,
    // Owns the heap spaces the interpreter's pointers reference. The
    // `MemorySpace` storage is a `Box<[PolyWord]>`, so moving the
    // `Session` does not move the pointed-to words.
    _loaded: LoadedImage,
    unresolved: Vec<String>,
}

impl Session {
    /// Parse `bytes` (auto-detecting pexport text vs binary bicimage),
    /// load, and prepare a runnable session.
    pub fn from_bytes(bytes: &[u8], config: SessionConfig) -> Result<Self, SessionError> {
        let image = polyml_image::parse_auto(bytes)?;
        Self::from_image(&image, config)
    }

    /// Load and prepare an already-parsed [`Image`].
    pub fn from_image(image: &Image, config: SessionConfig) -> Result<Self, SessionError> {
        Self::from_loaded(load_image(image)?, config)
    }

    /// Prepare an already-loaded image. This is the whole `poly run`
    /// setup ritual behind a safe signature: runnability gate →
    /// process-global RTS state → RTS table + entry-point patching →
    /// root extraction → interpreter construction (stack + heap
    /// sizing) → image-mutable-space GC-root registration →
    /// entry-frame seeding.
    pub fn from_loaded(
        mut loaded: LoadedImage,
        config: SessionConfig,
    ) -> Result<Self, SessionError> {
        // Gate FIRST: everything below derefs the root as a closure. An
        // untrusted/corrupt image with a non-closure root would wild-deref.
        loaded.runnable.map_err(SessionError::NotRunnable)?;

        // Process-global RTS state, exactly as the CLI sets it: reset any
        // previous run's PolyFinish flag, publish CommandLine.arguments.
        crate::rts::clear_finish_requested();
        crate::rts::set_command_args(config.args);

        let rts = Arc::new(RtsTable::new());
        let (_patched, unresolved) = patch_entry_points(&mut loaded, &rts);

        // Set up the call frame manually (we pretend we're in the middle
        // of a CALL on the root closure).
        let root_closure_word = PolyWord::from_ptr(loaded.root);
        // SAFETY: the runnability gate above guarantees `loaded.root` is a
        // closure whose word 0 references a code object; `loaded` is owned
        // by the returned Session and outlives the interpreter (field
        // drop order).
        let code_obj_ptr = unsafe { *loaded.root }.as_ptr::<PolyWord>();

        // Register the mutable image space as a GC root region — the
        // global namespace hashtable lives here and references runtime
        // alloc-space objects (compiled structures, etc.). Without
        // scanning it the GC would collect freshly-compiled code (a
        // use-after-free; see examples/gc_tiny_heap_stress.rs).
        let image_mut_ptr = loaded.mutable.iter().next().map(std::ptr::from_ref);
        let image_mut_len = loaded.mutable.used_words();

        // SAFETY: `code_obj_ptr` is the root closure's code object,
        // validated by the runnability gate; it lives in `loaded`'s code
        // space, which the Session keeps alive for the interpreter's
        // whole lifetime.
        let mut interp = unsafe { Interpreter::from_code_object(config.stack_words, code_obj_ptr) }
            .with_default_alloc_space_bytes(config.heap_bytes)
            .with_rts(rts);
        if let Some(p) = image_mut_ptr {
            interp = interp.with_image_mutable_root(p, image_mut_len);
        }
        // UNTRUSTED (safe) mode: register the loaded image's spaces with
        // the typed-deref predicate. Skipped entirely on the trusted
        // default → byte-identical to `poly run`.
        if config.untrusted || loaded.untrusted {
            let [immutable, mutable, code] = loaded.space_bounds();
            interp = interp
                .with_untrusted_spaces(immutable, mutable, code)
                .with_untrusted(true);
        }

        interp.seed_return_sentinel();
        interp.seed_push(root_closure_word);

        Ok(Self {
            interp,
            _loaded: loaded,
            unresolved,
        })
    }

    /// Run up to `max_steps` bytecode steps (the CLI default is
    /// 5,000,000 — plenty for the standard bootstrap's ~1.11M).
    /// Resumable: after [`RunOutcome::StepBudgetExhausted`], call again
    /// to continue from where execution stopped.
    pub fn run(&mut self, max_steps: u64) -> RunResult {
        let (steps, result) = self.interp.run_until(max_steps);
        let outcome = match result {
            Ok(StepResult::Returned(v)) => RunOutcome::Returned(v),
            Ok(StepResult::Continue) => RunOutcome::StepBudgetExhausted,
            Ok(StepResult::Unimplemented { op, extended }) => {
                RunOutcome::Unimplemented { op, extended }
            }
            Err(e) => RunOutcome::Halted(e),
        };
        // If real threads are enabled (POLY_REAL_THREADS=1) and the root
        // forked children, they must drain before the Session drops (as
        // the CLI does before exiting) — but only on a TERMINAL outcome:
        // a budget-exhausted run is about to resume. No-op on the
        // single-threaded default.
        if !matches!(outcome, RunOutcome::StepBudgetExhausted) {
            self.interp.wait_for_children();
        }
        RunResult { steps, outcome }
    }

    /// Escape hatch: the underlying interpreter, for diagnostics and
    /// advanced drivers.
    #[must_use]
    pub fn interpreter(&self) -> &Interpreter {
        &self.interp
    }

    /// Escape hatch: mutable access to the underlying interpreter.
    pub fn interpreter_mut(&mut self) -> &mut Interpreter {
        &mut self.interp
    }

    /// Entry-point names `patch_entry_points` could not resolve against
    /// the RTS table. A call into one raises an SML exception at run
    /// time rather than failing the load (matching the CLI, which only
    /// reports them).
    #[must_use]
    pub fn unresolved_entry_points(&self) -> &[String] {
        &self.unresolved
    }
}
