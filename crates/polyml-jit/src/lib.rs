//! Cranelift-backed JIT for PolyML bytecode.
//!
//! Status: proof-of-concept stub. We compile one toy function
//! (`compile_identity`) to native code and call it from Rust to
//! prove the Cranelift build + JIT plumbing works in this
//! workspace. Real bytecode-to-IR translation comes next.
//!
//! ## Long-term plan
//!
//! - Each PolyML `Closure { code_addr }` will get a JIT'd entry
//!   point computed from the underlying code object's bytecode.
//! - The interpreter dispatches CALL into a JIT'd function by
//!   looking the closure's code pointer up in a JIT cache.
//! - Inside JIT'd code, opcodes we haven't yet translated trampoline
//!   back to the interpreter (one entry per uncompiled opcode).
//! - JIT'd code shares the same `Interpreter::stack` array as the
//!   interpreter for now; later we can spill registers more
//!   aggressively.

#![allow(clippy::missing_safety_doc)]

pub mod translate;

#[cfg(test)]
mod bench;

/// Trampoline that JIT'd code calls to dispatch CALL_FAST_RTS<N>.
/// Signature must match what `translate.rs` declares for the
/// extern symbol — `(stub: i64, n_args: i64, args: *const i64)
/// -> i64`. For now this is a placeholder that returns TAGGED(0);
/// real interpreter dispatch needs RTS-table access (a thread-local
/// or context pointer threaded through).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rts_trampoline(
    _stub_word: i64,
    _n_args: i64,
    _args: *const i64,
) -> i64 {
    // Tagged(0). Once we wire up Interpreter::rts_call this becomes
    // the dispatch entry; for the moment any JIT'd RTS call returns
    // unit, which compiles cleanly even if it'd execute wrong.
    1
}

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use thiserror::Error;

/// Errors from constructing or running a JIT compilation.
#[derive(Debug, Error)]
pub enum JitError {
    #[error("cranelift settings: {0}")]
    Settings(String),
    #[error("ISA construction failed: {0}")]
    Isa(String),
    #[error("module operation failed: {0}")]
    Module(String),
}

/// A live JIT environment. Owns the Cranelift module that holds
/// compiled functions — drop it and the JITted memory is freed.
pub struct Jit {
    pub(crate) module: JITModule,
    /// Monotonic counter so each compile gets a unique symbol name.
    next_id: u64,
}

impl Jit {
    /// Build a default native-target JIT environment.
    pub fn new() -> Result<Self, JitError> {
        let mut flags = settings::builder();
        flags
            .set("opt_level", "speed")
            .map_err(|e| JitError::Settings(e.to_string()))?;
        let isa_builder = cranelift_native::builder()
            .map_err(|e| JitError::Isa(e.to_string()))?;
        let isa = isa_builder
            .finish(settings::Flags::new(flags))
            .map_err(|e| JitError::Isa(e.to_string()))?;
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // Register the RTS-call trampoline so JIT'd code can call back
        // into Rust for any opcode that needs interpreter state.
        builder.symbol("polyml_jit_rts_trampoline", rts_trampoline as *const u8);
        Ok(Self {
            module: JITModule::new(builder),
            next_id: 0,
        })
    }

    pub(crate) fn fresh_name(&mut self, prefix: &str) -> String {
        let id = self.next_id;
        self.next_id += 1;
        format!("{prefix}_{id}")
    }

    /// Compile a toy "double the tagged int" function and return a
    /// pointer to its native entry point. Signature: `fn(i64) -> i64`.
    ///
    /// The function reads the high 63 bits of `x` (which is the
    /// PolyWord representation of a tagged int `n` as `2n+1`),
    /// extracts `n` via arithmetic shift right by 1, doubles it,
    /// then re-tags. This mirrors the operation `n -> 2n` on the
    /// SML-level int while preserving the tagged-bit invariant.
    pub fn compile_double(&mut self) -> Result<extern "C" fn(i64) -> i64, JitError> {
        let mut ctx = self.module.make_context();
        let mut func_builder_ctx = FunctionBuilderContext::new();
        let int = types::I64;
        // Signature: fn(i64) -> i64
        ctx.func.signature.params.push(AbiParam::new(int));
        ctx.func.signature.returns.push(AbiParam::new(int));

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_builder_ctx);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.seal_block(block);

            let x = builder.block_params(block)[0];
            // n = (x - 1) >> 1   (tagged int is 2n+1)
            let one = builder.ins().iconst(int, 1);
            let x_minus_1 = builder.ins().isub(x, one);
            let n = builder.ins().sshr_imm(x_minus_1, 1);
            // doubled = n + n
            let doubled = builder.ins().iadd(n, n);
            // re-tag: 2*doubled + 1
            let two = builder.ins().iconst(int, 2);
            let shifted = builder.ins().imul(doubled, two);
            let tagged = builder.ins().iadd(shifted, one);
            builder.ins().return_(&[tagged]);

            builder.finalize();
        }

        let name = self.fresh_name("polyml_jit_double");
        let func_id = self
            .module
            .declare_function(&name, Linkage::Export, &ctx.func.signature)
            .map_err(|e| JitError::Module(e.to_string()))?;
        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::Module(e.to_string()))?;
        self.module.clear_context(&mut ctx);
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::Module(e.to_string()))?;

        let code_ptr = self.module.get_finalized_function(func_id);
        // SAFETY: We just compiled this function with the matching
        // signature `fn(i64) -> i64`. The JIT memory remains valid
        // as long as `self.module` does.
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };
        Ok(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cranelift_compiles_and_runs_toy_function() {
        let mut jit = Jit::new().expect("jit init");
        let f = jit.compile_double().expect("compile");
        // PolyWord tagging: n is stored as 2n+1.
        //   tag(3)  = 7
        //   tag(6)  = 13
        let tagged_3: i64 = 2 * 3 + 1;
        let tagged_6: i64 = 2 * 6 + 1;
        assert_eq!(f(tagged_3), tagged_6, "double of tagged 3 should be tagged 6");

        let tagged_neg1: i64 = 2 * (-1) + 1; // = -1
        let tagged_neg2: i64 = 2 * (-2) + 1; // = -3
        assert_eq!(f(tagged_neg1), tagged_neg2);
    }

    #[test]
    fn jit_handle_can_compile_multiple_independent_functions() {
        // The same Jit can produce more than one function. (Real
        // bytecode→native translation will rely on this — each
        // PolyML code object becomes one Cranelift function.)
        let mut jit = Jit::new().expect("jit init");
        let f1 = jit.compile_double().expect("compile #1");
        let f2 = jit.compile_double().expect("compile #2");
        assert_eq!(f1(2 * 4 + 1), 2 * 8 + 1);
        assert_eq!(f2(2 * 5 + 1), 2 * 10 + 1);
    }
}
