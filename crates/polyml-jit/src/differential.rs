//! Differential JIT-vs-interp tester.
//!
//! Given a real code object from a loaded image, runs the function
//! under BOTH the bytecode interpreter and the JIT (assuming a
//! `JitEntry` is installed for it), then compares the return value.
//! Surfaces JIT bugs systematically — much faster than hand-tracing
//! bytecode + IR.
//!
//! ## Setup model
//!
//! The interpreter's "top-level call frame" convention is: push the
//! N args, then a retPC=0 sentinel, then a closure word. When the
//! callee's RETURN_N fires, it pops the result + closure + retPC +
//! N args, sees retPC == 0, and yields `StepResult::Returned(result)`.
//!
//! The JIT's calling convention takes a single `args_ptr` to a
//! `Vec<i64>` of length `arity_init` (= N + 2 + any extra older).
//! Slot[0..N] are args, slot[N] is retPC (0 sentinel), slot[N+1]
//! is the closure pointer. The JIT entry reads these and returns
//! the raw `PolyWord` bits as `i64`.
//!
//! Both modes share the same arg-values input; if they disagree on
//! the result, the JIT translation has a bug at the underlying
//! bytecode level.
//!
//! ## Limitations
//!
//! - Functions that dereference args fail if we pass tagged ints
//!   instead of real heap pointers. The wrapper catches *clean*
//!   errors but a SEGV from invalid deref aborts the process. Use
//!   carefully-chosen inputs.
//! - Allocation-emitting functions diverge in heap state (both modes
//!   allocate, but neither's results need to compare equal unless
//!   we compare the heap too). The bare `==` on results may give
//!   false positives. Consider testing pure functions first.
//! - The closure slot is `0` by default. Functions reading captures
//!   via `INDIRECT_CLOSURE_BN` will deref null. Pass a real closure
//!   via `with_closure`.

use polyml_runtime::{Interpreter, JitEntry, PolyWord, StepResult, with_jit_interp};

/// Result of a single differential run.
#[derive(Debug, Clone)]
pub struct DiffReport {
    pub code_obj_ptr: usize,
    pub sml_arity: usize,
    pub arity_init: usize,
    /// Raw arg values passed to BOTH modes (tagged ints typically,
    /// or PolyWord bits if pointers).
    pub args: Vec<i64>,
    /// Closure word passed in slot[N+1] of args_buf.
    pub closure_word: i64,
    pub jit_result: i64,
    pub interp_result: Option<i64>,
    pub interp_err: Option<String>,
    /// True iff both modes returned a value AND the values are equal.
    pub matches: bool,
    /// First 64 bytes of bytecode (hex), for studying divergences
    /// after the fact.
    pub bytecode_head: String,
}

impl DiffReport {
    pub fn pretty(&self) -> String {
        let mut s = format!(
            "code_obj=0x{:016x} sml_arity={} args=[{}] closure=0x{:016x}",
            self.code_obj_ptr,
            self.sml_arity,
            self.args
                .iter()
                .map(|v| format!("0x{v:016x}"))
                .collect::<Vec<_>>()
                .join(", "),
            self.closure_word,
        );
        s.push_str(&format!("\n  JIT result    = 0x{:016x}", self.jit_result));
        match &self.interp_err {
            Some(e) => s.push_str(&format!("\n  Interp result = ERR: {e}")),
            None => {
                let r = self.interp_result.unwrap_or(0);
                s.push_str(&format!("\n  Interp result = 0x{r:016x}"));
            }
        }
        s.push_str(&format!(
            "\n  Match: {}",
            if self.matches {
                "YES"
            } else {
                "NO — DIFFERENTIAL BUG"
            }
        ));
        s.push_str(&format!("\n  bc[0..64]: {}", self.bytecode_head));
        // If both look like pointers, dump 4 words of pointed-to data.
        let jit_ptr = self.jit_result;
        let interp_ptr = self.interp_result.unwrap_or(0);
        let looks_like_ptr = |p: i64| p != 0 && (p as u64) & 7 == 0 && (p as u64) > 0x1000;
        if looks_like_ptr(jit_ptr) && looks_like_ptr(interp_ptr) {
            unsafe {
                let pj = jit_ptr as *const i64;
                let pi = interp_ptr as *const i64;
                let lwj = pj.sub(1).read_unaligned();
                let lwi = pi.sub(1).read_unaligned();
                let len_j = (lwj as u64 & 0x00ff_ffff_ffff_ffff) as usize;
                let len_i = (lwi as u64 & 0x00ff_ffff_ffff_ffff) as usize;
                s.push_str(&format!(
                    "\n  header: jit=0x{lwj:016x} (len={len_j}) interp=0x{lwi:016x} (len={len_i})",
                ));
                let n = len_j.min(len_i).min(8);
                for k in 0..n {
                    let vj = pj.add(k).read_unaligned();
                    let vi = pi.add(k).read_unaligned();
                    let marker = if vj == vi { "" } else { " <-- DIFF" };
                    s.push_str(&format!(
                        "\n    word[{k}]: jit=0x{vj:016x} interp=0x{vi:016x}{marker}",
                    ));
                }
            }
        }
        s
    }
}

/// Run a single function under both JIT and interpreter, compare.
///
/// `args` must contain exactly `entry.sml_arity` values. The wrapper
/// pads with retPC=0 sentinel + closure word + zeros to reach
/// `entry.arity_init`.
///
/// `interp` must already have:
///   - the same image loaded as the JIT was translated from
///   - the JIT trampoline `JIT_INTERP` thread-local NOT set (we
///     don't want nested-JIT during the interp run)
///
/// # Panics
/// If `args.len() != entry.sml_arity`. The mismatch indicates a
/// caller bug; this isn't something we recover from gracefully.
pub fn diff_function(
    interp: &mut Interpreter,
    entry: &JitEntry,
    code_obj_ptr: usize,
    args: &[i64],
    closure_word: i64,
) -> DiffReport {
    assert_eq!(
        args.len(),
        entry.sml_arity,
        "diff_function: args.len() must equal sml_arity",
    );

    // Run interp FIRST so its step budget protects us from infinite
    // loops. If interp errors quickly (e.g., NotAClosure on a
    // bad-arg deref), SKIP the JIT run — the JIT will likely SEGV
    // on the same input and we can't recover.
    let (interp_result, interp_err) =
        match run_under_interp(interp, code_obj_ptr, entry.sml_arity, args, closure_word) {
            Ok(v) => (Some(v), None),
            Err(e) => (None, Some(e)),
        };
    let jit_result = if interp_err.is_some() {
        // Don't run JIT — likely SEGV.
        0
    } else {
        // Set JIT_INTERP thread-local so trampolines
        // (closure_alloc, alloc_tuple, etc.) can reach back into
        // the interp's alloc_space.
        with_jit_interp(interp, || run_under_jit(entry, args, closure_word))
    };
    // Comparison: if both results are tagged ints (low bit = 1),
    // require exact equality. If both are heap pointers (low bit
    // = 0 and high bits look like a real address), compare the
    // POINTED-TO words — same heap shape = same semantic result,
    // even if absolute addresses differ. If they differ in kind
    // (one tagged, one pointer), that's a real bug.
    let matches = match (jit_result, interp_result.as_ref()) {
        (j, Some(&i)) => compare_results(j, i, entry.sml_arity),
        _ => false,
    };
    // Read the first 64 bytes of bytecode for the report. SAFETY:
    // the JIT entry was installed from a valid code object, so the
    // body memory is accessible.
    let bytecode_head = unsafe {
        let p = code_obj_ptr as *const u8;
        let bytes: Vec<u8> = (0..64).map(|i| *p.add(i)).collect();
        bytes
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<Vec<_>>()
            .join(" ")
    };
    DiffReport {
        code_obj_ptr,
        sml_arity: entry.sml_arity,
        arity_init: entry.arity_init,
        args: args.to_vec(),
        closure_word,
        jit_result,
        interp_result,
        interp_err,
        matches,
        bytecode_head,
    }
}

fn run_under_jit(entry: &JitEntry, args: &[i64], closure_word: i64) -> i64 {
    // Build args_buf to match do_call's layout:
    //   args_buf[0]                 = arg_0 (deepest SML stack pos)
    //   args_buf[arity_init - 2]    = retPC sentinel (= 0)
    //   args_buf[arity_init - 1]    = closure pointer
    // For args.len() == N = sml_arity, arity_init = N + 2 + extra_older.
    let mut args_buf: Vec<i64> = vec![0; entry.arity_init];
    // Older slots stay 0. SML args at args_buf[extra_older..extra_older+N].
    let extra_older = entry.arity_init.saturating_sub(entry.sml_arity + 2);
    for (i, &v) in args.iter().enumerate() {
        args_buf[extra_older + i] = v;
    }
    // retPC sentinel and closure.
    if entry.arity_init >= 2 {
        args_buf[entry.arity_init - 2] = 0;
        args_buf[entry.arity_init - 1] = closure_word;
    }
    // SAFETY: caller-supplied JitEntry registered with matching ABI;
    // args_buf has exactly arity_init slots. The diff tester runs
    // JIT'd code in isolation (no interp stack involved), so we pass
    // sp_in=0 and stack_base=null. Phase-1 generated code ignores
    // both; Phase-2 won't run here because JIT_INTERP isn't set.
    unsafe { (entry.func)(args_buf.as_ptr(), 0, 0) }
}

fn run_under_interp(
    interp: &mut Interpreter,
    code_obj_ptr: usize,
    sml_arity: usize,
    args: &[i64],
    closure_word: i64,
) -> Result<i64, String> {
    interp.reset_stack();
    // Push from-bottom-up: sentinel retPC=0 first (deepest), then
    // args (oldest first), then retPC again as the call retPC, then
    // closure on top. This matches what do_call's caller would leave
    // before transferring control: stack[top] = closure, stack[top+1]
    // = retPC, stack[top+2..top+N+1] = args.
    //
    // For the sentinel, the top-level `do_return` checks retPC==0
    // and yields `Returned`.
    interp.test_seed_return_sentinel();
    for &v in args {
        interp.test_seed_top(PolyWord::from_bits(v as usize));
    }
    // retPC = 0 sentinel: when RETURN fires it pops this as retPC
    // and yields `Returned(result)`.
    interp.test_seed_top(PolyWord::from_bits(0));
    interp.test_seed_top(PolyWord::from_bits(closure_word as usize));
    // SAFETY: caller supplies a valid code-object pointer.
    unsafe {
        interp.set_code_segment_to_code_obj(code_obj_ptr);
    }
    let _ = sml_arity; // currently unused; kept for symmetry with JIT path
    // Run with a step budget so a runaway interp run doesn't hang
    // the tester. 10M steps is generous for any reasonable function.
    const STEP_BUDGET: u64 = 10_000_000;
    let mut steps = 0u64;
    loop {
        steps += 1;
        if steps > STEP_BUDGET {
            return Err(format!("interp exceeded {STEP_BUDGET} step budget"));
        }
        match interp.step() {
            Ok(StepResult::Continue) => continue,
            Ok(StepResult::Returned(v)) => return Ok(v.0 as i64),
            Ok(other) => return Err(format!("unexpected step result: {other:?}")),
            Err(e) => return Err(format!("interp error: {e:?}")),
        }
    }
}

/// Compare two PolyWord-bits results semantically.
///
/// - Both low-bit = 1 (tagged ints): exact equality.
/// - Both pointers (low bit = 0, look like real addresses): compare
///   the first few words of pointed-to data. Same shape = same
///   semantic result, even if absolute addresses differ (which they
///   will when both modes allocate fresh objects).
/// - Mixed (one tagged, one ptr): definitely a bug.
///
/// `_arity` is reserved for future heuristics about how deeply to
/// compare. For now, we compare the first 4 words of any heap data.
fn compare_results(jit: i64, interp: i64, _arity: usize) -> bool {
    let jit_tagged = jit & 1 == 1;
    let interp_tagged = interp & 1 == 1;
    if jit_tagged && interp_tagged {
        return jit == interp;
    }
    if jit_tagged != interp_tagged {
        return false; // tagged-vs-pointer mismatch
    }
    // Both are pointers. Sanity check: low 3 bits are zero (word
    // alignment) and the address looks heap-ish.
    if jit == 0 || interp == 0 {
        return jit == interp;
    }
    if (jit as u64) & 7 != 0 || (interp as u64) & 7 != 0 {
        return false; // mis-aligned pointer
    }
    // Read each object's length word (header at body - 8) to know
    // how many words of body to compare. SAFETY: heap objects are
    // preceded by their length word per PolyML's layout.
    unsafe {
        let pj = jit as *const i64;
        let pi = interp as *const i64;
        let lwj = pj.sub(1).read_unaligned();
        let lwi = pi.sub(1).read_unaligned();
        let len_j = (lwj as u64 & 0x00ff_ffff_ffff_ffff) as usize;
        let len_i = (lwi as u64 & 0x00ff_ffff_ffff_ffff) as usize;
        if len_j != len_i {
            return false; // different-sized objects
        }
        // Compare each body word. Recurse only one level: if a slot
        // is itself a pointer that differs in address, dereference
        // and compare those too. For now, just compare slot values;
        // capture values that are pointers may differ in absolute
        // address but the closure's CONTENT is what we care about.
        for k in 0..len_j {
            let vj = pj.add(k).read_unaligned();
            let vi = pi.add(k).read_unaligned();
            if vj != vi {
                // Same recent-alloc handling as before.
                let both_look_like_recent_alloc =
                    (vj as u64) & 7 == 0 && (vi as u64) & 7 == 0 && vj != 0 && vi != 0;
                if !both_look_like_recent_alloc {
                    return false;
                }
            }
        }
    }
    true
}

/// Tag an i64 as a PolyML tagged integer (low bit = 1).
pub fn tag(n: i64) -> i64 {
    (n << 1) | 1
}

/// Untag a PolyML tagged integer. Panics if low bit isn't 1.
pub fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged int, got 0x{t:016x}");
    t >> 1
}
