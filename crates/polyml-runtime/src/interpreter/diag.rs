//! Optional execution-profile diagnostics. Enabled per-interpreter
//! via `Interpreter::enable_diagnostics()`. When disabled, the entire
//! cost is one branch per step.
//!
//! Used to figure out *where* bootstrap is spending time when it
//! makes no observable RTS calls — e.g., distinguishing a real
//! allocation-heavy initialization loop from a stuck busy-wait.

use std::collections::HashMap;

/// Per-(code-object, pc-offset) and per-code-object counts gathered
/// during interpretation.
#[derive(Debug)]
pub struct DiagState {
    /// Visit counts keyed by `(code_start_addr, pc_offset)`.
    pub pc_visits: HashMap<(usize, u32), u64>,
    /// CALL count keyed by target code-object address (= what we
    /// jumped INTO via CALL_CLOSURE etc.).
    pub call_targets: HashMap<usize, u64>,
    /// Cumulative count of step()s observed.
    pub total_steps: u64,
    /// Per-opcode dispatch counts. Indexed by opcode byte. Useful for
    /// "which opcodes dominate?" — a hot opcode often points at a
    /// concrete optimization target.
    pub opcode_counts: [u64; 256],
}

impl Default for DiagState {
    fn default() -> Self {
        Self {
            pc_visits: HashMap::new(),
            call_targets: HashMap::new(),
            total_steps: 0,
            opcode_counts: [0; 256],
        }
    }
}

impl DiagState {
    /// Hot-PC report: top-N (code, offset) by visit count.
    /// Returns a vector of `((code_addr, offset), count)`.
    #[must_use]
    pub fn hot_pcs(&self, n: usize) -> Vec<((usize, u32), u64)> {
        let mut v: Vec<_> = self.pc_visits.iter().map(|(k, c)| (*k, *c)).collect();
        v.sort_unstable_by_key(|(_, c)| std::cmp::Reverse(*c));
        v.truncate(n);
        v
    }

    /// Per-code-object summary: total step-count visited in each
    /// code object, top-N by count.
    #[must_use]
    pub fn hot_code_objects(&self, n: usize) -> Vec<(usize, u64)> {
        let mut totals: HashMap<usize, u64> = HashMap::new();
        for ((code, _), c) in &self.pc_visits {
            *totals.entry(*code).or_default() += *c;
        }
        let mut v: Vec<_> = totals.into_iter().collect();
        v.sort_unstable_by_key(|(_, c)| std::cmp::Reverse(*c));
        v.truncate(n);
        v
    }

    /// Top-N call targets (functions entered most often).
    #[must_use]
    pub fn hot_call_targets(&self, n: usize) -> Vec<(usize, u64)> {
        let mut v: Vec<_> = self.call_targets.iter().map(|(k, c)| (*k, *c)).collect();
        v.sort_unstable_by_key(|(_, c)| std::cmp::Reverse(*c));
        v.truncate(n);
        v
    }

    /// Top-N opcodes by dispatch count. Returns (opcode_byte, count).
    #[must_use]
    #[allow(clippy::cast_possible_truncation)]
    pub fn hot_opcodes(&self, n: usize) -> Vec<(u8, u64)> {
        let mut v: Vec<(u8, u64)> = self
            .opcode_counts
            .iter()
            .enumerate()
            .filter(|&(_, &c)| c > 0)
            .map(|(i, &c)| (i as u8, c))
            .collect();
        v.sort_unstable_by_key(|(_, c)| std::cmp::Reverse(*c));
        v.truncate(n);
        v
    }
}
