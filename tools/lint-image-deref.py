#!/usr/bin/env python3
"""Mechanical lint for the COMPLETE image-controlled-operand deref surface
(task #96 — the untrusted-image type-confusion residual).

Run:  uv run python3 tools/lint-image-deref.py
Exit: 0 = clean (no un-gated image-operand derefs), 1 = un-gated deref(s) found.

This is the COMPLETENESS ORACLE for the --untrusted safe mode and a permanent
regression guard: it statically enumerates every place where an image-controlled
operand (a) is read off the PC code-stream, (b) is dereferenced as an RTS
free-function argument, or (c) is laundered into the object-graph export walk,
and flags any that is NOT behind an untrusted gate / a hardened helper.

The lint recognizes the SANCTIONED FIX IDIOMS and only goes green when they are
adopted:
  * SURFACE 4 (mod.rs PC-relative): a read off `self.pc` is SAFE iff it sits in
    the bounds-checked fetch path (fetch_u8/16/32, pc_offset_signed) OR its
    enclosing fn bounds the address vs `code_start`/`code_end` (check_pc_const_*
    / check_case16_*) OR it is behind `if self.untrusted`.
  * SURFACE 5 (rts.rs reader args): a deref of a PolyWord parameter is SAFE iff
    the fn body routes it through `safe_rts_arg_ptr` or otherwise consults a
    space-membership gate (`safe_spaces` / `contains_with_header` / RtsSafeSpaces).
  * SURFACE 6 (export graph walk): an rts.rs fn handing a PolyWord operand to a
    graph-walk helper (export::snapshot*) is SAFE iff it passes the space
    snapshot (snapshot_gated with safe_spaces).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MOD = ROOT / "crates" / "polyml-runtime" / "src" / "interpreter" / "mod.rs"
RTS = ROOT / "crates" / "polyml-runtime" / "src" / "rts.rs"

DEREF_TOKENS = (
    "read_unaligned",
    ".read()",
    "from_raw_parts",
    "length_word_of",
)

findings = []  # (surface, file, lineno, text)


def lines_of(p):
    return p.read_text().split("\n")


# ----------------------------------------------------------------------------
# Helper: split a Rust source file into top-level `fn` bodies by brace depth.
# Returns list of (name, start_line_idx, end_line_idx, body_lines).
# ----------------------------------------------------------------------------
FN_RE = re.compile(r"\bfn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*[<(]")


def split_functions(lines):
    fns = []
    i = 0
    n = len(lines)
    while i < n:
        m = FN_RE.search(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        # Find the opening brace (could be on a later line for multi-line sigs).
        depth = 0
        started = False
        body = []
        start = i
        j = i
        while j < n:
            l = lines[j]
            for ch in l:
                if ch == "{":
                    depth += 1
                    started = True
                elif ch == "}":
                    depth -= 1
            body.append(l)
            if started and depth == 0:
                break
            j += 1
        fns.append((name, start, j, body))
        i = j + 1
    return fns


def test_region_start(lines):
    for i, l in enumerate(lines):
        if l.strip() == "#[cfg(test)]":
            return i
    return len(lines)


# ============================================================================
# SURFACE 4 — PC-relative code-stream reads (mod.rs)
# ============================================================================
def lint_surface4():
    lines = lines_of(MOD)
    fns = split_functions(lines)

    # The bounds-checked fetch path is recognized SAFE: fetch_u8/16/32 guard
    # `*self.pc` against `self.pc >= self.code_end`; pc_offset_signed bounds the
    # PC vs code_start/code_end.
    SAFE_FETCH = {"fetch_u8", "fetch_u16_le", "fetch_u32_le", "pc_offset_signed",
                  "fetch_i8", "fetch_u16", "fetch_u32"}

    for name, start, end, body in fns:
        if name in SAFE_FETCH:
            continue
        text = "\n".join(body)
        # Does this fn read off self.pc at all (a raw deref, not a bounds compare)?
        touches_pc = "self.pc" in text
        has_raw_deref = any(tok in text for tok in DEREF_TOKENS) or re.search(
            r"\*\s*(table_after|entry|base)\b", text
        )
        if not (touches_pc and has_raw_deref):
            continue
        # SAFE if the fn bounds the address vs code_start/code_end, OR is gated
        # behind `if self.untrusted`, OR calls a check_* bounds helper.
        gated = (
            "self.code_start" in text
            and "self.code_end" in text
        ) or "if self.untrusted" in text or re.search(r"check_(pc_const|case16)\w*", text)
        if gated:
            continue
        # Flag every deref-token line in the body.
        for off, l in enumerate(body):
            ln = start + off + 1
            if any(tok in l for tok in DEREF_TOKENS) or re.search(
                r"\*\s*(table_after|entry|base)\b", l
            ):
                findings.append(("SURFACE4", "mod.rs", ln, l.strip()))


# ============================================================================
# SURFACE 5 — RTS reader free-function args (rts.rs)
# ============================================================================
SIG_PARAM_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*PolyWord")


def lint_surface5():
    lines = lines_of(RTS)
    tstart = test_region_start(lines)
    fns = split_functions(lines)

    # Gate tokens that signal an ACTUAL space-membership check IN THE BODY
    # (deliberately NOT bare `RtsSafeSpaces` / a `safe_spaces:` param, which only
    # appear in the SIGNATURE — a fn that merely *takes* the snapshot but never
    # consults it is NOT gated). The fix idiom is a CALL to one of these.
    SPACE_GATE_TOKENS = (
        "safe_rts_arg_ptr(",
        "contains_with_header(",
        "space_end_of(",
        ".safe_spaces",  # `ctx.safe_spaces.as_ref()` handed to a gate helper
    )

    for name, start, end, body in fns:
        if start >= tstart:  # skip the #[cfg(test)] region
            continue
        sig = body[0]
        # Collect PolyWord params (the image-controlled operands), excluding the
        # thread-id (named `_tid` / `tid`).
        params = [p for p in SIG_PARAM_RE.findall(sig) if p not in ("_tid", "tid", "_")]
        if not params:
            continue
        # The gate must appear in the BODY (drop the signature line(s) up to the
        # opening brace) — a `RtsSafeSpaces` param type does not count.
        brace = next((i for i, l in enumerate(body) if "{" in l), 0)
        body_text = "\n".join(body[brace:])
        text = "\n".join(body)
        # Build the set of pointer locals derived from a param via `.as_ptr` /
        # `.cast` so we can spot the FIRST deref of an operand-derived pointer.
        # Does the fn deref a param (or a ptr derived from it) WITHOUT a gate?
        # We look for the canonical un-gated patterns:
        #   *<param>.as_ptr   |  <param>.as_ptr<...>() then *<local>
        #   length_word_of(<param>...) | length_word_of(<derived ptr>)
        derefs_param = bool(
            re.search(r"\*\s*\w*\.as_ptr::<", text)
            or re.search(r"length_word_of\(", text)
            or re.search(r"\.as_ptr::<\w+>\(\)\s*\}", text)
        )
        if not derefs_param:
            continue
        # SAFE if the body consults a space-membership gate (a CALL, in the body
        # — not merely an RtsSafeSpaces param in the signature).
        gated = any(tok in body_text for tok in SPACE_GATE_TOKENS)
        if gated:
            continue
        # Flag the first deref-bearing line.
        for off, l in enumerate(body):
            ln = start + off + 1
            if re.search(r"\*\s*\w*\.as_ptr::<", l) or "length_word_of(" in l:
                findings.append(("SURFACE5", "rts.rs", ln, f"{name}: {l.strip()}"))
                break


# ============================================================================
# SURFACE 6 — arg laundered through a graph-walk helper (rts.rs -> export)
# ============================================================================
def lint_surface6():
    lines = lines_of(RTS)
    tstart = test_region_start(lines)
    fns = split_functions(lines)
    WALK_HELPERS = ("export::snapshot", "::snapshot(", "walk_graph", "deep_copy")
    for name, start, end, body in fns:
        if start >= tstart:
            continue
        text = "\n".join(body)
        calls_walk = any(h in text for h in WALK_HELPERS)
        if not calls_walk:
            continue
        # SAFE iff it hands the space snapshot to the gated entry point.
        gated = "snapshot_gated" in text and "safe_spaces" in text
        if gated:
            continue
        for off, l in enumerate(body):
            ln = start + off + 1
            if any(h in l for h in WALK_HELPERS):
                findings.append(("SURFACE6", "rts.rs", ln, f"{name}: {l.strip()}"))
                break


# ============================================================================
# SURFACE C — per-opcode gate sentinel (a regression that DROPS the hardened
# `if self.untrusted` gates in mod.rs is visible).
# ============================================================================
def lint_surfaceC():
    lines = lines_of(MOD)
    n = sum(1 for l in lines if "if self.untrusted" in l)
    SENTINEL = 40
    print(f"[SURFACE C] mod.rs `if self.untrusted` gates: {n} (sentinel >= {SENTINEL})")
    if n < SENTINEL:
        findings.append(
            ("SURFACEC", "mod.rs", 0,
             f"per-opcode untrusted gate count dropped to {n} (< {SENTINEL}) — a hardening regression")
        )


def main():
    lint_surface4()
    lint_surface5()
    lint_surface6()
    lint_surfaceC()

    if not findings:
        print("lint-image-deref: CLEAN — 0 un-gated image-controlled-operand "
              "derefs across SURFACE 4 / 5 / 6.")
        return 0

    print(f"\nlint-image-deref: {len(findings)} UN-GATED image-operand deref(s):")
    for surface, fname, ln, text in findings:
        print(f"  [{surface}] {fname}:{ln}  {text}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
