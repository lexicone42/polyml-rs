# Bertrand's postulate — proof artifacts

This directory holds the full proof of **Bertrand's postulate** — for every n ≥ 1
there is a prime p with n < p ≤ 2n — in Isabelle/Pure, run on the polyml-rs
interpreter by genuine LCF kernel inference (Erdős's proof).

```
bertrand : ⊢ ∀n. lt 0 n ⟹ ∃p. prime2 p ∧ lt n p ∧ le p (add n n)
```

0-hypothesis (`hyps_of = []` and `extra_shyps = []`); the conclusion asserts a
**structural** prime (`prime2`) strictly greater than n and at most 2n (range-probed,
not weakened); the only classical assumption is `ex_middle`; the proof introduces no
prime-existence / Bertrand / SEB / inequality axiom (audited by name). Fenced +
reproducible by `crates/polyml-bin/tests/isabelle_bertrand.rs` (`#[ignore]`).

## Reproduce

```sh
tools/build-isabelle-pure.sh     # -> /tmp/isabelle_pure (one-time)
cargo test --release -p polyml-bin --test isabelle_bertrand -- --ignored --nocapture
```

The test concatenates the seven committed pieces below (stripping the trailing
`OS.Process.exit` from the five intermediate appendices) into one self-contained
driver and runs it on `/tmp/isabelle_pure`. HEAVY: ~224 billion bytecode steps,
~25–35 min, **12 GB heap** (`POLYML_HEAP_BYTES=12000000000` — `prime2 631`'s unary
trial-division thrashes a 6 GB heap). The driver ends with `BERTRAND_PROVED` +
`BERTRAND_FINAL_AXIOM_AUDIT total=68 classical=1 ... suspicious=0`.

## The seven pieces (concatenate IN ORDER)

1. **`bertrand_f7_full.sml`** — the Erdős central-binomial machinery: `cb_lower`
   (4^n ≤ (2n+1)·C(2n,n)), `cb_refined` (the 4^(2n/3) refinement under "no prime in
   (n,2n]"), `threshold_assembled`, the primorial bound ∏_{p≤n}p ≤ 4^n, the p-adic
   valuation (Legendre), the FTA prime-power factorization. The final context `ctxtV4`.
2. **`bertrand_w1_appendix.sml`** — `bertrand_large_given_seb` : `SEB_HYP n ⟹ le 513 n
   ⟹ ∃ prime in (n,2n]` (the threshold contradiction: assuming no prime, the assembled
   inequality 4^n ≤ (2n+1)·(2n)^(s+1)·4^(2n/3) collides with SEB → False); + `seb_reduce`.
3. **`w1_crude_appendix.sml`** — `seb_tail_reduce` (((s+1)²)^(s+2) < 4^D from a bit-bound
   + a small exponent comparison) + a `bitlen` function (2 conservative recursion eqns).
4. **`w1_pow_poly_appendix.sml`** — `crude_tail` : SEB for **all s ≥ 36**, with no
   windows and no real-log layer, via the fixed exponent `b = ⌊(s+9)/4⌋` and a
   polynomial-vs-exponential induction (`Pc : (4c+39)² ≤ 2^(c+11)`; numeral-light base
   case `39² ≤ 2^11` via the `64·32 → 273≤800` factorization) + the analytic core
   `s²−33s−74 > 0`.
5. **`bertrand_ch_appendix.sml`** — `bertrand_chain` : a prime in (n,2n] for **all
   n < 631**, exhibited by the doubling chain {2,3,5,7,13,23,43,83,163,317,631} (each
   `prime2` PROVED via the sqrt-bounded `prime2_via_check`, with `Proofterm.proofs := 0`
   to bound RAM — the kernel still type-checks every inference).
6. **`bertrand_jewel_appendix.sml`** — the fat-margin **s=35 case** (`1296^37 < 4^⌊n/3⌋`
   via `seb_tail_reduce` + `1296 ≤ 2^11` + `407 < 2⌊n/3⌋`) → `seb_full_tail` (SEB for all
   n ≥ 631, combining the s=35 case with `crude_tail` for s ≥ 36) → `bertrand_large` (n ≥
   631) → `bertrand_given_chain` : `[bertrand_chain] ⟹ bertrand`.
7. **`bertrand_full_discharge_appendix.sml`** — feed the real proved `bertrand_chain`
   into `bertrand_given_chain` (`implies_elim`) to obtain the UNCONDITIONAL `bertrand`.

## Campaign note (honest history)

The proof was built across a long multi-fleet campaign whose later half was, for the
*final theorem*, a detour: a binary-numeral subsystem (`bnat` with a proved iso) was
built to crack three "window" comparisons at s ∈ {32,33,34} — but once the small-n
chain reached 631 and `crude_tail` covered s ≥ 36, those windows turned out to be
redundant (their range [516,612] ⊂ the chain's [1,630]), and the lone genuine residual
(s=35) has a 37-bit margin and needs no binary computation. The `bnat` machinery
(banked in this directory's gitignored scratch) is sound, reusable
binary-arithmetic-in-the-LCF-kernel infrastructure, but the committed proof above uses
none of it. The real analytic content is `crude_tail` (the fixed-exponent W1 route).
