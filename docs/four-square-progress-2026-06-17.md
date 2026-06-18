# Lagrange's four-square theorem — progress (2026-06-17)

Staged ultracode campaign (wf_abb7c4f3-0ba) toward
`⊢ ∀n. ∃a b c d. n = a²+b²+c²+d²` on the Isabelle/Pure interpreter. The full
theorem is **NOT yet proved**; the graceful floor banked two genuine 0-hyp
results, with the two number-theoretic cruxes cleanly scoped below.

`four_sq k := ∃a b c d. k = a·a+b·b+c·c+d·d` — an object existential over the
established `oeq`/`add`/`mult`, **not** an axiom. `prime2` = the genuine
structural prime. Base = the self-contained two-square monolith (Thue pigeonhole
+ Wilson/QR + `cong` + the absdiff/ring decision procedure); 67 conservative
axioms, 0 added by any four-square delta; only classical assumption = excluded
middle.

## Proved + banked (regression-fenced)

`crates/polyml-bin/tests/isabelle_support/isabelle_four_square.sml` (run directly;
test `isabelle_four_square.rs`):

- **PART A — `four_sq_mult`** (Euler's four-square identity / multiplicativity):
  `⊢ four_sq m ⟹ four_sq n ⟹ four_sq (m·n)`. 0-hyp, aconv, two soundness probes
  (`PROBE_CONDITIONAL`, `PROBE_PRODUCT`). Marker `L4_IDENTITY_ALL_OK`. The product
  of two sums of four squares is a sum of four squares; proved by a ring-over-ℕ
  decision procedure (`proveStarFor`/`proveIdentityG`) with absdiff handling the
  signed cross terms `w,x,y,z`.
- **ASSEMBLY — `lagrange_assembly`** (multiplicative-closure reduction):
  `⊢ (⋀p. prime2 p ⟹ four_sq p) ⟹ (⋀n. four_sq n)`. 0-hyp, aconv, conditional
  probe. Marker `L4_ASM_ALL_OK`. Via `prime_cases` + `strong_induct` +
  `four_sq_mult` + the `four_sq{0,1,2}` base cases + a cofactor/bound lemma. The
  prime hypothesis is NOT discharged.

## Also proved (resume material, not separately fenced)

`tests/isabelle_support/four_square_resume/` (`base.sml` + the deltas):

- **PART B back-end — `pm_from_cong`**:
  `⊢ cong p N 0 ⟹ 0<N ⟹ N<p·p ⟹ four_sq N ⟹ ∃m. 0<m ∧ m<p ∧ four_sq (m·p)`
  (+ `pm_bridge`, `cong_zero_imp_dvd`). All 0-hyp, aconv.
- **PART C front-end — `sym_residue_thm`**
  (`⊢ 0<m ⟹ ∃a'. cong m (a'·a') (a·a) ∧ a'+a' ≤ m`, the symmetric residue lemma —
  the distinctive heart of the descent) **+ `four_residue_sum_thm`**
  (the `m·r` decomposition with all four `2x'≤m` bounds) + `cong_zero_imp_mult`.
  All 0-hyp, aconv.

## What is left (the two open cruxes — both number-theoretic, not scaffolding)

### (1) PART B FRONT-END — the residue-set pigeonhole
For an odd prime p, prove `∃a b. cong p (a·a + b·b + 1) 0`. The two sets
`{a² mod p : 0≤a≤(p−1)/2}` and `{(p−1)−b² mod p : 0≤b≤(p−1)/2}` each have
`(p+1)/2` elements in `[0,p)`, so `(p+1)/2 + (p+1)/2 = p+1 > p` ⟹ by pigeonhole
they intersect. This is **structurally the same image-collision pigeonhole already
built for Thue** (`dup_gridres` / `list_pigeonhole` in `isabelle_thue.sml`) — reuse
it on a residue list of `a²` and of `(p−1)−b²`. Then feed `N := a·a+b·b+1` into the
**proven** `pm_from_cong` (discharge `0<N` trivially, `N<p·p` from `a,b≤(p−1)/2`,
the `four_sq N` witness `a²+b²+1²+0²` via `four_sq_witness`) ⟹ for an odd prime p,
`∃m. 0<m ∧ m<p ∧ four_sq(m·p)`.

### (2) PART C DESCENT STEP — `prime2 p ⟹ 1<m ⟹ m<p ⟹ four_sq(m·p) ⟹ ∃m2. 1≤m2<m ∧ four_sq(m2·p)`
From the **proven** `four_residue_sum` (gives `a',b',c',d',r` with
`a'²+b'²+c'²+d'² = m·r` and all `2x'≤m`):
- (a) **r=0 exclusion**: `a'²+…+d'²=0` ⟹ `m | a,b,c,d` ⟹ `m² | m·p` ⟹ `m | p`,
  contradicting `1<m<p` prime.
- (b) **r<m**: from `2x'≤m`, `4·(a'²+…+d'²) ≤ 4m²` ⟹ `a'²+…+d'² ≤ m²` ⟹ `m·r ≤ m²`
  ⟹ `r≤m`; exclude `r=m` (forces all `x'=m/2`, the m-even sub-case) ⟹ `r<m`.
- (c) **the expensive step**: apply the Euler identity `proveStarFor` to
  `(m·p)·(m·r) = w²+x²+y²+z²`, show `m | w,x,y,z` from the cross-term structure,
  divide through by `m²` (via `proveIdentityG` bookkeeping) ⟹
  `r·p = (w/m)²+(x/m)²+(y/m)²+(z/m)² = four_sq(r·p)`. (`proveStarFor` on real
  witnesses is ~13 min compute — the genuinely large piece.)

Then iterate the descent to `m=1` (`four_sq p`, every prime), discharge
`lagrange_assembly`'s prime hypothesis, and conclude `∀n. four_sq n`.

## Suggested next workflow

Two independent prove-phases on `four_square_resume/base.sml` + the proven deltas:
seat 1 = PART B front-end (reuse the Thue pigeonhole), seat 2 = PART C descent
step (the residue r-range + the Euler-divide-by-m²). When both land, a short
assembly seat iterates the descent and discharges the assembly. Budget the descent
seat generously (the `proveStarFor` step is minutes per invocation).
