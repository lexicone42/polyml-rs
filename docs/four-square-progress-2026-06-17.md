# Lagrange's four-square theorem — progress (2026-06-17, updated 2026-06-18, 2026-06-20, 2026-06-22, 2026-06-22b)

Staged ultracode campaign (wf_abb7c4f3-0ba, then wf_d352530c-63b, then
wf_236bdf0c-5cd, then the 2026-06-22 DESCENT-step analysis, then the 2026-06-22b
DIVIDE-leaf session) toward `⊢ ∀n. ∃a b c d. n = a²+b²+c²+d²` on the
Isabelle/Pure interpreter. The full theorem is **NOT yet proved**; the graceful
floor banked genuine 0-hyp results, with the remaining descent step cleanly
scoped below.

## 2026-06-23 UPDATE (divide-leaf fleet) — most of the sign-leaves now proven

A multi-agent fleet ran the remaining divide sign-leaves on the warm
`/tmp/l4_foursq_star` checkpoint, each parameterizing the proven `++++` template
(N coordinates take the RIGHT congruence branch). State now:

- **VERIFIED (independently replayed by a separate agent — hyps=7, the genuine
  `four_sq (p·r)` existential, 0 new axioms, `Tagged(0)`):** `PPPP` (prior),
  `PPPN`, `PPNN`, `PNPP`, `PNPN` — **5 of 8**.
- **Proven but pending independent verification:** `PPNP`, `PNNP`, `PNNN`. Their
  deltas are complete and soundness-clean (self-contained, end-to-end, **no new
  axioms**) and each author-agent recorded "proven", but they fell out of the
  fleet's structured report, so they are being re-replayed by hand to confirm. If
  they hold, **all 8 divide leaves are done.**

Operational notes from the fleet (for the next run): each leaf needs
`POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88`; the 4-pair leaves peak
~28 GB RSS during the divide-by-m² and **must run one-at-a-time** (two concurrent
OOM-kill on a 31 GB machine); ~17–31 min wall each. Deltas:
`tests/isabelle_support/four_square_resume/divide_leaf_<pat>_delta.sml` (gitignored
resume scratch).

**Remaining to close the theorem (fleet 2):** the 16→8 disjE assembly tree
(route each signed-flag combination to its leaf), strict r<m (r=m exclusion),
then strong-induct on m to m=1 (`four_sq p`) and discharge the PROVEN
`lagrange_assembly`.

## 2026-06-22b UPDATE (DIVIDE-leaf session) — the divide PIPELINE PROVEN (one leaf end-to-end); 8-star count CONFIRMED; dev-loop UNBLOCKED

The single biggest de-risking step landed: the **Euler divide-by-m² closes
end-to-end for the uniform-orientation leaf**, and the warm-checkpoint dev-loop
is now real. The full theorem still needs the 7 other sign-leaves + strict r<m +
iteration (genuinely 2 more focused fleets), but the "expensive ring-procedure
step" the prior fleets flagged as the wall is DONE for one leaf, and the
machinery is uniform across all 8.

### LANDED (validated on the real base, not STAR_CHEAP)

- **Phase 0 — WARM CHECKPOINTS + a heap knob (the dev-loop unblock).**
  - `crates/polyml-bin/src/main.rs` now honours `POLYML_HEAP_BYTES` (env override
    of the hardcoded 1.6 GB; `run` subcommand, ~line 342). Run four-square drivers
    at 8 GB: `POLYML_HEAP_BYTES=8000000000`. This is the trivial Rust change the
    2026-06-22 doc demanded; it eliminates the GC death-spiral the prior fleet hit.
  - `/tmp/l4_foursq` (1.4 GB, symlinked into the persistent store): the assembled
    base + `four_sq_mult` (proven, the ONE real ~13-min proveStarFor) +
    `lagrange_assembly` + seat1 `descent_residue`, with `restore_l4_context ()` +
    every helper fn in the exported heap. **Reloads in ~16 s and PROVES** (verified:
    `four_sq_mult`/`descent_residue` hyps=0, `ctermGR`/`sq_diff_inst` work). Every
    divide iteration is now seconds, not 25 min.
  - `/tmp/l4_foursq_star` (2.7 GB): the above PLUS `star_v` — the generic varified
    Euler star (`mn + 2(PxQx+PyQy+PzQz) = w²+(Px²+Qx²)+…` on the eight free atoms),
    banked 0-hyp so it instantiates at ANY concrete witnesses for FREE (no
    proveStarFor). `starFast (a,…,h)` = one `infer_instantiate` of `star_v`.
  - **8-stars-in-ONE-checkpoint does NOT fit** (memory finding this session): a
    build proving `starV_0 … starV_7` in one heap GC-thrashed near a 27 GB RSS
    ceiling (machine has 31 GB) and stalled after **4 stars proven** (PPPP, PPPN,
    PPNP, PPNN — each `hyps=0`, confirming every star polynomial proves correctly);
    the export never ran. The proveIdentityG term graphs accumulate. **FIX for the
    next fleet: build stars in batches of ≤3, or one-per-checkpoint** (a single
    star fits easily — the `starV` (`++++`) checkpoint `/tmp/l4_foursq_star` is
    2.7 GB and builds clean). A lean per-pattern star checkpoint
    (`/tmp/l4_foursq_pppn` with `starV_1`) is built this session to validate the
    mixed leaf. So the ~1.7 hr of star-proving is still required but is now
    pre-scripted (`/tmp/l4_build_8stars_v2.sml` emits all 8; split it).

- **The (++++) DIVIDE LEAF — PROVEN end-to-end** (`divide_leaf_pppp_delta.sml`,
  marker `DIVF_SMOKE hyps=7`, on `/tmp/l4_foursq_star`). For the uniform LEFT
  orientation (`cong m a' a`, …, `cong m d' d`):
    `oeq (m*p) (a²+b²+c²+d²) ⟹ oeq (a'²+b'²+c'²+d'²) (m*r) ⟹
     cong m a' a ⟹ … ⟹ cong m d' d ⟹ lt 0 m ⟹ four_sq (p*r)`.
  The FULL divide pipeline runs: `starFast` (reused star, cheap) → the four
  divisibility congruences `cong m w 0` / `cong m Px Qx` / `cong m Py Qy` /
  `cong m Pz Qz` (uniform cong-algebra, CHEAP, no proveStarFor) → `sq_diff_dvd`
  (the new helper, below) for sx,sy,sz → the multiplicativity assembly
  `(m*p)(m*r) = w²+sx²+sy²+sz²` → `m∣w,sx,sy,sz` → divide by m² (proveIdentityG +
  `mult_left_cancel_r`) → `four_sq_witness`. Runs in ~10 min (the proveIdentityG
  calls inside sq_diff_dvd + the divide), NO 13-min proveStarFor (star reused).

- **`sq_diff_dvd` — the new divisibility-aware square-difference law** (banked in
  `divide_leaf_pppp_delta.sml`): `cong m P Q ⟹ ∃s. (s² + 2PQ = P²+Q²) ∧ cong m s 0`.
  The leaves' key lemma; the absdiff `s=|P−Q|` is divisible by m because
  `P≡Q (mod m)`. (Validated standalone: `SMOKE sq_diff_dvd hyps=1`.)

- **The MIXED-pattern (PPPN) leaf machinery — VALIDATED** (`divide_leaf_pppn_mixed_delta.sml`,
  on `/tmp/l4_foursq_pppn` which banks `starV_1`; markers `DIVPPPN_STAR_SHAPE_OK`,
  `DIVPPPN_CONG_W_OK`, `DIVPPPN_CONG_X_OK`, `DIVPPPN_SQDIFF_W_X hyps_W=5 hyps_X=4`).
  This is the crucial second validation: it proves the RIGHT-branch flag handling
  (`cong m (d'+d) 0`, the `−`-oriented coordinate) works in a mixed pattern. Two
  things the `++++` leaf could not exercise are shown here:
  (1) `w` is now itself an absdiff `|wP−wQ|` (the RIGHT coord puts `d·d'` in the
      negative group); `cong m wP wQ` is proved by the **+correction trick**:
      `cong m (wP+d²)(wQ+d²)` (both ≡ m·p ≡ 0 — `wP+d²≡m·p` via LEFT flags,
      `wQ+d²=d·(d'+d)≡0` via the RIGHT flag) then `cong_radd_cancel`.
  (2) `cong m Px Qx` mixes LEFT and RIGHT terms (`g·d≡c·d`, `c·h+c·d=c·(h+d)≡0`).
  So both the `++++` (proven full leaf) AND a mixed leaf's distinctive congruences
  are validated; the remaining 6 stars/leaves are structurally identical
  permutations (each star a one-shot proveIdentityG; each leaf the same
  sq_diff_dvd + cong + divide-by-m² as the two proven ones).

- **STRICT r<m building blocks — VALIDATED + the delta FIXED**
  (`descent_strict_rltm_delta.sml`). The 2026-06-22 delta had a `let … end`
  WITHOUT an `in` (Static Error "in expected but out was found") and was never
  runtime-validated (heap wall). FIXED to top-level decls; now all blocks validate
  on the warm checkpoint: `L4_RLTM_{GR_ALIASES,SQ_STRICT_MONO,SQ_EQ_IMP_EQ,
  LE_RADD_CANCEL,LE_LADD_CANCEL,TIGHTA}_OK` (smoke: `sq_eq_imp_eq` gives
  `oeq(a²)(b²) ⟹ oeq a b`, hyps=1). The full r=m exclusion ASSEMBLY (consuming the
  four tight equalities → 2x'_i=m → m even → m∣p) is still pending; NOTE the
  m-even/`gcd(m,4)` subtlety (the tight equalities give `m∣2a_i`, not `m∣a_i`).

### THE KEY ALGEBRAIC RE-SCOPING (offline-verified, /tmp/check_*.py, /tmp/*star*.py)

- **The divisibility crux is UNIFORM and CHEAP — but only within a fixed
  orientation.** `cong m e a` (e≡a) makes `w = ae+bf+cg+dh ≡ a²+b²+c²+d² = m·p ≡ 0`
  and `X≡Y≡Z≡0` IDENTICALLY (verified symbolically + 200000 numeric). NO
  proveStarFor, NO sign bookkeeping — pure cong-algebra. This is the new, cheap
  heart of the divide.
- **BUT the sign-vs-bound conflict is REAL and the 8 stars are GENUINELY needed**
  (the 2026-06-22 "PATH A reuses ONE star" optimism was PARTLY wrong). The signed
  flag `cong m a' a ∨ cong m (a'+a) 0` gives PER-COORDINATE orientation. With the
  base's all-positive witness builders (`Px=af+ch`, always added), divisibility
  holds ONLY when all four orientations agree (`++++`/`−−−−`) — verified: mixed
  patterns give e.g. `w ≡ a²+b²+c²−d² ≢ 0`. To fix a mixed coordinate you need the
  TRUE signed value (`−d'`), which is not a ℕ term; the ℕ realization re-groups the
  witness terms into pos/neg parts (`w` becomes `|wP−wQ|` too), giving a DIFFERENT
  all-positive star polynomial per pattern. **Counted exactly: 16 sign patterns →
  8 distinct star shapes** (paired by global negation; `check_star_count.py` lists
  the pairing). The generalized star `mn + 2(wP·wQ+Px·Qx+Py·Qy+Pz·Qz) =
  (wP²+wQ²)+(Px²+Qx²)+(Py²+Qy²)+(Pz²+Qz²)` holds for ALL 16 (`verify_gen_star.py`);
  zero components dropped per pattern (`verify_dropped_stars.py`). So the
  divide is **8 leaves, each structurally identical to the proven `++++` leaf** —
  same `sq_diff_dvd` + uniform-cong + divide-by-m² machinery — differing only in
  the witness groupings + which flag branch (LEFT/RIGHT) feeds each coordinate's
  cong. Each leaf reuses its banked `starV_i` (no fresh proveStarFor).

### REMAINING (precise, the honest map)

1. **The 7 other divide leaves** (`PPPN … PNNN` + their global-negation twins).
   Each: build the pattern's witnesses from `starV_i`, prove the 4 divisibility
   congruences (now with `w` as a 4th `sq_diff_dvd`, and RIGHT-branch flags for the
   `−` coordinates — the RIGHT branch is exactly `sq_cong_from_signed`'s caseR
   pattern), assemble, divide. ~10 min each on the star8 checkpoint. The general
   leaf is a parameterization of the proven `++++` leaf.
2. **The 16→8 disjE assembly tree**: case-split each of the 4 signed flags
   (`disjE_r`), routing each of the 16 combinations to its leaf (8 distinct, via
   the global-negation symmetry the proof is the same up to relabeling).
3. **Strict r<m**: the r=m exclusion assembly (building blocks DONE; the m-even
   subcase needs the `m∣2a ⟹ … ⟹ m∣p` chase, ~6-10 lemmas).
4. **Iterate + discharge**: `strong_induct` on m (from `primemult_thm`'s
   `0<m'<p four_sq(m'·p)`, descend to m=1 ⟹ `four_sq p`), `four_sq 2` trivial,
   ⟹ `(∀p. prime2 p ⟹ four_sq p)` ⟹ discharge the PROVEN `lagrange_assembly` ⟹
   `∀n. four_sq n`.

ARTIFACTS this session: `/tmp/l4_foursq`, `/tmp/l4_foursq_star`,
`/tmp/l4_foursq_star8` (persisted in /var/tmp/polyml-rs); resume deltas
`divide_leaf_pppp_delta.sml` (the proven leaf + `sq_diff_dvd`),
`descent_strict_rltm_delta.sml` (FIXED + validated); the 8-star builder
`/tmp/l4_build_8stars_v2.sml`. The heap knob is the one Rust change.

## 2026-06-22 UPDATE (DESCENT-step analysis) — the deep obstruction RE-DIAGNOSED; PATH A confirmed viable; precise cost mapped

A descent-step session that did NOT close the full theorem (predicted multi-fleet)
but DID correct the prior fleet's verdict and map the divide precisely. All
algebra independently re-verified offline (sympy, /tmp/check_*.py — conjugate
identity, per-tag divisibility over 200000 random cases, r=m exclusion).

- **THE PRIOR "PATH B / signed-integer layer" VERDICT IS WRONG — PATH A (clever-ℕ)
  is viable.** The key refutation: the BANKED `proveStarFor` (partA) IS ALREADY the
  CONJUGATE quaternion Euler star. Its witnesses `w = ae+bf+cg+dh`, `sx = Px−Qx`,
  `sy = Py−Qy`, `sz = Pz−Qz` are EXACTLY the conjugate-product witnesses
  `w, x, y, z` of `(a,b,c,d)·conj(e,f,g,h)` (verified: `sx≡x`, `sy≡y`, `sz≡z`
  identically). When the second quaternion is the residue rep, these reduce mod m
  to `(m·p, 0, 0, 0)` — i.e. **all four are divisible by m**, which is precisely
  what the divide-by-m² needs. The prior "absdiff witnesses' divisibility not
  available" obstruction is FALSE: `m∣k ⟺ m∣|k|` over ℤ and `(|W|/m)² = (W/m)²`,
  so the absolute-value (absdiff) witnesses are exactly usable.

- **THE SIGN-VS-BOUND CONFLICT IS REAL BUT LOCAL (to nat-magnitude feeding).** The
  prior fleet's `w ≡ ±a²±b²±c²±d²` finding is correct ONLY when the witnesses are
  fed the unsigned MAGNITUDES (then divisibility holds only for the uniform tag).
  The resolution: the two banked `sym_residue_signed` branches `cong m a' a` /
  `cong m (a'+a) 0` are **NOT per-coordinate orientation flips** — they BOTH encode
  the UNIFORM orientation `b ≡ a (mod m)`, differing only in whether the signed
  representative `b` is `+a'` or `−a'` (magnitude `a'` ≤ m/2). With `b_i ≡ a_i`
  uniformly, ALL four signed witnesses `≡ 0 (mod m)` for EVERY tag (verified, all
  16 patterns + 200000 random numeric cases). So divisibility is UNIFORM and
  flag-driven (cong algebra, cheap, NO proveStarFor). The signed small rep
  (|b|≤m/2) is also MATHEMATICALLY NECESSARY for `r<m`: the `[0,m)` positive rep
  gives only `r<4m`. So the per-coordinate sign tag is intrinsic — but it needs NO
  integer layer.

- **THE GENUINE COST (precise, the divide):** the IDENTITY
  `(m·p)·(m·r) = sw²+sx²+sy²+sz²` with the SIGNED witnesses depends on the tag
  pattern (which magnitude-product lands in the Pos vs Neg group of each absdiff).
  These collapse to **8 distinct all-positive star shapes** (16 tags, ×2 symmetry).
  One varified star can NOT cover all tags by ℕ-instantiation (the sign can't be
  absorbed into ℕ args — definitively checked). So the divide needs **up to 8
  `proveStarFor` runs (~13 min each ≈ 1.7 hr compute)** for the 8 tag-shape
  identities, PLUS the (cheap, uniform) divisibility cong-chase, PLUS the per-leaf
  absdiff assembly (a nested 4-coordinate disjE tree, 16 leaves), PLUS the
  divide-by-m². This is the genuinely large remaining piece — a multi-fleet effort,
  but with banked machinery (no from-scratch abstraction).

- **STRICT r<m — fully analysed, building blocks banked.** `r=m` NEVER occurs for
  prime p (verified: 0/200000 cases), precisely because it forces `m∣p`. The route
  (no proveStarFor): `r=m` ⟹ `4·sum = Σ(2x'_i)² = 4m²` with each `(2x'_i)²≤m²` ⟹
  each `2x'_i = m` (tightness + `sq_eq_imp_eq`) ⟹ `m = 2·x'_i` (so m even,
  `k:=x'_i`) ⟹ `a_i ≡ x'_i (mod m)` uniformly (flag, since `2x'_i=m` makes
  `x'_i ≡ −x'_i`) ⟹ `a_i = x'_i + m·s_i` ⟹ `m·p = Σ a_i²` collapses to `m·(…)` ⟹
  `m∣p` ⟹ banked `m_dvd_p_contra`. The 2026-06-22 delta
  (`descent_strict_rltm_delta.sml`) banks the verified building blocks
  `sq_strict_mono`, `sq_eq_imp_eq`, `le_radd_cancel`/`le_ladd_cancel`,
  `tightA` (four-term tightness), and the GR aliases `le_eq_or_lt_d` /
  `add_left_cancel_d` / `add_right_cancel_d`. The full `r=m`-exclusion assembly
  (consuming the 4 tight equalities + the cong/dvd chase to `m∣p`) is scoped but
  the descent-fleet dev-loop wall (below) prevented blind completion this session.

- **DEV-LOOP IS HEAP-BOUND, NOT JUST TIME-BOUND (sharp new finding, 2026-06-22, two
  runs).** The default 1.6 GB poly heap (`with_default_alloc_space_bytes(1_600*1024*1024)`
  at `crates/polyml-bin/src/main.rs:349`, **hardcoded, NO env override**) is too small
  to load `_assembled_base.sml` + `seat1_descent_residue_delta.sml` + anything more.
  - RUN 1 (base+seat1+`rltm` delta): validated `four_sq_mult` (`L4_IDENTITY_ALL_OK`,
    0-hyp, aconv) and `lagrange_assembly` (`L4_ASM_ALL_OK`, 0-hyp), reached seat1, then
    hit a **100%-retained GC death-spiral at seat1's `r_le_m` SMOKE test** (stack frozen
    ~700, no marker advance) — the `rltm` GR-alias `varify`s (`le_eq_or_lt`/
    `add_left_cancel` schematic theorems) tipped it over.
  - RUN 2 (base+seat1+export ONLY, no rltm): again validated `four_sq_mult` +
    `lagrange_assembly`, but **`lagrange_assembly` itself thrashed** — live words pinned
    at a STATIC 163.1M / 97% retained for ~6 min with literally zero net progress (GC
    reclaims ~20 words/cycle, instantly refilled), a SOFT heap wall. It never reached
    seat1 OR the export.
  **CONCLUSION: base + `four_sq_mult` + `lagrange_assembly` ALONE saturates the 1.6 GB
  heap to the thrash point**, so the warm-checkpoint export CANNOT be produced on the
  current hardcoded heap, and the divide fleet CANNOT keep appending. **The next fleet's
  Phase 0 MUST first add a heap knob** (a `poly run --max-heap N` / `POLYML_HEAP_BYTES`
  env, threading `with_default_alloc_space_bytes` — trivial Rust change at main.rs:349/778)
  and run at e.g. 6–8 GB; THEN export a lean warm checkpoint (keep only
  `four_sq_mult`/`lagrange_assembly`/`descent_residue` + GR context, drop seat1's
  intermediate smoke terms) and iterate the divide on the reloaded image. Without the heap
  bump, every four-square run is both ~25 min AND heap-starved. (The prior fleet banked
  `descent_residue` as a STANDALONE seat — likely with STAR_CHEAP or a trimmed base — not
  stacked on the real `four_sq_mult`+`lagrange_assembly`, explaining how it fit.)
- **DEV-LOOP: a WARM checkpoint is the unblock (Phase 0).**
  STAR_CHEAP is a dead end (captures exE eigenvariables). The fix is exporting
  a warm four-square image (`/tmp/l4_foursq`) AFTER `four_sq_mult` is proven, via
  `PolyML.export(target, PolyML.rootFunction)` capturing `Context.the_generic_context()`
  as `L4_context` + a `restore_l4_context ()` thunk (mirrors build-isabelle-pure.sh);
  the proven theorem vals (`four_sq_mult`/`lagrange_assembly`/`descent_residue`) and
  the helper fns survive in the exported heap. Reloaders call `restore_l4_context ()`
  first, then iterate the divide delta in seconds instead of ~25 min. This makes the
  8-star divide fleet practical. NB the heap finding above: export BEFORE seat1's
  smoke-heavy tail if possible, or with a bumped heap, so the export itself fits.
  (The all-POS `++++` divide leaf is ONE plain star
  instantiation — testable first on the warm image as the divide template.)

- **RECOMMENDED next fleet (concrete):** (Phase 0) bank `/tmp/l4_foursq`. (Phase 1)
  finish strict `r<m` on the warm image (cheap, building blocks banked). (Phase 2)
  the divide: prove the `++++` leaf end-to-end (1 star + uniform divisibility +
  divide-by-m²) as the template, then the remaining 7 tag-shape stars + the 16-leaf
  assembly tree. (Phase 3) strong-induct on m to m=1 (`four_sq p`), discharge the
  PROVEN `lagrange_assembly`. The proveStarFor calls are INSIDE descent_step's proof
  (run once when the lemma is proved), NOT per induction step.

## 2026-06-20 UPDATE (descent workflow wf_236bdf0c-5cd) — descent SETUP banked; the deep obstruction ROOT-CAUSED

A third fleet (3 descent seats raced + an independent verifier) banked one more
genuine increment AND — the real prize — root-caused exactly why the descent
resists the ℕ formalization. The full theorem did NOT close (predicted).

- **BANKED + VERIFIED (re-run from scratch to Tagged(0), 0-hyp, aconv, axiom-clean):**
  `descent_residue` (seat1, resume `seat1_descent_residue_delta.sml`, 900 lines,
  ZERO add_axiom_global — pure derivation, does NOT use proveStarFor):
  `⊢ prime2 p ⟹ 1<m ⟹ m<p ⟹ four_sq(m·p) ⟹ ∃r. 0<r ∧ r≤m ∧ four_sq(m·r)`.
  This is the descent **SETUP** (stages a/b/c: signed four_residue_sum + r=0
  exclusion + the AM `r≤m` bound) — NOT the descent **STEP**: `r≤m` is
  NON-STRICT, so it cannot start strong induction (needs strict `r<m` + the divide
  to `four_sq(r·p)`). A second pure-derivation variant is banked as
  `seat3_descent_ab_delta.sml`; a 3-square-rejection soundness probe as
  `three_square_rejection_probe.sml` (7 = 2²+1²+1²+1² is provable; 7 is NOT a sum
  of three squares — so the `∀n. ∃a b c d` form is genuinely non-collapsible).

- **THE DEEP OBSTRUCTION (independently re-derived by two agents — the key finding).**
  With the flag-form signed residues (per-coordinate independent signs, `a'≡a OR
  a'≡−a (mod m)`), the Euler witness `W = a·a'+b·b'+c·c'+d·d' ≡ ±a²±b²±c²±d² (mod m)`
  is `≡0` **only when all four signs agree**. Aligning the signs (replace `a'` by
  `m−a'`) restores the divisibility `m∣W` needed for the divide-by-m² — but
  DESTROYS the `2x'≤m` bound that gives `r<m`. **This bound-vs-sign conflict is
  irreducible in the ℕ flag-encoding.** The textbook ℤ proof escapes it via a
  single signed representative in `(−m/2, m/2]`. So closing the descent needs a
  from-scratch **signed Euler identity over ℕ** (or a thin signed-integer layer)
  that tracks per-coordinate divisibility — a dedicated multi-phase fleet, exactly
  as Thue's lemma and the two-square crown jewel each took 2–3 fleets.

- **DEV-LOOP BLOCKER (force-multiplier for the next fleet — fix FIRST).** The
  cheap-iteration path is BROKEN: `L4_STAR_CHEAP=1` makes `star_i = Thm.assume(...)`,
  which CAPTURES the exE eigenvariables (`nd_w`) → "forall_intr: variable nd_w free
  in assumptions" → four_sq_mult undeclared → Static Errors. So EVERY descent test
  currently needs the full ~25-min real base run (one real proveStarFor in PART A).
  **Phase 0 of any descent fleet must be:** bank a WARM four-square checkpoint
  (export `thyGR`/`ctxtGR` post-`four_sq_mult`) OR repair STAR_CHEAP to not capture
  eigenvariables — otherwise debugging the signed divide is impractical.

- **Remaining (precise):** (1) strict `r<m` (the `r=m` exclusion — tractable,
  ~6–10 lemmas: equal-share + sqrt-on-bound + Euclid's lemma); (2) THE SIGNED EULER
  DIVIDE-BY-m² over ℕ (large — needs the signed identity above). Then iterate the
  descent to m=1 (`four_sq p`) and discharge the proven `lagrange_assembly`.

## 2026-06-18 UPDATE (descent workflow wf_d352530c-63b) — Part B DONE, Part C keystone DONE

The descent workflow advanced the two cruxes and landed one of them in full:

- **PART B — PROVED** (both 0-hyp, aconv, soundness-probed; resume
  `partB_frontend_delta.sml`; re-verified by hand `L4_PARTB_ALL_OK`, Tagged(0)):
  - `pigeon_thm`    : `prime2 p ⟹ p = 2m+1 ⟹ ∃a b. a≤m ∧ b≤m ∧ cong p (a²+b²+1) 0`
    (the residue-set pigeonhole, via Thue's `list_pigeonhole`; +4 conservative
    recursion/case-def axioms for the helper consts `bres`/`fdec`).
  - `primemult_thm` : `prime2 p ⟹ p = 2m+1 ⟹ ∃m'. 0<m' ∧ m'<p ∧ four_sq (m'·p)`
    (composes `pigeon_thm` with the proven `pm_from_cong`). **Every odd prime has
    a four-square multiple** — Part B is closed.
- **PART C keystone — PROVED** (`sym_residue_signed`, 0-hyp, aconv; resume
  `partC_keystone_signed_delta.sml`; standalone `sr_full.sml` re-verified
  `SR_SIGNED_OK`, Tagged(0)):
  `0<m ⟹ ∃a'. (cong m a' a ∨ cong m (a'+a) 0) ∧ a'+a' ≤ m`.
- **KEY DIAGNOSTIC (why the descent stalled, now corrected):** the *originally*
  banked `sym_residue_thm`/`four_residue_sum_thm` deliver only the **squared**
  congruence `a'²≡a² (mod m)`, which is **strictly too weak** for the descent:
  the r=0 exclusion needs `a'=0 ⟹ m∣a` (and m is NOT prime here, so `m∣a²` does
  not give `m∣a`), and the Euler divide-by-m² needs per-coordinate sign
  divisibility — both require the **signed** relation `a'≡±a (mod m)`. This
  mirrors `isabelle_twosquare.sml`'s descent, which genuinely splits into
  `pos_descent` (`cong p U (c·V)`) and `neg_descent` (`cong p (U+c·V) 0`). So the
  new signed keystone is the *right* missing piece, not a detour.

REMAINING (precise, the genuinely large open piece): from `sym_residue_signed`,
(a) build a **signed `four_residue_sum`** (thread the per-coordinate ± disjunction
through all four coordinates → `a'²+b'²+c'²+d'² = m·r` with the SIGNED residues),
(b) the **r=0 exclusion** (`a'=…=d'=0 ⟹ m∣a,b,c,d ⟹ m²∣m·p ⟹ m∣p`, contra),
(c) **r<m**, (d) the **Euler divide-by-m²** (`(m·p)(m·r)=w²+x²+y²+z²` via
`proveStarFor`, `m∣w,x,y,z`, divide → `four_sq(r·p)`), then iterate the descent
to m=1 (`four_sq p`) and discharge `lagrange_assembly`. (c)/(d) are the
expensive ring-procedure steps (~13 min/`proveStarFor` call).

(Original 2026-06-17 status below; superseded where it lists Part B / the keystone
as open.)

---

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
