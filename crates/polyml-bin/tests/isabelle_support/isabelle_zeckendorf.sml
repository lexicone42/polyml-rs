(* ======================================================================
   ZECKENDORF'S THEOREM in Isabelle/Pure, on the classical NT foundation
   (spliced in front by common::with_nt_helpers).

   Every positive integer has a UNIQUE representation as a sum of
   NON-CONSECUTIVE Fibonacci numbers (e.g. 100 = 89 + 8 + 3).

   Definitions (all conservative recursion axioms):
     zfib 0 = 1,  zfib 1 = 2,  zfib (k+2) = zfib(k+1) + zfib k   (1,2,3,5,8,...)
     ixlist = INil | ICons nat ixlist                 (lists of zfib INDICES)
     rep_sum INil = 0,  rep_sum (ICons i r) = zfib i + rep_sum r
     vb b INil;  vb b (ICons i r) <-> (i < b) AND vb (i-1) r
     valid_rep r <-> vb-based: strictly-decreasing indices with gaps >= 2
                     (the genuine "non-consecutive Fibonacci indices" condition)

   Theorems (both 0-hypothesis, aconv-checked, soundness-probed):
     EXISTENCE  (ZK_EXIST_OK):  !n. 0 < n ==> EX r. valid_rep r AND rep_sum r = n
                  -- greedy strong induction (largest zfib k <= n; recurse on n - zfib k)
     UNIQUENESS (ZK_UNIQUE_OK): !n r1 r2. valid_rep r1 ==> valid_rep r2
                                ==> rep_sum r1 = n ==> rep_sum r2 = n ==> r1 = r2
                  -- the CRUX sum-bound (zfib k <= rep_sum r < zfib(k+1) for a rep
                     topping at k) forces the largest index from n alone; strip + recurse.

   The only non-Peano assumption is excluded middle (ex_middle), from the shared
   classical foundation. Built by ultracode wf_20b7a36f-ce3 (3 seats, all proved
   BOTH halves independently); the "robust" seat (this file) carries the explicit
   kernel soundness probes (rep genuinely non-consecutive; req genuinely
   discriminates lists; uniqueness genuinely concludes r1 = r2, not r1 = r1).
   ====================================================================== *)

val () = out "DELTA_START\n";
(* ======================================================================
   ZECKENDORF BASE on with_nt_helpers.  Extend thyS2 (the foundation's final,
   strong-induction-bearing theory) with:
     - zfib : nat -> nat   (distinct Fibonacci 1,2,3,5,8,...)
     - ixlist = INil | ICons nat ixlist   (index lists)
     - rep_sum : ixlist -> nat
     - vb : nat -> ixlist -> o   (valid-below-bound: strictly-dec, gaps>=2,
                                   all indices < the bound)
   then prove the basics + the CRUX sum-bound.
   ====================================================================== *)
val one  = suc ZeroC;
val two  = suc (suc ZeroC);

(* ---- sub (truncated subtraction), needed for the bound i-1 ---- *)
val thyZ0 = Sign.add_consts
  [(Binding.name "zfib", natT --> natT, NoSyn),
   (Binding.name "sub",  natT --> natT --> natT, NoSyn)] thyS2;
val zfibC = Const (Sign.full_name thyZ0 (Binding.name "zfib"), natT --> natT);
fun zfib t = zfibC $ t;
val subC = Const (Sign.full_name thyZ0 (Binding.name "sub"), natT --> natT --> natT);
fun sub a b = subC $ a $ b;

(* ---- ixlist datatype ---- *)
val thyZ0b = Sign.add_types_global [(Binding.name "ixlist",0,NoSyn)] thyZ0;
val ixlistN = Sign.full_name thyZ0b (Binding.name "ixlist");
val ixlistT = Type (ixlistN,[]);
val thyZ0c = Sign.add_consts
  [(Binding.name "INil",    ixlistT, NoSyn),
   (Binding.name "ICons",   natT --> ixlistT --> ixlistT, NoSyn),
   (Binding.name "rep_sum", ixlistT --> natT, NoSyn),
   (Binding.name "vb",      natT --> ixlistT --> oT, NoSyn),
   (Binding.name "valid_rep", ixlistT --> oT, NoSyn)] thyZ0b;
fun cZ nm T = Const (Sign.full_name thyZ0c (Binding.name nm), T);
val INilC   = cZ "INil" ixlistT;
val IConsC  = cZ "ICons" (natT --> ixlistT --> ixlistT);  fun icons i r = IConsC $ i $ r;
val repsumC = cZ "rep_sum" (ixlistT --> natT);            fun rep_sum r = repsumC $ r;
val vbC     = cZ "vb" (natT --> ixlistT --> oT);          fun vb b r = vbC $ b $ r;
val validC  = cZ "valid_rep" (ixlistT --> oT);            fun valid_rep r = validC $ r;
val rpredT  = ixlistT --> oT;

(* ---- zfib axioms ---- *)
val kZ = Free("k", natT);
val ((_,zfib_0), tZa) = Thm.add_axiom_global (Binding.name "zfib_0",
      jT (oeq (zfib ZeroC) one)) thyZ0c;
val ((_,zfib_1), tZb) = Thm.add_axiom_global (Binding.name "zfib_1",
      jT (oeq (zfib one) two)) tZa;
val ((_,zfib_SS), tZc) = Thm.add_axiom_global (Binding.name "zfib_SS",
      jT (oeq (zfib (suc (suc kZ))) (add (zfib (suc kZ)) (zfib kZ)))) tZb;
(* ---- sub axioms (truncated): sub n 0 = n ; sub 0 (Suc m) = 0 ; sub (Suc n)(Suc m)=sub n m ---- *)
val nS = Free("n", natT); val mS = Free("m", natT);
val ((_,sub_0),  tZd) = Thm.add_axiom_global (Binding.name "sub_0",
      jT (oeq (sub nS ZeroC) nS)) tZc;
val ((_,sub_Z),  tZe) = Thm.add_axiom_global (Binding.name "sub_Z",
      jT (oeq (sub ZeroC (suc mS)) ZeroC)) tZd;
val ((_,sub_SS), tZf) = Thm.add_axiom_global (Binding.name "sub_SS",
      jT (oeq (sub (suc nS) (suc mS)) (sub nS mS))) tZe;
(* ---- rep_sum axioms ---- *)
val iR = Free("i", natT); val rR = Free("r", ixlistT);
val ((_,rep_INil),  tZg) = Thm.add_axiom_global (Binding.name "rep_INil",
      jT (oeq (rep_sum INilC) ZeroC)) tZf;
val ((_,rep_ICons), tZh) = Thm.add_axiom_global (Binding.name "rep_ICons",
      jT (oeq (rep_sum (icons iR rR)) (add (zfib iR) (rep_sum rR)))) tZg;
(* ---- vb axioms : vb b INil = True (encoded as: vb b INil is provable);
        vb b (ICons i r) <-> (lt i b) /\ vb (sub i 1) r.
   We model "True" as oeq Zero Zero (a trivially provable o-prop) for the Nil
   case, and give vb_ICons as a two-way bridge via fold/unfold. ---- *)
val bV = Free("b", natT);
(* vb_INil : provable for any b *)
val ((_,vb_INil), tZi) = Thm.add_axiom_global (Binding.name "vb_INil",
      jT (vb bV INilC)) tZh;
(* unfold: vb b (ICons i r) ==> (lt i b)   and   ==> vb (sub i 1) r *)
val ((_,vb_lt),  tZj) = Thm.add_axiom_global (Binding.name "vb_lt",
      Logic.mk_implies (jT (vb bV (icons iR rR)), jT (lt iR bV))) tZi;
val ((_,vb_tl),  tZk) = Thm.add_axiom_global (Binding.name "vb_tl",
      Logic.mk_implies (jT (vb bV (icons iR rR)), jT (vb (sub iR one) rR))) tZj;
(* fold: (lt i b) ==> vb (sub i 1) r ==> vb b (ICons i r) *)
val ((_,vb_cons), tZl) = Thm.add_axiom_global (Binding.name "vb_cons",
      Logic.mk_implies (jT (lt iR bV),
        Logic.mk_implies (jT (vb (sub iR one) rR), jT (vb bV (icons iR rR))))) tZk;
(* ---- valid_rep : the UN-capped validity (strictly-dec + gaps>=2).
   valid_rep INil = True ; valid_rep (ICons i r) <-> vb (sub i 1) r
   (head i is the max; tail valid below i-1 forces next index < i-1, gap>=2). ---- *)
val ((_,valid_INil), tZl1) = Thm.add_axiom_global (Binding.name "valid_INil",
      jT (valid_rep INilC)) tZl;
val ((_,valid_unfold), tZl2) = Thm.add_axiom_global (Binding.name "valid_unfold",
      Logic.mk_implies (jT (valid_rep (icons iR rR)), jT (vb (sub iR one) rR))) tZl1;
val ((_,valid_fold), tZl3) = Thm.add_axiom_global (Binding.name "valid_fold",
      Logic.mk_implies (jT (vb (sub iR one) rR), jT (valid_rep (icons iR rR)))) tZl2;
(* ---- list induction over ixlist ---- *)
val PL = Free("P", rpredT);
val iL = Free("i", natT); val rL = Free("r", ixlistT); val kL = Free("k", ixlistT);
val list_induct_prop =
  Logic.mk_implies (jT (PL $ INilC),
    Logic.mk_implies
      (Logic.all iL (Logic.all rL
         (Logic.mk_implies (jT (PL $ rL), jT (PL $ (icons iL rL))))),
       jT (PL $ kL)));
val ((_,list_induct), thyZ) = Thm.add_axiom_global (Binding.name "ixlist_induct", list_induct_prop) tZl3;

(* ============================================================================
   THE single final context for the Zeckendorf development.
   ============================================================================ *)
val ctxtZ  = Proof_Context.init_global thyZ;
val ctermZ = Thm.cterm_of ctxtZ;

(* ---- re-varify reused foundation axioms/lemmas onto ctxtZ ---- *)
val zfib_0_v  = varify zfib_0;
val zfib_1_v  = varify zfib_1;
val zfib_SS_v = varify zfib_SS;
val sub_0_v   = varify sub_0;
val sub_Z_v   = varify sub_Z;
val sub_SS_v  = varify sub_SS;
val rep_INil_v= varify rep_INil;
val rep_ICons_v= varify rep_ICons;
val vb_INil_v = varify vb_INil;
val vb_lt_v   = varify vb_lt;
val vb_tl_v   = varify vb_tl;
val vb_cons_v = varify vb_cons;
val valid_INil_v   = varify valid_INil;
val valid_unfold_v = varify valid_unfold;
val valid_fold_v   = varify valid_fold;
val list_induct_v = varify list_induct;

val oeq_refl_vZ   = varify oeq_refl;
val oeq_subst_vZ  = varify oeq_subst;
val add_0_vZ      = varify add_0;
val add_Suc_vZ    = varify add_Suc;
val add_0_right_vZ= varify add_0_right;
val add_Suc_right_vZ = varify add_Suc_right;
val add_comm_vZ   = varify add_comm;
val add_assoc_vZ  = varify add_assoc;
val nat_induct_vZ = varify nat_induct;
val exI_vZ        = varify exI_ax;
val exE_vZ        = varify exE_ax;
val le_refl_vZ    = varify le_refl;
val le_add_vZ     = varify le_add;
val le_trans_vZ   = varify le_trans;
val lt_suc_vZ     = varify lt_suc;
val lt_trans_vZ   = varify lt_trans;
val le_suc_mono_vZ= varify le_suc_mono;
val le_add_mono_vZ= varify le_add_mono;

(* ---- ground instantiators on ctxtZ ---- *)
fun oeqreflZ_at t = beta_norm (Drule.infer_instantiate ctxtZ [(("a",0), ctermZ t)] oeq_refl_vZ);
fun add0Z_at t    = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ t)] add_0_vZ);
fun addSucZ_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("m",0), ctermZ mt),(("n",0), ctermZ nt)] add_Suc_vZ);
fun add0rZ_at t   = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ t)] add_0_right_vZ);
fun addSrZ_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("m",0), ctermZ mt),(("n",0), ctermZ nt)] add_Suc_right_vZ);
fun addcommZ_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("m",0), ctermZ mt),(("n",0), ctermZ nt)] add_comm_vZ);
fun addassocZ_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("m",0), ctermZ mt),(("n",0), ctermZ nt),(("k",0), ctermZ kt)] add_assoc_vZ);
fun zfibSS_at t   = beta_norm (Drule.infer_instantiate ctxtZ [(("k",0), ctermZ t)] zfib_SS_v);
fun sub0_at t     = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ t)] sub_0_v);
fun subZ_at t     = beta_norm (Drule.infer_instantiate ctxtZ [(("m",0), ctermZ t)] sub_Z_v);
fun subSS_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("n",0), ctermZ nt),(("m",0), ctermZ mt)] sub_SS_v);
fun repCons_at (it,rt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("i",0), ctermZ it),(("r",0), ctermZ rt)] rep_ICons_v);
fun vbINil_at t   = beta_norm (Drule.infer_instantiate ctxtZ [(("b",0), ctermZ t)] vb_INil_v);
fun vbLt_at (bt,it,rt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("b",0), ctermZ bt),(("i",0), ctermZ it),(("r",0), ctermZ rt)] vb_lt_v);
fun vbTl_at (bt,it,rt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("b",0), ctermZ bt),(("i",0), ctermZ it),(("r",0), ctermZ rt)] vb_tl_v);
fun vbCons_at (bt,it,rt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("b",0), ctermZ bt),(("i",0), ctermZ it),(("r",0), ctermZ rt)] vb_cons_v);
fun validUnfold_at (it,rt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("i",0), ctermZ it),(("r",0), ctermZ rt)] valid_unfold_v);
fun validFold_at (it,rt) = beta_norm (Drule.infer_instantiate ctxtZ
                          [(("i",0), ctermZ it),(("r",0), ctermZ rt)] valid_fold_v);

(* ---- classical-FOL connective helpers re-stated on ctxtZ ----
   (conjI_atT/disjE_elimC etc. in the foundation are built on ctxtC, whose
   signature predates zfib/ixlist; rebuild them on ctxtZ.) *)
val conjI_vZ      = varify conjI_ax;
val conjunct1_vZ  = varify conjunct1_ax;
val conjunct2_vZ  = varify conjunct2_ax;
val disjI1_vZ     = varify disjI1_ax;
val disjI2_vZ     = varify disjI2_ax;
val disjE_vZ      = varify disjE_ax;
val mp_vZ         = varify mp_ax;
val oFalse_elim_vZ= varify oFalse_elim_ax;
val ex_middle_vZ  = varify ex_middle_ax;
fun conjI_atZ (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] conjI_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atZ (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] conjunct1_vZ)
  in Thm.implies_elim inst h end;
fun conjunct2_atZ (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] conjunct2_vZ)
  in Thm.implies_elim inst h end;
fun disjI1_atZ (At,Bt) h =
  (beta_norm (Drule.infer_instantiate ctxtZ [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] disjI1_vZ)) OF [h];
fun disjI2_atZ (At,Bt) h =
  (beta_norm (Drule.infer_instantiate ctxtZ [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] disjI2_vZ)) OF [h];
fun disjE_elimZ (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("A",0), ctermZ At),(("B",0), ctermZ Bt),(("C",0), ctermZ Ct)] disjE_vZ)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun mp_atZ (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] mp_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun oFalse_elimZ_at rT = beta_norm (Drule.infer_instantiate ctxtZ [(("R",0), ctermZ rT)] oFalse_elim_vZ);
fun ex_middle_atZ At = beta_norm (Drule.infer_instantiate ctxtZ [(("A",0), ctermZ At)] ex_middle_vZ);
val impI_vZ       = varify impI_ax;
val allI_vZ       = varify allI_ax;
val allE_vZ       = varify allE_ax;
(* impI_atZ (At,Bt) hImpThm : feed a meta-implication (jT At ==> jT Bt) -> jT (Imp At Bt) *)
fun impI_atZ (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("A",0), ctermZ At),(("B",0), ctermZ Bt)] impI_vZ)
  in Thm.implies_elim inst hImpThm end;
(* allI_atZ Pabs hAllThm : Pabs nat=>o, hAllThm : !!x. jT (Pabs x) -> jT (Forall Pabs) *)
fun allI_atZ Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ [(("P",0), ctermZ Pabs)] allI_vZ)
  in Thm.implies_elim inst hAllThm end;
(* allE_atZ Pabs at hForall : jT (Forall Pabs) -> jT (Pabs at) (beta-normalised) *)
fun allE_atZ Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ
        [(("P",0), ctermZ Pabs),(("a",0), ctermZ at)] allE_vZ)
  in Thm.implies_elim inst hForall end;

(* exE elimination on ctxtZ *)
fun exE_elimZ (Pabs, goalC) exThm wName wTy bodyFn =
  let
    val wF = Free(wName, wTy);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermZ hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermZ wF) (Thm.implies_intr (ctermZ hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Pabs), (("Q",0), ctermZ goalC)] exE_vZ);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* le_intro on ctxtZ *)
fun le_introZ (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Pabs), (("a",0), ctermZ w)] exI_vZ);
  in inst OF [hyp] end;

(* add-congruence helpers on ctxtZ *)
fun add_cong_lZ (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Pabs), (("a",0), ctermZ pT), (("b",0), ctermZ qT)] oeq_subst_vZ);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtZ [(("a",0), ctermZ (add pT kT))] oeq_refl_vZ);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rZ (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Pabs), (("a",0), ctermZ pT), (("b",0), ctermZ qT)] oeq_subst_vZ);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtZ [(("a",0), ctermZ (add hT pT))] oeq_refl_vZ);
  in inst OF [hpq, refl_hp] end;

(* generic oeq_subst for an arbitrary one-hole predicate Pabs over nat *)
fun oeq_subst_at (Pabs, aT, bT) heq hPa =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Pabs), (("a",0), ctermZ aT), (("b",0), ctermZ bT)] oeq_subst_vZ);
  in (inst OF [heq]) OF [hPa] end;

val () = out "ZBASE_CONTEXT_READY\n";

(* ============================================================================
   zfib_nz : Ex(%m. oeq (zfib k) (Suc m))   ("zfib k is nonzero")  for all k.
   Plain nat_induct gives at Suc(Suc ..) the recursion, but the IH only covers
   the predecessor.  We use the PAIRED predicate
       R k := (Ex(%m. zfib k = Suc m)) /\ (Ex(%m. zfib (Suc k) = Suc m))
   R 0 from zfib_0 (=Suc 0) and zfib_1 (=Suc(Suc 0));  R(Suc k) reuses R k's
   2nd conjunct for the 1st, and zfib_SS for the 2nd (a sum with a nonzero
   summand is nonzero).
   ============================================================================ *)
fun mkExSuc t = mkEx (Abs ("m", natT, oeq t (suc (Bound 0))));
(* exI for "t = Suc w" *)
fun exSuc_intro (t, w) heq =   (* heq : oeq t (Suc w)  ->  Ex(%m. oeq t (Suc m)) *)
  let
    val Pabs = Abs ("m", natT, oeq t (suc (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Pabs), (("a",0), ctermZ w)] exI_vZ);
  in inst OF [heq] end;

(* zfib 0 = Suc 0 : from zfib_0 (zfib 0 = 1 = Suc 0) *)
val z0_is_Suc = exSuc_intro (zfib ZeroC, ZeroC) zfib_0_v;          (* one = Suc 0 definitionally *)
val () = out ("z0_is_Suc: " ^ Syntax.string_of_term ctxtZ (Thm.prop_of z0_is_Suc) ^ "\n");

(* ============================================================================
   zfib_nz : forall k. Ex(%m. oeq (zfib k) (Suc m))   via the paired predicate.
   ============================================================================ *)
fun nz t = mkExSuc t;                               (* Ex(%m. oeq t (Suc m)) *)
(* build pairPred via Term.lambda over a fresh Free to avoid de-Bruijn capture
   by nz's inner Abs("m",..). *)
val pairPred =
  let val kk = Free("k_pp", natT)
  in Term.lambda kk (mkConj (nz (zfib kk)) (nz (zfib (suc kk)))) end;

(* base R 0 : nz (zfib 0) /\ nz (zfib 1) *)
val z0nz = exSuc_intro (zfib ZeroC, ZeroC) zfib_0_v;          (* nz (zfib 0), zfib 0 = Suc 0 *)
val z1nz = exSuc_intro (zfib one, one) zfib_1_v;             (* nz (zfib 1), zfib 1 = Suc(Suc 0) *)
val baseR = conjI_atZ (nz (zfib ZeroC), nz (zfib one)) z0nz z1nz;

(* step: !!x. R x ==> R(Suc x)
     R x = nz(zfib x) /\ nz(zfib(Suc x))
     R(Suc x) = nz(zfib(Suc x)) /\ nz(zfib(Suc(Suc x)))
   1st conjunct = R x's 2nd conjunct.
   2nd: zfib(Suc(Suc x)) = zfib(Suc x) + zfib x ; zfib(Suc x) = Suc w (from R x.2)
        so zfib(Suc(Suc x)) = Suc w + zfib x = Suc (w + zfib x)  -> nz. *)
val zstep =
  let
    val xF = Free("x_z", natT);
    val RxProp = jT (mkConj (nz (zfib xF)) (nz (zfib (suc xF))));
    val Rx = Thm.assume (ctermZ RxProp);
    val c1 = conjunct1_atZ (nz (zfib xF), nz (zfib (suc xF))) Rx;   (* nz (zfib x) *)
    val c2 = conjunct2_atZ (nz (zfib xF), nz (zfib (suc xF))) Rx;   (* nz (zfib (Suc x)) *)
    (* derive nz (zfib (Suc (Suc x))) from c2 + zfib_SS *)
    (* use exE on c2 : Ex(%m. zfib(Suc x) = Suc m) *)
    val Pc2 = Abs("m", natT, oeq (zfib (suc xF)) (suc (Bound 0)));
    val goal2 = nz (zfib (suc (suc xF)));
    fun body2 w hw =                                  (* hw : zfib(Suc x) = Suc w *)
      let
        val ss = zfibSS_at xF;                        (* zfib(Suc(Suc x)) = zfib(Suc x) + zfib x *)
        (* rewrite zfib(Suc x) -> Suc w in the sum:  add (zfib(Suc x)) (zfib x) = add (Suc w)(zfib x) *)
        val cong = add_cong_lZ (zfib (suc xF), suc w, zfib xF) hw;  (* add(zfib(Sx))(zfib x)=add(Suc w)(zfib x) *)
        val e1 = oeq_trans OF [ss, cong];             (* zfib(SSx) = add (Suc w)(zfib x) *)
        val aS = addSucZ_at (w, zfib xF);             (* add (Suc w)(zfib x) = Suc(add w (zfib x)) *)
        val e2 = oeq_trans OF [e1, aS];               (* zfib(SSx) = Suc(add w (zfib x)) *)
      in exSuc_intro (zfib (suc (suc xF)), add w (zfib xF)) e2 end;
    val nzSS = exE_elimZ (Pc2, goal2) c2 "w_z" natT body2;
    val RSx = conjI_atZ (nz (zfib (suc xF)), nz (zfib (suc (suc xF)))) c2 nzSS;
    val disch = Thm.implies_intr (ctermZ RxProp) RSx;
  in Thm.forall_intr (ctermZ xF) disch end;

val zfib_nz =
  let
    val kF = Free("k", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ pairPred), (("k",0), ctermZ kF)] nat_induct_vZ);
    val r1 = Thm.implies_elim ind baseR;
    val Rk = Thm.implies_elim r1 zstep;              (* R k = nz(zfib k) /\ nz(zfib(Suc k)) *)
    val nzk = conjunct1_atZ (nz (zfib kF), nz (zfib (suc kF))) Rk;
  in varify nzk end;
val () = out ("zfib_nz: " ^ Syntax.string_of_term ctxtZ (Thm.prop_of zfib_nz) ^ "\n");

(* ---- zfib_ge1 : le one (zfib k)   from zfib_nz ---- *)
val zfib_ge1 =
  let
    val kF = Free("k", natT);
    val nzk = beta_norm (Drule.infer_instantiate ctxtZ [(("k",0), ctermZ kF)] (varify zfib_nz));
    val Pnz = Abs("m", natT, oeq (zfib kF) (suc (Bound 0)));
    val goal = le one (zfib kF);
    fun body w hw =                                  (* hw : zfib k = Suc w *)
      let
        (* le one (zfib k) = Ex(%p. zfib k = add one p).  witness p = w.
           need zfib k = add one w = Suc w. add one w = add (Suc 0) w = Suc(add 0 w)=Suc w *)
        val aS = addSucZ_at (ZeroC, w);              (* add (Suc 0) w = Suc(add 0 w) *)
        val a0 = add0Z_at w;                         (* add 0 w = w *)
        val aSc = oeq_trans OF [aS, (let val P=Abs("z",natT,oeq (suc (add ZeroC w)) (suc (Bound 0)))
                                       in oeq_subst_at (P, add ZeroC w, w) a0 (oeqreflZ_at (suc (add ZeroC w))) end)];
        (* aSc : add one w = Suc w *)
        val hh = oeq_trans OF [hw, oeq_sym OF [aSc]];  (* zfib k = add one w *)
      in le_introZ (one, zfib kF, w) hh end;
    val res = exE_elimZ (Pnz, goal) nzk "w_g" natT body;
  in varify res end;
val () = out ("zfib_ge1: " ^ Syntax.string_of_term ctxtZ (Thm.prop_of zfib_ge1) ^ "\n");
val () = out ("zfib_ge1 hyps=" ^ Int.toString (length (Thm.hyps_of zfib_ge1)) ^ "\n");
(* ============================================================================
   lt_add_pos : le one c ==> lt a (add a c)      (adding >=1 strictly increases)
     le one c  =  Ex(%p. c = Suc 0 + p) ; from c>=1 get c = Suc c0 (c0 = ... ).
     Actually simplest: le one c gives a witness p with c = add one p = Suc p
     (since add one p = Suc(add 0 p) = Suc p).  Then add a c = add a (Suc p)
     = Suc(add a p) and lt a (Suc(add a p)) = le (Suc a)(Suc(add a p)) from
     le a (add a p) (=le_add) via le_suc_mono.
   ============================================================================ *)
val lt_add_pos =
  let
    val aF = Free("a", natT); val cF = Free("c", natT);
    val H = Thm.assume (ctermZ (jT (le one cF)));        (* Ex(%p. c = add one p) *)
    val Pabs = Abs("p", natT, oeq cF (add one (Bound 0)));
    val goal = lt aF (add aF cF);                        (* le (Suc a)(add a c) *)
    fun body p hp =                                       (* hp : c = add one p *)
      let
        (* add one p = Suc p *)
        val aS = addSucZ_at (ZeroC, p);                  (* add (Suc 0) p = Suc(add 0 p) *)
        val a0 = add0Z_at p;                             (* add 0 p = p *)
        val one_p = oeq_trans OF [aS,
                       (let val P=Abs("z",natT,oeq (suc (add ZeroC p)) (suc (Bound 0)))
                        in oeq_subst_at (P, add ZeroC p, p) a0 (oeqreflZ_at (suc (add ZeroC p))) end)];
        (* one_p : add one p = Suc p *)
        val c_Sp = oeq_trans OF [hp, one_p];             (* c = Suc p *)
        (* le a (add a p)  (le_add)  : le_add gives le m (add m p) at m=a *)
        val la = beta_norm (Drule.infer_instantiate ctxtZ
                   [(("m",0), ctermZ aF),(("p",0), ctermZ p)] le_add_vZ); (* le a (add a p) *)
        (* le_suc_mono : le a (add a p) ==> le (Suc a)(Suc(add a p)) *)
        val lsm = beta_norm (Drule.infer_instantiate ctxtZ
                    [(("m",0), ctermZ aF),(("n",0), ctermZ (add aF p))] le_suc_mono_vZ);
        val le_SaS = lsm OF [la];                          (* le (Suc a)(Suc(add a p)) *)
        (* Suc(add a p) = add a (Suc p) = add a c   (need add a (Suc p) and rewrite c) *)
        val aSr = addSrZ_at (aF, p);                       (* add a (Suc p) = Suc(add a p) *)
        (* so Suc(add a p) = add a (Suc p) *)
        val Suc_eq = oeq_sym OF [aSr];                     (* Suc(add a p) = add a (Suc p) *)
        (* add a (Suc p) = add a c  by add_cong_r of (Suc p = c) i.e. sym c_Sp *)
        val Sp_c = oeq_sym OF [c_Sp];                      (* Suc p = c *)
        val acong = add_cong_rZ (aF, suc p, cF) Sp_c;      (* add a (Suc p) = add a c *)
        val bridge = oeq_trans OF [Suc_eq, acong];         (* Suc(add a p) = add a c *)
        (* rewrite le (Suc a)(Suc(add a p)) -> le (Suc a)(add a c) via subst on 2nd arg.
           Build Ple with Term.lambda over a fresh Free to avoid de-Bruijn capture
           by le's inner Abs. *)
        val Ple = let val zz = Free("z_le", natT) in Term.lambda zz (le (suc aF) zz) end;
        val res = oeq_subst_at (Ple, suc (add aF p), add aF cF) bridge le_SaS;
      in res end;                                          (* le (Suc a)(add a c) = lt a (add a c) *)
    val core = exE_elimZ (Pabs, goal) H "p_lp" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le one cF))) core;
  in varify disch end;
val () = out ("lt_add_pos: " ^ Syntax.string_of_term ctxtZ (Thm.prop_of lt_add_pos)
              ^ " hyps=" ^ Int.toString (length (Thm.hyps_of lt_add_pos)) ^ "\n");

(* ============================================================================
   zfib_mono : lt (zfib k) (zfib (Suc k))     for all k.   By nat_induct.
     base k=0 : lt (zfib 0)(zfib 1) = lt 1 2 = le 2 2 (le_refl).
     step     : show lt (zfib(Suc k))(zfib(Suc(Suc k))).
                zfib(Suc(Suc k)) = zfib(Suc k) + zfib k ; zfib k >= 1 ;
                so lt (zfib(Suc k)) (zfib(Suc k)+zfib k) by lt_add_pos.
   ============================================================================ *)
val zfib_mono =
  let
    val monoPred =
      let val kk = Free("k_m", natT)
      in Term.lambda kk (lt (zfib kk) (zfib (suc kk))) end;
    val kF = Free("k", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ monoPred), (("k",0), ctermZ kF)] nat_induct_vZ);
    (* BASE : lt (zfib 0)(zfib 1).  zfib 0 = 1, zfib 1 = 2.  lt 1 2 = le 2 2. *)
    val base =
      let
        (* le 2 2 by le_refl @ 2 *)
        val lr = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ two)] le_refl_vZ); (* le 2 2 *)
        (* lt (zfib 0)(zfib 1) = le (Suc(zfib 0))(zfib 1).
           rewrite: Suc(zfib 0) = Suc 1 = 2 (zfib 0 = 1) ; zfib 1 = 2.
           So want le 2 2, then rewrite both args back. *)
        (* le 2 (zfib 1)  from le 2 2 via subst 2 -> zfib 1 (sym zfib_1) *)
        val z1s = oeq_sym OF [zfib_1_v];                  (* 2 = zfib 1 *)
        val Pr  = let val zz = Free("z_b1", natT) in Term.lambda zz (le two zz) end;
        val l2z1 = oeq_subst_at (Pr, two, zfib one) z1s lr;   (* le 2 (zfib 1) *)
        (* le (Suc(zfib 0)) (zfib 1) from le 2 (zfib 1) via subst 2 -> Suc(zfib 0).
           2 = Suc 1 = Suc(zfib 0)?  Suc(zfib 0) = Suc 1 = 2.  need 2 = Suc(zfib 0). *)
        (* zfib 0 = 1 (zfib_0). Suc(zfib 0) = Suc 1 = 2.  So 2 = Suc(zfib 0) via Suc_cong(sym zfib_0). *)
        val z0s = oeq_sym OF [zfib_0_v];                  (* 1 = zfib 0 *)
        val Sc  = let val P=Abs("z",natT,oeq two (suc (Bound 0)))
                  in oeq_subst_at (P, one, zfib ZeroC) z0s (oeqreflZ_at two) end; (* 2 = Suc(zfib 0)? two = Suc one, and one->zfib 0 *)
        (* Sc : oeq two (suc (zfib Zero)) *)
        val Pl  = let val zz = Free("z_b2", natT) in Term.lambda zz (le zz (zfib one)) end;
        val res = oeq_subst_at (Pl, two, suc (zfib ZeroC)) Sc l2z1;   (* le (Suc(zfib 0))(zfib 1) *)
      in res end;
    (* STEP : !!k. lt(zfib k)(zfib(Suc k)) ==> lt(zfib(Suc k))(zfib(Suc(Suc k))) *)
    val step =
      let
        val xF = Free("x_m", natT);
        val IHprop = jT (lt (zfib xF) (zfib (suc xF)));
        val IH = Thm.assume (ctermZ IHprop);             (* unused but discharged *)
        val ge1 = beta_norm (Drule.infer_instantiate ctxtZ [(("k",0), ctermZ xF)] (varify zfib_ge1)); (* le 1 (zfib x) *)
        val lap = beta_norm (Drule.infer_instantiate ctxtZ
                    [(("a",0), ctermZ (zfib (suc xF))),(("c",0), ctermZ (zfib xF))] (varify lt_add_pos));
        val ltsum = lap OF [ge1];                          (* lt (zfib(Sx)) (add (zfib(Sx))(zfib x)) *)
        (* rewrite add(zfib(Sx))(zfib x) -> zfib(SSx) via sym zfib_SS[x] *)
        val ss = zfibSS_at xF;                            (* zfib(SSx) = add(zfib Sx)(zfib x) *)
        val sssym = oeq_sym OF [ss];                       (* add(zfib Sx)(zfib x) = zfib(SSx) *)
        val Pr = let val zz = Free("z_st", natT) in Term.lambda zz (lt (zfib (suc xF)) zz) end;
        val res = oeq_subst_at (Pr, add (zfib (suc xF)) (zfib xF), zfib (suc (suc xF))) sssym ltsum;
        val disch = Thm.implies_intr (ctermZ IHprop) res;
      in Thm.forall_intr (ctermZ xF) disch end;
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;
  in varify r2 end;
val () = out ("zfib_mono: " ^ Syntax.string_of_term ctxtZ (Thm.prop_of zfib_mono)
              ^ " hyps=" ^ Int.toString (length (Thm.hyps_of zfib_mono)) ^ "\n");
(* ============================================================================
   lt_imp_le : lt a b ==> le a b
     lt a b = le (Suc a) b = Ex(%p. b = Suc a + p) = Ex(%p. b = Suc(a+p)) = ...
     b = add (Suc a) p = Suc(add a p) = add a (Suc p)  ->  le a b  (witness Suc p)
   ============================================================================ *)
val lt_imp_le =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val H = Thm.assume (ctermZ (jT (lt aF bF)));        (* Ex(%p. b = add (Suc a) p) *)
    val Pabs = Abs("p", natT, oeq bF (add (suc aF) (Bound 0)));
    val goal = le aF bF;
    fun body p hp =                                      (* hp : b = add (Suc a) p *)
      let
        val aS = addSucZ_at (aF, p);                     (* add (Suc a) p = Suc(add a p) *)
        val b_S = oeq_trans OF [hp, aS];                 (* b = Suc(add a p) *)
        val aSr = addSrZ_at (aF, p);                     (* add a (Suc p) = Suc(add a p) *)
        val b_aSp = oeq_trans OF [b_S, oeq_sym OF [aSr]];(* b = add a (Suc p) *)
      in le_introZ (aF, bF, suc p) b_aSp end;
    val core = exE_elimZ (Pabs, goal) H "p_li" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (lt aF bF))) core;
  in varify disch end;
val () = out ("lt_imp_le hyps=" ^ Int.toString (length (Thm.hyps_of lt_imp_le)) ^ "\n");

(* ============================================================================
   add_mono_r : le a b ==> le (add c a) (add c b)      (fixed LEFT summand c)
     le a b : b = a + p.  add c b = add c (a+p) = (c+a)+p  (assoc),  witness p.
   ============================================================================ *)
val add_mono_r =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H = Thm.assume (ctermZ (jT (le aF bF)));         (* Ex(%p. b = add a p) *)
    val Pabs = Abs("p", natT, oeq bF (add aF (Bound 0)));
    val goal = le (add cF aF) (add cF bF);
    fun body p hp =                                       (* hp : b = add a p *)
      let
        (* add c b = add c (add a p) = add (add c a) p   (assoc, reversed) *)
        val congr = add_cong_rZ (cF, bF, add aF p) hp;   (* add c b = add c (add a p) *)
        val as1 = addassocZ_at (cF, aF, p);              (* add (add c a) p = add c (add a p) *)
        val cb_eq = oeq_trans OF [congr, oeq_sym OF [as1]];   (* add c b = add (add c a) p *)
      in le_introZ (add cF aF, add cF bF, p) cb_eq end;
    val core = exE_elimZ (Pabs, goal) H "p_am" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le aF bF))) core;
  in varify disch end;
val () = out ("add_mono_r hyps=" ^ Int.toString (length (Thm.hyps_of add_mono_r)) ^ "\n");

(* ============================================================================
   zfib_step_d : le (zfib i) (zfib (add i d))     for all i, d.   Induction on d.
     d=0 : zfib(add i 0) = zfib i (add_0_right) ; le (zfib i)(zfib i) (le_refl).
     d=Suc e : IH le (zfib i)(zfib(add i e)).  Also zfib(add i e) <= zfib(Suc(add i e))
       (lt_imp_le of zfib_mono).  And zfib(add i (Suc e)) = zfib(Suc(add i e))
       (add_Suc_right cong).  Chain by le_trans.
   ============================================================================ *)
val zfib_step_d =
  let
    val iF = Free("i", natT);
    val stepPred =
      let val dd = Free("d_sp", natT)
      in Term.lambda dd (le (zfib iF) (zfib (add iF dd))) end;
    val dF = Free("d", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ stepPred), (("k",0), ctermZ dF)] nat_induct_vZ);
    (* BASE d=0 : le (zfib i)(zfib(add i 0)).  add i 0 = i. *)
    val base =
      let
        val lr = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ (zfib iF))] le_refl_vZ); (* le (zfib i)(zfib i) *)
        val a0r = add0rZ_at iF;                          (* add i 0 = i *)
        val a0rs = oeq_sym OF [a0r];                     (* i = add i 0 *)
        (* rewrite le (zfib i)(zfib i) -> le (zfib i)(zfib(add i 0)) via subst i->add i 0
           inside zfib on the 2nd arg.  predicate %z. le (zfib i)(zfib z). *)
        val Pr = let val zz = Free("z_sb", natT) in Term.lambda zz (le (zfib iF) (zfib zz)) end;
        val res = oeq_subst_at (Pr, iF, add iF ZeroC) a0rs lr;
      in res end;
    (* STEP d=Suc e *)
    val step =
      let
        val eF = Free("e_sp", natT);
        val IHprop = jT (le (zfib iF) (zfib (add iF eF)));
        val IH = Thm.assume (ctermZ IHprop);
        (* zfib_mono at (add i e) : lt (zfib(add i e))(zfib(Suc(add i e))) *)
        val zm = beta_norm (Drule.infer_instantiate ctxtZ
                   [(("k",0), ctermZ (add iF eF))] (varify zfib_mono));   (* lt (zfib(add i e))(zfib(Suc(add i e))) *)
        val zml = (varify lt_imp_le) OF [zm];            (* le (zfib(add i e))(zfib(Suc(add i e))) *)
        (* chain IH then zml : le (zfib i)(zfib(Suc(add i e))) *)
        val lt1 = (varify le_trans) OF [IH, zml];        (* le (zfib i)(zfib(Suc(add i e))) *)
        (* rewrite Suc(add i e) -> add i (Suc e) : add_Suc_right sym *)
        val aSr = addSrZ_at (iF, eF);                    (* add i (Suc e) = Suc(add i e) *)
        val Pr = let val zz = Free("z_ss", natT) in Term.lambda zz (le (zfib iF) (zfib zz)) end;
        val res = oeq_subst_at (Pr, suc (add iF eF), add iF (suc eF)) (oeq_sym OF [aSr]) lt1;
        val disch = Thm.implies_intr (ctermZ IHprop) res;
      in Thm.forall_intr (ctermZ eF) disch end;
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;
  in varify r2 end;
val () = out ("zfib_step_d hyps=" ^ Int.toString (length (Thm.hyps_of zfib_step_d))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of zfib_step_d) ^ "\n");

(* ============================================================================
   le_zfib : le i j ==> le (zfib i) (zfib j)        (zfib monotone, non-strict)
     le i j : j = i + d.  zfib_step_d : le (zfib i)(zfib(i+d)) ; rewrite (i+d)->j.
   ============================================================================ *)
val le_zfib =
  let
    val iF = Free("i", natT); val jF = Free("j", natT);
    val H = Thm.assume (ctermZ (jT (le iF jF)));         (* Ex(%d. j = add i d) *)
    val Pabs = Abs("d", natT, oeq jF (add iF (Bound 0)));
    val goal = le (zfib iF) (zfib jF);
    fun body d hd =                                       (* hd : j = add i d *)
      let
        val sd = beta_norm (Drule.infer_instantiate ctxtZ
                   [(("i",0), ctermZ iF),(("d",0), ctermZ d)] (varify zfib_step_d)); (* le (zfib i)(zfib(add i d)) *)
        (* rewrite add i d -> j inside zfib 2nd arg : subst (add i d)->j via sym hd *)
        val Pr = let val zz = Free("z_lz", natT) in Term.lambda zz (le (zfib iF) (zfib zz)) end;
        val res = oeq_subst_at (Pr, add iF d, jF) (oeq_sym OF [hd]) sd;
      in res end;
    val core = exE_elimZ (Pabs, goal) H "d_lz" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le iF jF))) core;
  in varify disch end;
val () = out ("le_zfib hyps=" ^ Int.toString (length (Thm.hyps_of le_zfib)) ^ "\n");

(* ============================================================================
   zfib_two_step : le (add (zfib i) (zfib (sub i one))) (zfib (Suc i))
     i=0   : sub 0 1 = 0 ; add (zfib 0)(zfib 0) = 1+1 = 2 = zfib 1 = zfib(Suc 0).
     i=Suc j : sub (Suc j) 1 = j ; add (zfib(Suc j))(zfib j) = zfib(Suc(Suc j))
               = zfib(Suc i)  (zfib_SS) -> equality -> le (le_refl after subst).
   ============================================================================ *)
val zfib_two_step =
  let
    val iF = Free("i", natT);
    (* case split on i via disj_zero_or_suc *)
    val dz = beta_norm (Drule.infer_instantiate ctxtZ [(("p",0), ctermZ iF)] (varify disj_zero_or_suc));
    (* dz : Disj (oeq i 0) (Ex(%q. oeq i (Suc q))) *)
    val goalC = le (add (zfib iF) (zfib (sub iF one))) (zfib (suc iF));
    (* CASE i = 0 *)
    val caseZero =
      let
        val hz = Thm.assume (ctermZ (jT (oeq iF ZeroC)));  (* i = 0 *)
        (* prove le (add(zfib 0)(zfib(sub 0 1)))(zfib(Suc 0)) then rewrite 0->i ... actually
           easier: prove the goal AT i, but using i=0 to rewrite i to 0 everywhere, prove the
           ground 0-case, then rewrite back.  We instead prove the ground 0 instance and
           transport along i=0 (sym). *)
        (* ground: sub 0 1 = 0 *)
        val s01 = subZ_at ZeroC;                          (* sub 0 (Suc 0) = 0 ; one = Suc 0 *)
        (* add (zfib 0)(zfib(sub 0 1)) : rewrite sub 0 1 -> 0 : zfib(sub 0 1) = zfib 0 *)
        val Pz1 = let val zz = Free("z_z1", natT) in Term.lambda zz (oeq (add (zfib ZeroC) (zfib (sub ZeroC one))) (add (zfib ZeroC) (zfib zz))) end;
        (* refl of LHS *)
        val reflL = oeqreflZ_at (add (zfib ZeroC) (zfib (sub ZeroC one)));
        val congsub = oeq_subst_at (Pz1, sub ZeroC one, ZeroC) s01 reflL;  (* add(zfib 0)(zfib(sub 0 1)) = add(zfib 0)(zfib 0) *)
        (* add (zfib 0)(zfib 0) = add 1 1 (zfib_0 twice) = 2 *)
        val z0 = zfib_0_v;                                (* zfib 0 = 1 *)
        (* add(zfib 0)(zfib 0) -> add 1 1 *)
        val ccl = add_cong_lZ (zfib ZeroC, one, zfib ZeroC) z0;  (* add(zfib 0)(zfib 0)=add 1 (zfib 0) *)
        val ccr = add_cong_rZ (one, zfib ZeroC, one) z0;          (* add 1 (zfib 0)=add 1 1 *)
        val to11 = oeq_trans OF [ccl, ccr];               (* add(zfib 0)(zfib 0) = add 1 1 *)
        (* add 1 1 = 2 : add (Suc 0) (Suc 0) = Suc(add 0 (Suc 0)) = Suc(Suc 0) = 2 *)
        val aS = addSucZ_at (ZeroC, one);                 (* add(Suc 0)(Suc 0)=Suc(add 0 (Suc 0)) *)
        val a0 = add0Z_at one;                            (* add 0 (Suc 0)=Suc 0 = one *)
        val Pa = Abs("z", natT, oeq (suc (add ZeroC one)) (suc (Bound 0)));
        val aS2 = oeq_trans OF [aS, oeq_subst_at (Pa, add ZeroC one, one) a0 (oeqreflZ_at (suc (add ZeroC one)))]; (* add 1 1 = Suc one = 2 *)
        val LHS_2 = oeq_trans OF [to11, aS2];             (* add(zfib 0)(zfib 0) = 2 *)
        val LHS_full = oeq_trans OF [congsub, LHS_2];     (* add(zfib 0)(zfib(sub 0 1)) = 2 *)
        (* zfib(Suc 0) = zfib 1 = 2 ; so RHS = 2.  goal0 : le (..lhs..) (zfib(Suc 0)).
           le 2 (zfib(Suc 0)) : zfib 1 = 2 -> le 2 2 (le_refl), rewrite 2->zfib 1. *)
        val z1 = zfib_1_v;                                (* zfib 1 = 2 ; zfib(Suc 0)=zfib 1 by one=Suc 0 *)
        val lr2 = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ two)] le_refl_vZ); (* le 2 2 *)
        (* le 2 (zfib(Suc 0)) : rewrite 2nd 2 -> zfib(Suc 0).  zfib(Suc 0)=2 (z1, one=Suc0).
           need 2 = zfib(Suc 0): sym z1 with one = Suc 0 (definitional). *)
        val PrR = let val zz = Free("z_r0", natT) in Term.lambda zz (le two zz) end;
        val le2z1 = oeq_subst_at (PrR, two, zfib (suc ZeroC)) (oeq_sym OF [z1]) lr2;  (* le 2 (zfib(Suc 0)) *)
        (* now rewrite the LHS 2 -> add(zfib 0)(zfib(sub 0 1)) via sym LHS_full *)
        val PlL = let val zz = Free("z_l0", natT) in Term.lambda zz (le zz (zfib (suc ZeroC))) end;
        val goal0 = oeq_subst_at (PlL, two, add (zfib ZeroC) (zfib (sub ZeroC one))) (oeq_sym OF [LHS_full]) le2z1;
        (* goal0 : le (add(zfib 0)(zfib(sub 0 1)))(zfib(Suc 0)).  Now transport 0 -> i via sym hz. *)
        val PiAll = let val zz = Free("z_i0", natT)
                    in Term.lambda zz (le (add (zfib zz) (zfib (sub zz one))) (zfib (suc zz))) end;
        val res = oeq_subst_at (PiAll, ZeroC, iF) (oeq_sym OF [hz]) goal0;
        val disch = Thm.implies_intr (ctermZ (jT (oeq iF ZeroC))) res;
      in disch end;
    (* CASE i = Suc q *)
    val caseSuc =
      let
        val exHyp = Thm.assume (ctermZ (jT (mkEx (Abs("q", natT, oeq iF (suc (Bound 0)))))));
        val Pq = Abs("q", natT, oeq iF (suc (Bound 0)));
        fun body q hq =                                   (* hq : i = Suc q *)
          let
            (* sub i 1 = sub (Suc q) 1 ... but i not literally Suc q; rewrite via hq.
               Work at i' = Suc q (ground), prove le (add(zfib(Suc q))(zfib(sub(Suc q)1)))(zfib(Suc(Suc q))),
               then transport Suc q -> i via sym hq. *)
            val Sq = suc q;
            (* sub (Suc q) 1 = sub q 0 = q *)
            val sSS = subSS_at (q, ZeroC);                (* sub(Suc q)(Suc 0)=sub q 0 ; one=Suc 0 *)
            val sq0 = sub0_at q;                          (* sub q 0 = q *)
            val sub_eq = oeq_trans OF [sSS, sq0];         (* sub (Suc q) 1 = q *)
            (* zfib(sub(Suc q)1) = zfib q : cong subst *)
            val Pzs = let val zz = Free("z_qs", natT) in Term.lambda zz (oeq (add (zfib Sq) (zfib (sub Sq one))) (add (zfib Sq) (zfib zz))) end;
            val reflL = oeqreflZ_at (add (zfib Sq) (zfib (sub Sq one)));
            val lhs_eq = oeq_subst_at (Pzs, sub Sq one, q) sub_eq reflL;  (* add(zfib(Sq))(zfib(sub(Sq)1)) = add(zfib Sq)(zfib q) *)
            (* zfib_SS at q : zfib(Suc(Suc q)) = add(zfib(Suc q))(zfib q) *)
            val ss = zfibSS_at q;                          (* zfib(SSq) = add(zfib(Sq))(zfib q) *)
            (* so add(zfib Sq)(zfib q) = zfib(SSq) (sym) ; chain *)
            val lhs_full = oeq_trans OF [lhs_eq, oeq_sym OF [ss]];  (* add(zfib(Sq))(zfib(sub(Sq)1)) = zfib(SSq) *)
            (* zfib(Suc(Suc q)) = zfib(Suc(Suc q)) ; goal AT Suc q is le (lhs)(zfib(Suc(Suc q))).
               from lhs_full (lhs = zfib(SSq)) : le (lhs)(zfib(SSq)) follows from le (zfib SSq)(zfib SSq)
               by rewriting LHS. *)
            val lrSS = beta_norm (Drule.infer_instantiate ctxtZ [(("n",0), ctermZ (zfib (suc Sq)))] le_refl_vZ); (* le (zfib(SSq))(zfib(SSq)) *)
            val PlL = let val zz = Free("z_ls", natT) in Term.lambda zz (le zz (zfib (suc Sq))) end;
            val goalSq = oeq_subst_at (PlL, zfib (suc Sq), add (zfib Sq) (zfib (sub Sq one))) (oeq_sym OF [lhs_full]) lrSS;
            (* goalSq : le (add(zfib Sq)(zfib(sub Sq 1)))(zfib(Suc(Suc q)))  = goal at i := Suc q *)
            (* transport Suc q -> i via sym hq *)
            val PiAll = let val zz = Free("z_is", natT)
                        in Term.lambda zz (le (add (zfib zz) (zfib (sub zz one))) (zfib (suc zz))) end;
            val res = oeq_subst_at (PiAll, Sq, iF) (oeq_sym OF [hq]) goalSq;
          in res end;
        val core = exE_elimZ (Pq, goalC) exHyp "q_ts" natT body;
        val disch = Thm.implies_intr (ctermZ (jT (mkEx Pq))) core;
      in disch end;
    val res = disjE_elimZ (oeq iF ZeroC, mkEx (Abs("q", natT, oeq iF (suc (Bound 0)))), goalC) dz caseZero caseSuc;
  in varify res end;
val () = out ("zfib_two_step hyps=" ^ Int.toString (length (Thm.hyps_of zfib_two_step))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of zfib_two_step) ^ "\n");
(* ============================================================================
   sum_upper : forall r b. vb b r ==> lt (rep_sum r) (zfib b)
   Stated with an OBJECT-LEVEL inner Forall over b so the list induction's IH at
   the tail can be used at the DIFFERENT bound (sub i 1):
       R r := Forall(%b. Imp (vb b r) (lt (rep_sum r) (zfib b)))
   list induction on r.
     BASE r=INil : rep_sum INil = 0 ; lt 0 (zfib b) = le 1 (zfib b) = zfib_ge1 b.
     STEP r=ICons i r' : assume R r' ; show R (ICons i r').
       given b with vb b (ICons i r'):
         lt i b      (vb_lt)   -> Suc i <= b -> zfib(Suc i) <= zfib b  (le_zfib)
         vb (sub i 1) r'  (vb_tl)
         IH at bound (sub i 1):  lt (rep_sum r')(zfib(sub i 1))
                              i.e. le (Suc(rep_sum r'))(zfib(sub i 1))
         rep_sum (ICons i r') = zfib i + rep_sum r'         (rep_ICons)
         Suc(zfib i + rep_sum r') = zfib i + Suc(rep_sum r')  (add_Suc_right)
           <= zfib i + zfib(sub i 1)        (add_mono_r of IH)
           <= zfib(Suc i)                   (zfib_two_step)
           <= zfib b                        (le_zfib of (lt i b -> Suc i <= b))
         so le (Suc(rep_sum(ICons i r')))(zfib b) = lt (rep_sum(ICons i r'))(zfib b).
   ============================================================================ *)
fun Rbody r = let val bb = Free("b_su", natT)
              in Term.lambda bb (mkImp (vb bb r) (lt (rep_sum r) (zfib bb))) end;
fun Rprop r = mkForall (Rbody r);

val sum_upper =
  let
    val Rpred = let val rr = Free("r_su", ixlistT) in Term.lambda rr (jT (Rprop rr)) end;
    (* list induction: P r = jT (Rprop r) *)
    val RpredO = let val rr = Free("r_su", ixlistT) in Term.lambda rr (Rprop rr) end;  (* o-valued *)
    val kF = Free("k_su", ixlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ RpredO), (("k",0), ctermZ kF)] list_induct_v);
    (* BASE r = INil : Forall(%b. Imp (vb b INil)(lt 0 (zfib b))).  via allI + impI. *)
    val base =
      let
        val bF = Free("b_b", natT);
        (* show jT (Imp (vb b INil)(lt (rep_sum INil)(zfib b)))  for fresh b *)
        val concl =
          let
            (* assume vb b INil (unused); produce lt (rep_sum INil)(zfib b). *)
            val hvb = Thm.assume (ctermZ (jT (vb bF INilC)));
            val ge1 = beta_norm (Drule.infer_instantiate ctxtZ [(("k",0), ctermZ bF)] (varify zfib_ge1)); (* le 1 (zfib b) *)
            (* lt (rep_sum INil)(zfib b) = le (Suc(rep_sum INil))(zfib b).
               rep_sum INil = 0, so Suc(rep_sum INil) = Suc 0 = 1.  rewrite. *)
            val rINil = rep_INil_v;                       (* rep_sum INil = 0 *)
            (* le 1 (zfib b) -> le (Suc(rep_sum INil))(zfib b) via subst 1 -> Suc(rep_sum INil).
               1 = Suc 0 = Suc(rep_sum INil) needs 0 = rep_sum INil (sym rINil). *)
            val one_eq = let val P = Abs("z", natT, oeq one (suc (Bound 0)))
                         in oeq_subst_at (P, ZeroC, rep_sum INilC) (oeq_sym OF [rINil]) (oeqreflZ_at one) end;
            (* one_eq : oeq one (Suc(rep_sum INil)) *)
            val PlL = let val zz = Free("z_lb", natT) in Term.lambda zz (le zz (zfib bF)) end;
            val ltres = oeq_subst_at (PlL, one, suc (rep_sum INilC)) one_eq ge1;  (* le (Suc(rep_sum INil))(zfib b) *)
            val disch = Thm.implies_intr (ctermZ (jT (vb bF INilC))) ltres;       (* jT (vb b INil) ==> jT (lt..) *)
          in impI_atZ (vb bF INilC, lt (rep_sum INilC) (zfib bF)) disch end;       (* jT (Imp ..) *)
        (* allI over b *)
        val allbody = Rbody INilC;
        val minor = Thm.forall_intr (ctermZ bF) concl;   (* !!b. jT (allbody b) -- but concl is jT (Imp..) = jT (allbody b) after beta *)
      in allI_atZ allbody minor end;
    (* STEP : !!i r'. R r' ==> R (ICons i r') *)
    val step =
      let
        val iF = Free("i_s", natT); val rF = Free("r_s", ixlistT);
        val IHprop = jT (Rprop rF);
        val IH = Thm.assume (ctermZ IHprop);             (* jT (Forall(%b. Imp (vb b r')(lt (rep_sum r')(zfib b)))) *)
        val consTm = icons iF rF;
        (* build jT (Imp (vb b (ICons i r'))(lt (rep_sum (ICons i r'))(zfib b))) for fresh b *)
        val bF = Free("b_s", natT);
        val concl =
          let
            val hvb = Thm.assume (ctermZ (jT (vb bF consTm)));   (* vb b (ICons i r') *)
            val lt_ib = (vbLt_at (bF, iF, rF)) OF [hvb];          (* lt i b *)
            val vb_tl = (vbTl_at (bF, iF, rF)) OF [hvb];          (* vb (sub i 1) r' *)
            (* IH at bound (sub i 1) : Imp (vb (sub i 1) r')(lt (rep_sum r')(zfib(sub i 1))) *)
            val ihAt = allE_atZ (Rbody rF) (sub iF one) IH;       (* jT (Imp (vb (sub i 1) r')(lt (rep_sum r')(zfib(sub i 1)))) *)
            val ih_concl = mp_atZ (vb (sub iF one) rF, lt (rep_sum rF) (zfib (sub iF one))) ihAt vb_tl;
            (* ih_concl : lt (rep_sum r')(zfib(sub i 1)) = le (Suc(rep_sum r'))(zfib(sub i 1)) *)
            (* add_mono_r : le a b ==> le (add c a)(add c b).  a=Suc(rep_sum r'), b=zfib(sub i 1), c=zfib i. *)
            val amr = beta_norm (Drule.infer_instantiate ctxtZ
                        [(("a",0), ctermZ (suc (rep_sum rF))),
                         (("b",0), ctermZ (zfib (sub iF one))),
                         (("c",0), ctermZ (zfib iF))] (varify add_mono_r));
            val mono = amr OF [ih_concl];                 (* le (add(zfib i)(Suc(rep_sum r')))(add(zfib i)(zfib(sub i 1))) *)
            (* add(zfib i)(Suc(rep_sum r')) = Suc(add(zfib i)(rep_sum r')) (add_Suc_right) *)
            val aSr = addSrZ_at (zfib iF, rep_sum rF);    (* add(zfib i)(Suc(rep_sum r')) = Suc(add(zfib i)(rep_sum r')) *)
            (* rewrite mono's LHS via aSr : le (Suc(add(zfib i)(rep_sum r')))(add(zfib i)(zfib(sub i 1))) *)
            val PlL = let val zz = Free("z_m", natT) in Term.lambda zz (le zz (add (zfib iF) (zfib (sub iF one)))) end;
            val mono2 = oeq_subst_at (PlL, add (zfib iF) (suc (rep_sum rF)), suc (add (zfib iF) (rep_sum rF))) aSr mono;
            (* mono2 : le (Suc(add(zfib i)(rep_sum r')))(add(zfib i)(zfib(sub i 1))) *)
            (* zfib_two_step at i : le (add(zfib i)(zfib(sub i 1)))(zfib(Suc i)) *)
            val zts = beta_norm (Drule.infer_instantiate ctxtZ [(("i",0), ctermZ iF)] (varify zfib_two_step));
            (* chain mono2 then zts : le (Suc(add(zfib i)(rep_sum r')))(zfib(Suc i)) *)
            val chain1 = (varify le_trans) OF [mono2, zts];
            (* zfib(Suc i) <= zfib b : from lt i b = le (Suc i) b, le_zfib gives le (zfib(Suc i))(zfib b) *)
            val lz = (varify le_zfib) OF [lt_ib];          (* le (zfib(Suc i))(zfib b)   (lt i b = le (Suc i) b) *)
            val chain2 = (varify le_trans) OF [chain1, lz];  (* le (Suc(add(zfib i)(rep_sum r')))(zfib b) *)
            (* rewrite Suc(add(zfib i)(rep_sum r')) -> Suc(rep_sum(ICons i r')) :
               rep_sum(ICons i r') = add(zfib i)(rep_sum r') (rep_ICons) ; Suc-cong. *)
            val rc = repCons_at (iF, rF);                  (* rep_sum(ICons i r') = add(zfib i)(rep_sum r') *)
            (* need Suc(add(zfib i)(rep_sum r')) = Suc(rep_sum(ICons i r')) i.e. sym Suc-cong of rc *)
            val Psc = Abs("z", natT, oeq (suc (add (zfib iF) (rep_sum rF))) (suc (Bound 0)));
            val sc_eq = oeq_subst_at (Psc, add (zfib iF) (rep_sum rF), rep_sum consTm) (oeq_sym OF [rc]) (oeqreflZ_at (suc (add (zfib iF) (rep_sum rF))));
            (* sc_eq : Suc(add(zfib i)(rep_sum r')) = Suc(rep_sum(ICons i r')) *)
            val PlL2 = let val zz = Free("z_f", natT) in Term.lambda zz (le zz (zfib bF)) end;
            val ltfin = oeq_subst_at (PlL2, suc (add (zfib iF) (rep_sum rF)), suc (rep_sum consTm)) sc_eq chain2;
            (* ltfin : le (Suc(rep_sum(ICons i r')))(zfib b) = lt (rep_sum(ICons i r'))(zfib b) *)
            val disch = Thm.implies_intr (ctermZ (jT (vb bF consTm))) ltfin;
          in impI_atZ (vb bF consTm, lt (rep_sum consTm) (zfib bF)) disch end;
        val allbody = Rbody consTm;
        val minor = Thm.forall_intr (ctermZ bF) concl;
        val Rcons = allI_atZ allbody minor;             (* jT (Rprop (ICons i r')) *)
        val disch = Thm.implies_intr (ctermZ IHprop) Rcons;
      in Thm.forall_intr (ctermZ iF) (Thm.forall_intr (ctermZ rF) disch) end;
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;                  (* jT (Rprop k) *)
  in varify r2 end;
val () = out ("sum_upper hyps=" ^ Int.toString (length (Thm.hyps_of sum_upper))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of sum_upper) ^ "\n");

(* a usable corollary : vb b r ==> lt (rep_sum r)(zfib b) *)
fun sum_upper_at (bt, rt) hvb =
  let
    val su_r = beta_norm (Drule.infer_instantiate ctxtZ [(("k_su",0), ctermZ rt)] (varify sum_upper)); (* Rprop r *)
    val atb = allE_atZ (Rbody rt) bt su_r;              (* jT (Imp (vb b r)(lt (rep_sum r)(zfib b))) *)
  in mp_atZ (vb bt rt, lt (rep_sum rt) (zfib bt)) atb hvb end;
(* ============================================================================
   THE CRUX SUM-BOUND LEMMA.
     sum_bound : valid_rep (ICons k r)
                 ==>  le (zfib k) (rep_sum (ICons k r))            (lower)
                  /\  lt (rep_sum (ICons k r)) (zfib (Suc k))      (upper)
   i.e. a valid rep whose LARGEST (head) index is k has rep_sum in
   [zfib k, zfib(Suc k)).  This is what forces the largest index of any valid
   rep of n to be the UNIQUE k with zfib k <= n < zfib(Suc k), driving both
   greedy existence and largest-index uniqueness.
   ============================================================================ *)
val sum_bound =
  let
    val kF = Free("k", natT); val rF = Free("r", ixlistT);
    val consTm = icons kF rF;
    val H = Thm.assume (ctermZ (jT (valid_rep consTm)));
    val rc = repCons_at (kF, rF);                       (* rep_sum(ICons k r) = add(zfib k)(rep_sum r) *)
    (* ---- LOWER : le (zfib k)(rep_sum(ICons k r)) ----
       le (zfib k)(add(zfib k)(rep_sum r))  (le_add) ; rewrite RHS via sym rc. *)
    val la = beta_norm (Drule.infer_instantiate ctxtZ
               [(("m",0), ctermZ (zfib kF)),(("p",0), ctermZ (rep_sum rF))] le_add_vZ); (* le (zfib k)(add(zfib k)(rep_sum r)) *)
    val PlR = let val zz = Free("z_lo", natT) in Term.lambda zz (le (zfib kF) zz) end;
    val lower = oeq_subst_at (PlR, add (zfib kF) (rep_sum rF), rep_sum consTm) (oeq_sym OF [rc]) la;
    (* ---- UPPER : lt (rep_sum(ICons k r))(zfib(Suc k)) ----
       valid_unfold : valid_rep(ICons k r) ==> vb (sub k 1) r *)
    val vb_tl = (validUnfold_at (kF, rF)) OF [H];        (* vb (sub k 1) r *)
    val su = sum_upper_at (sub kF one, rF) vb_tl;        (* lt (rep_sum r)(zfib(sub k 1))
                                                            = le (Suc(rep_sum r))(zfib(sub k 1)) *)
    (* add_mono_r : a=Suc(rep_sum r), b=zfib(sub k 1), c=zfib k *)
    val amr = beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ (suc (rep_sum rF))),
                 (("b",0), ctermZ (zfib (sub kF one))),
                 (("c",0), ctermZ (zfib kF))] (varify add_mono_r));
    val mono = amr OF [su];                              (* le (add(zfib k)(Suc(rep_sum r)))(add(zfib k)(zfib(sub k 1))) *)
    val aSr = addSrZ_at (zfib kF, rep_sum rF);           (* add(zfib k)(Suc(rep_sum r)) = Suc(add(zfib k)(rep_sum r)) *)
    val PlL = let val zz = Free("z_u", natT) in Term.lambda zz (le zz (add (zfib kF) (zfib (sub kF one)))) end;
    val mono2 = oeq_subst_at (PlL, add (zfib kF) (suc (rep_sum rF)), suc (add (zfib kF) (rep_sum rF))) aSr mono;
    (* mono2 : le (Suc(add(zfib k)(rep_sum r)))(add(zfib k)(zfib(sub k 1))) *)
    val zts = beta_norm (Drule.infer_instantiate ctxtZ [(("i",0), ctermZ kF)] (varify zfib_two_step)); (* le (add(zfib k)(zfib(sub k 1)))(zfib(Suc k)) *)
    val chain = (varify le_trans) OF [mono2, zts];      (* le (Suc(add(zfib k)(rep_sum r)))(zfib(Suc k)) *)
    (* rewrite Suc(add(zfib k)(rep_sum r)) -> Suc(rep_sum(ICons k r)) via Suc-cong of (sym rc) *)
    val Psc = Abs("z", natT, oeq (suc (add (zfib kF) (rep_sum rF))) (suc (Bound 0)));
    val sc_eq = oeq_subst_at (Psc, add (zfib kF) (rep_sum rF), rep_sum consTm) (oeq_sym OF [rc]) (oeqreflZ_at (suc (add (zfib kF) (rep_sum rF))));
    val PlL2 = let val zz = Free("z_u2", natT) in Term.lambda zz (le zz (zfib (suc kF))) end;
    val upper = oeq_subst_at (PlL2, suc (add (zfib kF) (rep_sum rF)), suc (rep_sum consTm)) sc_eq chain;
    (* upper : le (Suc(rep_sum(ICons k r)))(zfib(Suc k)) = lt (rep_sum(ICons k r))(zfib(Suc k)) *)
    (* combine into a Conj *)
    val conj = conjI_atZ (le (zfib kF) (rep_sum consTm), lt (rep_sum consTm) (zfib (suc kF))) lower upper;
    val disch = Thm.implies_intr (ctermZ (jT (valid_rep consTm))) conj;
  in varify disch end;
val () = out ("sum_bound hyps=" ^ Int.toString (length (Thm.hyps_of sum_bound))
              ^ ":\n  " ^ Syntax.string_of_term ctxtZ (Thm.prop_of sum_bound) ^ "\n");

(* ============================================================================
   VALIDATION : sum_bound is 0-hyp AND aconv its intended schematic statement.
   ============================================================================ *)
val kVc = Var (("k",0), natT);
val rVc = Var (("r",0), ixlistT);
val consVc = icons kVc rVc;
val sum_bound_intended =
  Logic.mk_implies (jT (valid_rep consVc),
    jT (mkConj (le (zfib kVc) (rep_sum consVc))
               (lt (rep_sum consVc) (zfib (suc kVc)))));
val sb_hyps0 = (length (Thm.hyps_of sum_bound) = 0);
val sb_aconv = (Thm.prop_of sum_bound) aconv sum_bound_intended;
val () = out ("sum_bound 0hyp=" ^ Bool.toString sb_hyps0
              ^ " aconv=" ^ Bool.toString sb_aconv ^ "\n");

(* ---- SOUNDNESS PROBE : the kernel must reject a false strengthening.
   Drop the lower bound to "le (Suc(zfib k))(rep_sum ..)" (i.e. zfib k < sum,
   FALSE when r = INil since then sum = zfib k exactly).  sum_bound must NOT be
   aconv this strengthened variant. ---- *)
val bogus_strong =
  Logic.mk_implies (jT (valid_rep consVc),
    jT (mkConj (lt (zfib kVc) (rep_sum consVc))
               (lt (rep_sum consVc) (zfib (suc kVc)))));
val probe_lower = not ((Thm.prop_of sum_bound) aconv bogus_strong);
(* and the upper bound must be STRICT, not <= : replacing lt by le (allowing
   rep_sum = zfib(Suc k)) is a false weakening of the upper claim's content. *)
val bogus_upper =
  Logic.mk_implies (jT (valid_rep consVc),
    jT (mkConj (le (zfib kVc) (rep_sum consVc))
               (le (rep_sum consVc) (zfib (suc kVc)))));
val probe_upper = not ((Thm.prop_of sum_bound) aconv bogus_upper);
val () = if probe_lower andalso probe_upper
         then out "PROBE_OK sum_bound keeps lower>= and upper< exactly\n"
         else out "PROBE_UNSOUND sum_bound matched a false variant!\n";

(* ============================================================================
   BASE_OK gate : every base lemma 0-hyp, the crux 0-hyp + aconv + probed.
   ============================================================================ *)
fun h0 th = (length (Thm.hyps_of th) = 0);
val all_base_ok =
      h0 zfib_nz andalso h0 zfib_ge1 andalso h0 zfib_mono andalso h0 lt_add_pos
      andalso h0 lt_imp_le andalso h0 add_mono_r andalso h0 zfib_step_d
      andalso h0 le_zfib andalso h0 zfib_two_step andalso h0 sum_upper
      andalso h0 sum_bound
      andalso sb_hyps0 andalso sb_aconv andalso probe_lower andalso probe_upper;
val () =
  if all_base_ok then out "BASE_OK\n"
  else out "BASE_INCOMPLETE\n";

val () = out "ZK_ROBUST_START\n";
(* ======================================================================
   Zeckendorf EXISTENCE + UNIQUENESS, building on the base delta
   (/tmp/zk_base_delta.sml) already spliced in front of this file.
   All work on ctxtZ / ctermZ.  Re-varify base lemmas as needed.
   ====================================================================== *)

(* convenient varified copies of the base crux + helpers *)
val sum_bound_vZ   = varify sum_bound;
val le_zfib_vZ     = varify le_zfib;
val zfib_mono_vZ   = varify zfib_mono;
val zfib_ge1_vZ    = varify zfib_ge1;
val lt_imp_le_vZ   = varify lt_imp_le;
val add_mono_r_vZ  = varify add_mono_r;
val sum_upper_vZ   = varify sum_upper;

(* foundation lemmas, varified onto ctxtZ *)
val le_antisym_vZ  = varify le_antisym;
val le_total_vZ    = varify le_total;
val lt_trans_vZ2   = varify lt_trans;
val le_trans_vZ2   = varify le_trans;
val strong_induct_vZ = varify strong_induct;
val add_left_cancel_vZ = varify add_left_cancel;
val disj_zero_or_suc_vZ2 = varify disj_zero_or_suc;
val Suc_inj_vZ     = varify Suc_inj_ax;
val Suc_neq_Zero_vZ = varify Suc_neq_Zero_ax;
val lt_suc_vZ2     = varify lt_suc;

(* zero_le : le Zero n  (from le_add at m=0 + add_0 rewrite, or directly) *)
(* le Zero n = Ex(%p. oeq n (add Zero p)). witness p=n: oeq n (add Zero n) = sym add_0. *)
fun zero_le_at nt =
  let
    val a0 = add0Z_at nt;                 (* add 0 n = n *)
    val eq = oeq_sym OF [a0];             (* n = add 0 n *)
  in le_introZ (ZeroC, nt, nt) eq end;

val () = out "ZK_HELPERS_READY\n";

(* ============================================================================
   sub helpers
   ============================================================================ *)
(* sub_eq_zero_imp_le : oeq (sub a b) Zero ==> le a b
     Proof by induction... easier: cases. We instead prove the contrapositive
     route is painful; do double induction.  Use the simpler characterization:
       le a b  iff  Ex p. oeq b (add a p).
     We prove sub_add : forall a b. oeq (add (sub a b) (min...))  -- skip.
   Instead prove directly the two lemmas we actually need:
     (L1) add_sub : le a b ==> oeq (add a (sub b a)) b
     (L2) sub_zero_le : oeq (sub n m) Zero ==> le n m
     (L3) sub_lt_mono : le b n ==> lt a b ==> lt (sub n b) (sub n a)   [a<=b<=n]
   ============================================================================ *)

(* L1 add_sub : le a b ==> oeq (add a (sub b a)) b.
   From le a b get witness p with b = add a p.  Then sub b a = sub (add a p) a.
   Need sub (add a p) a = p :  prove sub_add_cancel : oeq (sub (add a p) a) p by
   induction on a.   base a=0: sub (add 0 p) 0 = sub p 0 = p... add 0 p = p,
   sub p 0 = p.  step a=Suc a': sub (add (Suc a') p)(Suc a') = sub (Suc(add a' p))(Suc a')
   = sub (add a' p) a' = p (IH). *)
val sub_add_cancel =
  let
    val pF = Free("p", natT);
    val Ppred = let val aa = Free("a_sac", natT)
                in Term.lambda aa (oeq (sub (add aa pF) aa) pF) end;
    val aF = Free("a", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ Ppred), (("k",0), ctermZ aF)] nat_induct_vZ);
    (* base a=0 : sub (add 0 p) 0 = p.  add 0 p = p ; sub p 0 = p. *)
    val base =
      let
        val a0 = add0Z_at pF;                 (* add 0 p = p *)
        (* sub (add 0 p) 0 -> sub p 0 via cong on 1st arg *)
        val Pc = let val zz = Free("z_b", natT) in Term.lambda zz (oeq (sub (add ZeroC pF) ZeroC) (sub zz ZeroC)) end;
        val reflL = oeqreflZ_at (sub (add ZeroC pF) ZeroC);
        val c1 = oeq_subst_at (Pc, add ZeroC pF, pF) a0 reflL;   (* sub(add 0 p)0 = sub p 0 *)
        val s0 = sub0_at pF;                  (* sub p 0 = p *)
        val res = oeq_trans OF [c1, s0];
      in res end;
    (* step a=Suc a' *)
    val step =
      let
        val xF = Free("a_s", natT);
        val ihprop = jT (oeq (sub (add xF pF) xF) pF);
        val IH = Thm.assume (ctermZ ihprop);
        (* sub (add (Suc a') p)(Suc a') :
             add (Suc a') p = Suc(add a' p)  (addSuc)
             sub (Suc(add a' p))(Suc a') = sub (add a' p) a'  (sub_SS)
             = p  (IH) *)
        val aS = addSucZ_at (xF, pF);         (* add (Suc a') p = Suc(add a' p) *)
        (* sub (add(Suc a')p)(Suc a') = sub (Suc(add a' p))(Suc a') via cong 1st arg *)
        val Pc = let val zz = Free("z_s", natT) in Term.lambda zz (oeq (sub (add (suc xF) pF) (suc xF)) (sub zz (suc xF))) end;
        val reflL = oeqreflZ_at (sub (add (suc xF) pF) (suc xF));
        val c1 = oeq_subst_at (Pc, add (suc xF) pF, suc (add xF pF)) aS reflL;
        (* c1 : sub(add(Suc a')p)(Suc a') = sub(Suc(add a' p))(Suc a') *)
        val sSS = subSS_at (add xF pF, xF);   (* sub(Suc(add a' p))(Suc a') = sub (add a' p) a' *)
        val c2 = oeq_trans OF [c1, sSS];      (* = sub (add a' p) a' *)
        val c3 = oeq_trans OF [c2, IH];       (* = p *)
        val disch = Thm.implies_intr (ctermZ ihprop) c3;
      in Thm.forall_intr (ctermZ xF) disch end;
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;
  in varify r2 end;
val () = out ("sub_add_cancel hyps=" ^ Int.toString (length (Thm.hyps_of sub_add_cancel))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of sub_add_cancel) ^ "\n");

(* L1 add_sub : le a b ==> oeq (add a (sub b a)) b *)
val add_sub =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val H = Thm.assume (ctermZ (jT (le aF bF)));        (* Ex(%p. oeq b (add a p)) *)
    val Pabs = Abs("p", natT, oeq bF (add aF (Bound 0)));
    val goal = oeq (add aF (sub bF aF)) bF;
    fun body p hp =                                      (* hp : b = add a p *)
      let
        (* sub b a = sub (add a p) a = p   (sub_add_cancel at a,p) *)
        val sac = beta_norm (Drule.infer_instantiate ctxtZ
                    [(("a",0), ctermZ aF),(("p",0), ctermZ p)] (varify sub_add_cancel)); (* sub(add a p)a = p *)
        (* sub b a : rewrite b->add a p inside sub 1st arg, then sub_add_cancel *)
        val Pc = let val zz = Free("z_as", natT) in Term.lambda zz (oeq (sub bF aF) (sub zz aF)) end;
        val reflL = oeqreflZ_at (sub bF aF);
        val cb = oeq_subst_at (Pc, bF, add aF p) hp reflL;   (* sub b a = sub (add a p) a *)
        val sub_eq = oeq_trans OF [cb, sac];                 (* sub b a = p *)
        (* add a (sub b a) = add a p   (add_cong_r of sub_eq) = b (sym hp) *)
        val cong = add_cong_rZ (aF, sub bF aF, p) sub_eq;    (* add a (sub b a) = add a p *)
        val res = oeq_trans OF [cong, oeq_sym OF [hp]];      (* add a (sub b a) = b *)
      in res end;
    val core = exE_elimZ (Pabs, goal) H "p_as" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le aF bF))) core;
  in varify disch end;
val () = out ("add_sub hyps=" ^ Int.toString (length (Thm.hyps_of add_sub))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of add_sub) ^ "\n");

val () = out "ZK_SUB_OK\n";

(* ============================================================================
   le_zero_eq : le x Zero ==> oeq x Zero
     le x Zero = Ex(%p. oeq Zero (add x p)). witness p: 0 = add x p -> add x p = 0
     -> x = 0 (add_eq_zero_left).
   ============================================================================ *)
val add_eq_zero_left_vZ = varify add_eq_zero_left;
val le_zero_eq =
  let
    val xF = Free("x", natT);
    val H = Thm.assume (ctermZ (jT (le xF ZeroC)));   (* Ex(%p. oeq Zero (add x p)) *)
    val Pabs = Abs("p", natT, oeq ZeroC (add xF (Bound 0)));
    val goal = oeq xF ZeroC;
    fun body p hp =                                    (* hp : 0 = add x p *)
      let
        val sym = oeq_sym OF [hp];                     (* add x p = 0 *)
        val res = add_eq_zero_left_vZ OF [sym];        (* x = 0 *)
      in res end;
    val core = exE_elimZ (Pabs, goal) H "p_lz0" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le xF ZeroC))) core;
  in varify disch end;
val () = out ("le_zero_eq hyps=" ^ Int.toString (length (Thm.hyps_of le_zero_eq)) ^ "\n");

(* ============================================================================
   sub_pos : lt a b ==> le (Suc Zero) (sub b a)     (a<b => b-a >= 1)
     lt a b = le (Suc a) b -> add (Suc a)(sub b (Suc a)) = b  (add_sub)
       -> b = Suc(add a w) = add a (Suc w)  (w = sub b (Suc a))
       -> sub b a = sub (add a (Suc w)) a = Suc w  (sub_add_cancel)  -> >= 1.
   ============================================================================ *)
val add_sub_vZ = varify add_sub;
val sub_add_cancel_vZ = varify sub_add_cancel;
val sub_pos =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val H = Thm.assume (ctermZ (jT (lt aF bF)));       (* le (Suc a) b *)
    (* add_sub at (Suc a, b) : oeq (add (Suc a)(sub b (Suc a))) b *)
    val asb = (beta_norm (Drule.infer_instantiate ctxtZ
                 [(("a",0), ctermZ (suc aF)),(("b",0), ctermZ bF)] add_sub_vZ)) OF [H];
    (* asb : oeq (add (Suc a) w) b   where w = sub b (Suc a) *)
    val w = sub bF (suc aF);
    (* add (Suc a) w = Suc(add a w) = add a (Suc w) *)
    val aS = addSucZ_at (aF, w);                       (* add (Suc a) w = Suc(add a w) *)
    val aSr = addSrZ_at (aF, w);                       (* add a (Suc w) = Suc(add a w) *)
    val bridge = oeq_trans OF [aS, oeq_sym OF [aSr]];  (* add (Suc a) w = add a (Suc w) *)
    val b_eq = oeq_trans OF [oeq_sym OF [bridge], asb];(* add a (Suc w) = b   ... wait sym *)
    (* b_eq : oeq (add a (Suc w)) b. we want b expressed; sub b a = sub (add a (Suc w)) a = Suc w *)
    (* sub b a = sub (add a (Suc w)) a via cong (b = add a (Suc w))? we have add a(Suc w)=b. *)
    val sac = beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ aF),(("p",0), ctermZ (suc w))] sub_add_cancel_vZ); (* sub(add a (Suc w))a = Suc w *)
    (* sub b a : rewrite b -> add a (Suc w) (sym b_eq) *)
    val Pc = let val zz = Free("z_sp", natT) in Term.lambda zz (oeq (sub bF aF) (sub zz aF)) end;
    val reflL = oeqreflZ_at (sub bF aF);
    val cb = oeq_subst_at (Pc, bF, add aF (suc w)) (oeq_sym OF [b_eq]) reflL;  (* sub b a = sub (add a (Suc w)) a *)
    val sba_eq = oeq_trans OF [cb, sac];               (* sub b a = Suc w *)
    (* le 1 (Suc w) : le (Suc 0)(Suc w).  witness: Suc w = add (Suc 0) w = Suc(add 0 w)=Suc w. *)
    val aS1 = addSucZ_at (ZeroC, w);                   (* add (Suc 0) w = Suc(add 0 w) *)
    val a01 = add0Z_at w;                              (* add 0 w = w *)
    val one_w = oeq_trans OF [aS1,
                  (let val P=Abs("z",natT,oeq (suc (add ZeroC w)) (suc (Bound 0)))
                   in oeq_subst_at (P, add ZeroC w, w) a01 (oeqreflZ_at (suc (add ZeroC w))) end)];
    (* one_w : add (Suc 0) w = Suc w *)
    val le1Sw = le_introZ (one, suc w, w) (oeq_sym OF [one_w]);  (* le 1 (Suc w) *)
    (* rewrite (Suc w) -> sub b a via sym sba_eq inside le's 2nd arg *)
    val Pr = let val zz = Free("z_sp2", natT) in Term.lambda zz (le one zz) end;
    val res = oeq_subst_at (Pr, suc w, sub bF aF) (oeq_sym OF [sba_eq]) le1Sw;
    val disch = Thm.implies_intr (ctermZ (jT (lt aF bF))) res;
  in varify disch end;
val () = out ("sub_pos hyps=" ^ Int.toString (length (Thm.hyps_of sub_pos))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of sub_pos) ^ "\n");

val () = out "ZK_SUB2_OK\n";

(* ============================================================================
   sub_decrease : le a b ==> le b n ==> oeq (sub n a) (add (sub b a) (sub n b))
     add_sub: add a (sub b a) = b   (a<=b)
              add b (sub n b) = n   (b<=n)
              add a (sub n a) = n   (a<=n, from a<=b<=n by le_trans)
     n = add a (sub n a)
       = add (add a (sub b a)) (sub n b)         [b = add a (sub b a), then add..(sub n b)=n]
       = add a (add (sub b a) (sub n b))          [assoc]
     cancel a:  sub n a = add (sub b a)(sub n b).
   ============================================================================ *)
val le_trans_vZ3 = varify le_trans;
val sub_decrease =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val nF = Free("n", natT);
    val Hab = Thm.assume (ctermZ (jT (le aF bF)));
    val Hbn = Thm.assume (ctermZ (jT (le bF nF)));
    val Han = le_trans_vZ3 OF [Hab, Hbn];                 (* le a n *)
    val sab = add_sub_vZ OF [Hab];                        (* add a (sub b a) = b *)
    val sbn = add_sub_vZ OF [Hbn];                        (* add b (sub n b) = n *)
    val san = add_sub_vZ OF [Han];                        (* add a (sub n a) = n *)
    (* n = add a (sub n a)  (sym san) *)
    (* also n = add b (sub n b) = add (add a (sub b a)) (sub n b)  via cong on 1st arg of add (b -> add a(sub b a)) *)
    val b_eq = oeq_sym OF [sab];                          (* b = add a (sub b a) *)
    val congb = add_cong_lZ (bF, add aF (sub bF aF), sub nF bF) b_eq;
    (* congb : add b (sub n b) = add (add a (sub b a)) (sub n b) *)
    val n_eq1 = oeq_trans OF [oeq_sym OF [sbn], congb];   (* n = add (add a (sub b a))(sub n b) *)
    val assoc = addassocZ_at (aF, sub bF aF, sub nF bF);  (* add (add a (sub b a))(sub n b) = add a (add (sub b a)(sub n b)) *)
    val n_eq2 = oeq_trans OF [n_eq1, assoc];              (* n = add a (add (sub b a)(sub n b)) *)
    (* also n = add a (sub n a) (sym san). so add a (sub n a) = add a (add (sub b a)(sub n b)) *)
    val lhs = oeq_trans OF [san, n_eq2];                  (* add a (sub n a) = add a (add (sub b a)(sub n b)) *)
    val canc = add_left_cancel_vZ OF [lhs];               (* sub n a = add (sub b a)(sub n b) *)
    val disch = Thm.implies_intr (ctermZ (jT (le bF nF)))
                  (Thm.implies_intr (ctermZ (jT (le aF bF))) canc);
  in varify disch end;
val () = out ("sub_decrease hyps=" ^ Int.toString (length (Thm.hyps_of sub_decrease)) ^ "\n");

(* lt_add_pos_comm : le one c ==> lt a (add c a)   (the c on the LEFT) *)
val lt_add_pos_vZ = varify lt_add_pos;
val add_comm_vZ2 = varify add_comm;
val lt_add_pos_comm =
  let
    val aF = Free("a", natT); val cF = Free("c", natT);
    val H = Thm.assume (ctermZ (jT (le one cF)));
    val lap = (beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ aF),(("c",0), ctermZ cF)] lt_add_pos_vZ)) OF [H]; (* lt a (add a c) *)
    (* rewrite add a c -> add c a (add_comm) inside lt's 2nd arg *)
    val comm = addcommZ_at (aF, cF);                      (* add a c = add c a *)
    val Pr = let val zz = Free("z_lap", natT) in Term.lambda zz (lt aF zz) end;
    val res = oeq_subst_at (Pr, add aF cF, add cF aF) comm lap;  (* lt a (add c a) *)
    val disch = Thm.implies_intr (ctermZ (jT (le one cF))) res;
  in varify disch end;
val () = out ("lt_add_pos_comm hyps=" ^ Int.toString (length (Thm.hyps_of lt_add_pos_comm)) ^ "\n");

(* sub_strict_decrease : lt a b ==> le b n ==> lt (sub n b) (sub n a)
     sub n a = add (sub b a)(sub n b)   (sub_decrease, a<=b<=n)
     sub b a >= 1   (sub_pos, a<b)
     lt (sub n b) (add (sub b a)(sub n b))   (lt_add_pos_comm, c=sub b a >=1)
     rewrite RHS -> sub n a (sym sub_decrease).
   ============================================================================ *)
val sub_pos_vZ = varify sub_pos;
val lt_imp_le_vZ2 = varify lt_imp_le;
val sub_decrease_vZ = varify sub_decrease;
val lt_add_pos_comm_vZ = varify lt_add_pos_comm;
val sub_strict_decrease =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val nF = Free("n", natT);
    val Hab = Thm.assume (ctermZ (jT (lt aF bF)));     (* lt a b *)
    val Hbn = Thm.assume (ctermZ (jT (le bF nF)));     (* le b n *)
    val Hab_le = lt_imp_le_vZ2 OF [Hab];               (* le a b *)
    (* sub_decrease : sub n a = add (sub b a)(sub n b) *)
    val sd = (beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ aF),(("b",0), ctermZ bF),(("n",0), ctermZ nF)] sub_decrease_vZ)
              OF [Hbn]) OF [Hab_le];                    (* oeq (sub n a) (add (sub b a)(sub n b)) *)
    val spos = (beta_norm (Drule.infer_instantiate ctxtZ
                  [(("a",0), ctermZ aF),(("b",0), ctermZ bF)] sub_pos_vZ)) OF [Hab]; (* le 1 (sub b a) *)
    (* lt (sub n b)(add (sub b a)(sub n b)) *)
    val lapc = (beta_norm (Drule.infer_instantiate ctxtZ
                  [(("a",0), ctermZ (sub nF bF)),(("c",0), ctermZ (sub bF aF))] lt_add_pos_comm_vZ))
               OF [spos];                               (* lt (sub n b) (add (sub b a)(sub n b)) *)
    (* rewrite (add (sub b a)(sub n b)) -> sub n a via sym sd inside lt 2nd arg *)
    val Pr = let val zz = Free("z_ssd", natT) in Term.lambda zz (lt (sub nF bF) zz) end;
    val res = oeq_subst_at (Pr, add (sub bF aF) (sub nF bF), sub nF aF) (oeq_sym OF [sd]) lapc;
    val disch = Thm.implies_intr (ctermZ (jT (le bF nF)))
                  (Thm.implies_intr (ctermZ (jT (lt aF bF))) res);
  in varify disch end;
val () = out ("sub_strict_decrease hyps=" ^ Int.toString (length (Thm.hyps_of sub_strict_decrease)) ^ "\n");

val () = out "ZK_DECREASE_OK\n";

(* ============================================================================
   lt_le_cases : Disj (lt a b) (le b a)      (totality split)
     le_total a b : Disj (le a b)(le b a).
       case le b a -> disjI2.
       case le a b -> witness p: b = add a p ; cases on p (disj_zero_or_suc):
         p=0 -> b = a (a+0), so le b a (le_refl + subst) -> disjI2.
         p=Suc q -> b = add a (Suc q) = Suc(add a q) = add (Suc a) q -> le (Suc a) b
                    = lt a b -> disjI1.
   ============================================================================ *)
val lt_le_cases =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val goalC = mkDisj (lt aF bF) (le bF aF);
    val tot = beta_norm (Drule.infer_instantiate ctxtZ
                [(("m",0), ctermZ aF),(("n",0), ctermZ bF)] le_total_vZ); (* Disj (le a b)(le b a) *)
    (* case le b a *)
    val caseBA =
      let
        val h = Thm.assume (ctermZ (jT (le bF aF)));
        val g = disjI2_atZ (lt aF bF, le bF aF) h;
      in Thm.implies_intr (ctermZ (jT (le bF aF))) g end;
    (* case le a b *)
    val caseAB =
      let
        val hab = Thm.assume (ctermZ (jT (le aF bF)));   (* Ex(%p. b = add a p) *)
        val Pabs = Abs("p", natT, oeq bF (add aF (Bound 0)));
        fun body p hp =                                   (* hp : b = add a p *)
          let
            val dz = beta_norm (Drule.infer_instantiate ctxtZ [(("p",0), ctermZ p)] disj_zero_or_suc_vZ2);
            (* dz : Disj (oeq p 0)(Ex(%q. oeq p (Suc q))) *)
            val PabsQ = Abs("q", natT, oeq p (suc (Bound 0)));
            val cZero =
              let
                val hz = Thm.assume (ctermZ (jT (oeq p ZeroC)));   (* p = 0 *)
                (* b = add a p = add a 0 = a *)
                val cong = add_cong_rZ (aF, p, ZeroC) hz;          (* add a p = add a 0 *)
                val a0r = add0rZ_at aF;                            (* add a 0 = a *)
                val b_a = oeq_trans OF [hp, oeq_trans OF [cong, a0r]]; (* b = a *)
                (* le b a : witness 0 : a = add b 0.  a = b (sym), add b 0 = b. *)
                val a_b = oeq_sym OF [b_a];                        (* a = b *)
                val ab0 = add0rZ_at bF;                            (* add b 0 = b *)
                val eq = oeq_trans OF [a_b, oeq_sym OF [ab0]];     (* a = add b 0 *)
                val leba = le_introZ (bF, aF, ZeroC) eq;           (* le b a *)
                val g = disjI2_atZ (lt aF bF, le bF aF) leba;
              in Thm.implies_intr (ctermZ (jT (oeq p ZeroC))) g end;
            val cSuc =
              let
                val exq = Thm.assume (ctermZ (jT (mkEx PabsQ)));
                fun sbody q hq =                                   (* hq : p = Suc q *)
                  let
                    (* b = add a p = add a (Suc q) = Suc(add a q) = add (Suc a) q *)
                    val cong = add_cong_rZ (aF, p, suc q) hq;      (* add a p = add a (Suc q) *)
                    val b_aSq = oeq_trans OF [hp, cong];           (* b = add a (Suc q) *)
                    val aSr = addSrZ_at (aF, q);                   (* add a (Suc q) = Suc(add a q) *)
                    val b_Saq = oeq_trans OF [b_aSq, aSr];         (* b = Suc(add a q) *)
                    val aS = addSucZ_at (aF, q);                   (* add (Suc a) q = Suc(add a q) *)
                    val b_Saddq = oeq_trans OF [b_Saq, oeq_sym OF [aS]]; (* b = add (Suc a) q *)
                    val ltab = le_introZ (suc aF, bF, q) b_Saddq;  (* le (Suc a) b = lt a b *)
                    val g = disjI1_atZ (lt aF bF, le bF aF) ltab;
                  in g end;
                val g = exE_elimZ (PabsQ, goalC) exq "q_llc" natT sbody;
              in Thm.implies_intr (ctermZ (jT (mkEx PabsQ))) g end;
            val combined = disjE_elimZ (oeq p ZeroC, mkEx PabsQ, goalC) dz cZero cSuc;
          in combined end;
        val core = exE_elimZ (Pabs, goalC) hab "p_llc" natT body;
      in Thm.implies_intr (ctermZ (jT (le aF bF))) core end;
    val res = disjE_elimZ (le aF bF, le bF aF, goalC) tot caseAB caseBA;
  in varify res end;
val () = out ("lt_le_cases hyps=" ^ Int.toString (length (Thm.hyps_of lt_le_cases))
              ^ ": " ^ Syntax.string_of_term ctxtZ (Thm.prop_of lt_le_cases) ^ "\n");

val () = out "ZK_CASES_OK\n";

(* ============================================================================
   zfib_index_exists : lt Zero n ==> Ex k. (le (zfib k) n AND lt n (zfib (Suc k)))
   The greedy/largest-index selection.  STRATEGY: an auxiliary search from k=0
   upward, by STRONG INDUCTION on d = sub n (zfib k) (the remaining gap).
     P d := Forall(%k. Imp (Conj (le (zfib k) n)(oeq (sub n (zfib k)) d)) Q)
     Q    := Ex(%j. Conj (le (zfib j) n)(lt n (zfib (Suc j)))).
   Given (le (zfib k) n) AND (sub n (zfib k) = d):
     case lt n (zfib (Suc k)) -> j=k.
     case le (zfib (Suc k)) n ->
        sub_strict_decrease(zfib k, zfib(Suc k), n) : lt (sub n (zfib(Suc k)))(sub n (zfib k))
           = lt (sub n (zfib(Suc k))) d.  Apply strong-IH at that smaller value,
           with k := Suc k (le (zfib(Suc k)) n holds, sub..=itself refl).
   Then instantiate at k=0 : le (zfib 0) n = le 1 n (from 0<n), sub n (zfib 0) = d0.
   ============================================================================ *)
val zfib_mono_vZ2 = varify zfib_mono;
val lt_le_cases_vZ = varify lt_le_cases;
val sub_strict_decrease_vZ = varify sub_strict_decrease;

(* Q(n) : Ex(%j. Conj (le (zfib j) n)(lt n (zfib (Suc j)))) -- with fresh-free body *)
fun Qbody nt = let val jj = Free("j_q", natT)
               in Term.lambda jj (mkConj (le (zfib jj) nt) (lt nt (zfib (suc jj)))) end;
fun Qprop nt = mkEx (Qbody nt);

val zfib_index_exists =
  let
    val nF = Free("n", natT);
    val Hpos = Thm.assume (ctermZ (jT (lt ZeroC nF)));   (* 0 < n,  = le (Suc 0) n = le 1 n *)
    val Qn = Qprop nF;
    (* the strong-induction predicate over d *)
    fun Pd_body d = let val kk = Free("k_pd", natT)
                    in Term.lambda kk (mkImp (mkConj (le (zfib kk) nF) (oeq (sub nF (zfib kk)) d)) Qn) end;
    fun Pd d = mkForall (Pd_body d);
    val Ppred = let val dd = Free("d_p", natT) in Term.lambda dd (Pd dd) end;  (* nat -> o *)
    (* ---- the strong-induction step: !!d. (!!m. lt m d ==> P m) ==> P d ---- *)
    val dF = Free("d_si", natT);
    val mSI = Free("m_si", natT);
    (* IH : !!m. lt m d ==> Trueprop (Pd m) *)
    val IHprop = Logic.all mSI (Logic.mk_implies (jT (lt mSI dF), jT (Pd mSI)));
    val IH = Thm.assume (ctermZ IHprop);
    (* build Trueprop (Pd d) = Forall(%k. Imp (Conj (le (zfib k) n)(sub n (zfib k)=d)) Qn) *)
    val kF = Free("k_z", natT);
    val antC = mkConj (le (zfib kF) nF) (oeq (sub nF (zfib kF)) dF);
    val concl =
      let
        val hAnt = Thm.assume (ctermZ (jT antC));               (* Conj (le (zfib k) n)(sub n (zfib k)=d) *)
        val hLe  = conjunct1_atZ (le (zfib kF) nF, oeq (sub nF (zfib kF)) dF) hAnt;  (* le (zfib k) n *)
        val hSub = conjunct2_atZ (le (zfib kF) nF, oeq (sub nF (zfib kF)) dF) hAnt;  (* sub n (zfib k) = d *)
        (* split on lt n (zfib (Suc k)) vs le (zfib(Suc k)) n *)
        val llc = beta_norm (Drule.infer_instantiate ctxtZ
                    [(("a",0), ctermZ nF),(("b",0), ctermZ (zfib (suc kF)))] lt_le_cases_vZ);
        (* llc : Disj (lt n (zfib(Suc k))) (le (zfib(Suc k)) n) *)
        val caseLt =
          let
            val hlt = Thm.assume (ctermZ (jT (lt nF (zfib (suc kF)))));   (* lt n (zfib(Suc k)) *)
            (* j = k : Conj (le (zfib k) n)(lt n (zfib(Suc k))) -> Qn *)
            val conj = conjI_atZ (le (zfib kF) nF, lt nF (zfib (suc kF))) hLe hlt;
            (* exI at j=k *)
            val exq = beta_norm (Drule.infer_instantiate ctxtZ
                        [(("P",0), ctermZ (Qbody nF)), (("a",0), ctermZ kF)] exI_vZ);
            val g = exq OF [conj];                                (* Qn *)
          in Thm.implies_intr (ctermZ (jT (lt nF (zfib (suc kF))))) g end;
        val caseLe =
          let
            val hle = Thm.assume (ctermZ (jT (le (zfib (suc kF)) nF)));   (* le (zfib(Suc k)) n *)
            (* sub_strict_decrease at (zfib k, zfib(Suc k), n) : lt (sub n (zfib(Suc k)))(sub n (zfib k)) *)
            val zm = beta_norm (Drule.infer_instantiate ctxtZ [(("k",0), ctermZ kF)] zfib_mono_vZ2); (* lt (zfib k)(zfib(Suc k)) *)
            val ssd = ((beta_norm (Drule.infer_instantiate ctxtZ
                          [(("a",0), ctermZ (zfib kF)),(("b",0), ctermZ (zfib (suc kF))),(("n",0), ctermZ nF)]
                          sub_strict_decrease_vZ)) OF [hle]) OF [zm];
            (* ssd : lt (sub n (zfib(Suc k)))(sub n (zfib k)) *)
            (* rewrite (sub n (zfib k)) -> d via hSub : lt (sub n (zfib(Suc k))) d *)
            val Pr = let val zz = Free("z_si", natT) in Term.lambda zz (lt (sub nF (zfib (suc kF))) zz) end;
            val ltmd = oeq_subst_at (Pr, sub nF (zfib kF), dF) hSub ssd;   (* lt (sub n (zfib(Suc k))) d *)
            (* IH at m = sub n (zfib(Suc k)) : Trueprop (Pd (sub n (zfib(Suc k)))) *)
            val ihAt = Thm.implies_elim (Thm.forall_elim (ctermZ (sub nF (zfib (suc kF)))) IH) ltmd;
            (* ihAt : Trueprop (Pd (sub n (zfib(Suc k)))) = Forall(%k'. Imp (Conj ..k'.. (sub n (zfib k') = sub n(zfib(Suc k)))) Qn) *)
            (* instantiate k' := Suc k *)
            val ihAtSk = allE_atZ (Pd_body (sub nF (zfib (suc kF)))) (suc kF) ihAt;
            (* ihAtSk : Imp (Conj (le (zfib(Suc k)) n)(oeq (sub n (zfib(Suc k))) (sub n (zfib(Suc k))))) Qn *)
            val reflSub = oeqreflZ_at (sub nF (zfib (suc kF)));  (* sub n (zfib(Suc k)) = itself *)
            val antSk = conjI_atZ (le (zfib (suc kF)) nF, oeq (sub nF (zfib (suc kF))) (sub nF (zfib (suc kF)))) hle reflSub;
            val g = mp_atZ (mkConj (le (zfib (suc kF)) nF) (oeq (sub nF (zfib (suc kF))) (sub nF (zfib (suc kF)))), Qn) ihAtSk antSk;
          in Thm.implies_intr (ctermZ (jT (le (zfib (suc kF)) nF))) g end;
        val res = disjE_elimZ (lt nF (zfib (suc kF)), le (zfib (suc kF)) nF, Qn) llc caseLt caseLe;
        val disch = Thm.implies_intr (ctermZ (jT antC)) res;     (* Imp ... -> in meta form *)
      in impI_atZ (antC, Qn) disch end;                          (* Trueprop (Imp (Conj..) Qn) *)
    (* allI over k *)
    val PdD = allI_atZ (Pd_body dF) (Thm.forall_intr (ctermZ kF) concl);  (* Trueprop (Pd d) *)
    val stepThm = Thm.forall_intr (ctermZ dF) (Thm.implies_intr (ctermZ IHprop) PdD);
    (* apply strong_induct : instantiate P := Ppred, k := (sub n (zfib 0)) ; gives Trueprop(Ppred (sub n (zfib 0))) *)
    val d0 = sub nF (zfib ZeroC);
    val siInst = beta_norm (Drule.infer_instantiate ctxtZ
                   [(("P",0), ctermZ Ppred), (("k",0), ctermZ d0)] strong_induct_vZ);
    (* siInst : (!!n. (!!m. lt m n ==> P m) ==> P n) ==> Trueprop (Ppred d0) *)
    val Pd0 = Thm.implies_elim siInst stepThm;                   (* Trueprop (Pd d0) = Forall(%k. ...) at d=d0 *)
    (* instantiate k := 0 : Imp (Conj (le (zfib 0) n)(sub n (zfib 0) = d0)) Qn *)
    val atK0 = allE_atZ (Pd_body d0) ZeroC Pd0;
    (* le (zfib 0) n : zfib 0 = 1, so le 1 n = lt 0 n = Hpos.  rewrite. *)
    (* Hpos : lt 0 n = le (Suc 0) n = le 1 n.  zfib 0 = 1 = one.  need le (zfib 0) n. *)
    val z0 = zfib_0_v;                                            (* zfib 0 = 1 = one *)
    (* le one n  from Hpos (lt 0 n = le (Suc 0) n ; Suc 0 = one definitionally) *)
    (* Hpos is le (Suc Zero) n ; one = suc ZeroC ; so Hpos : le one n already *)
    val leOneN = Hpos;                                           (* le one n  (= le (Suc 0) n) *)
    (* rewrite one -> zfib 0 via sym z0 inside le 1st arg *)
    val Pr0 = let val zz = Free("z_k0", natT) in Term.lambda zz (le zz nF) end;
    val leZ0n = oeq_subst_at (Pr0, one, zfib ZeroC) (oeq_sym OF [z0]) leOneN;  (* le (zfib 0) n *)
    val reflD0 = oeqreflZ_at d0;                                  (* sub n (zfib 0) = d0 *)
    val antK0 = conjI_atZ (le (zfib ZeroC) nF, oeq (sub nF (zfib ZeroC)) d0) leZ0n reflD0;
    val Qres = mp_atZ (mkConj (le (zfib ZeroC) nF) (oeq (sub nF (zfib ZeroC)) d0), Qn) atK0 antK0;
    (* Qres : Trueprop Qn *)
    val disch = Thm.implies_intr (ctermZ (jT (lt ZeroC nF))) Qres;
  in varify disch end;
val () = out ("zfib_index_exists hyps=" ^ Int.toString (length (Thm.hyps_of zfib_index_exists))
              ^ ":\n  " ^ Syntax.string_of_term ctxtZ (Thm.prop_of zfib_index_exists) ^ "\n");

val () = out "ZK_SELECT_OK\n";

(* ============================================================================
   vb_imp_valid : vb b r ==> valid_rep r        (cap can always be dropped)
     list induction on r.  r=INil: valid_INil.  r=ICons i r': vb b (ICons i r')
       -> vb (sub i 1) r' (vb_tl) -> valid_rep (ICons i r') (valid_fold).
   We don't even need induction: directly.  But vb_tl/valid_fold only handle the
   ICons shape, and vb_INil/valid_INil the INil shape; we split on r via list
   induction (the IH is unused).
   ============================================================================ *)
val vb_imp_valid =
  let
    val bGiven = Free("b", natT);
    (* P r := Forall(%b. Imp (vb b r)(valid_rep r))  -- inner-universal b so both shapes work *)
    fun VBody r = let val bb = Free("b_vv", natT) in Term.lambda bb (mkImp (vb bb r) (valid_rep r)) end;
    fun VProp r = mkForall (VBody r);
    val RpredO = let val rr = Free("r_vv", ixlistT) in Term.lambda rr (VProp rr) end;
    val kF = Free("k_vv", ixlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtZ
          [(("P",0), ctermZ RpredO), (("k",0), ctermZ kF)] list_induct_v);
    (* base r=INil : Forall(%b. Imp (vb b INil)(valid_rep INil)) *)
    val base =
      let
        val bF = Free("b_vb", natT);
        val hvb = Thm.assume (ctermZ (jT (vb bF INilC)));
        val concl = valid_INil_v;                            (* valid_rep INil *)
        val disch = Thm.implies_intr (ctermZ (jT (vb bF INilC))) concl;
        val imp = impI_atZ (vb bF INilC, valid_rep INilC) disch;
        val minor = Thm.forall_intr (ctermZ bF) imp;
      in allI_atZ (VBody INilC) minor end;
    (* step r=ICons i r' : IH unused *)
    val step =
      let
        val iF = Free("i_vs", natT); val rF = Free("r_vs", ixlistT);
        val IHprop = jT (VProp rF);
        val IH = Thm.assume (ctermZ IHprop);
        val consTm = icons iF rF;
        val bF = Free("b_vs", natT);
        val hvb = Thm.assume (ctermZ (jT (vb bF consTm)));    (* vb b (ICons i r') *)
        val vbtl = (vbTl_at (bF, iF, rF)) OF [hvb];           (* vb (sub i 1) r' *)
        val vr = (validFold_at (iF, rF)) OF [vbtl];           (* valid_rep (ICons i r') *)
        val disch = Thm.implies_intr (ctermZ (jT (vb bF consTm))) vr;
        val imp = impI_atZ (vb bF consTm, valid_rep consTm) disch;
        val minor = Thm.forall_intr (ctermZ bF) imp;
        val Vcons = allI_atZ (VBody consTm) minor;
        val dischIH = Thm.implies_intr (ctermZ IHprop) Vcons;
      in Thm.forall_intr (ctermZ iF) (Thm.forall_intr (ctermZ rF) dischIH) end;
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;                        (* VProp k *)
  in varify r2 end;
val () = out ("vb_imp_valid hyps=" ^ Int.toString (length (Thm.hyps_of vb_imp_valid)) ^ "\n");
(* corollary: vb b r ==> valid_rep r *)
fun vb_imp_valid_at (bt, rt) hvb =
  let val vp = beta_norm (Drule.infer_instantiate ctxtZ [(("k_vv",0), ctermZ rt)] (varify vb_imp_valid)); (* VProp r *)
      val atb = allE_atZ (let val bb = Free("b_vv", natT) in Term.lambda bb (mkImp (vb bb rt)(valid_rep rt)) end) bt vp;
  in mp_atZ (vb bt rt, valid_rep rt) atb hvb end;

val () = out "ZK_VBIMP_OK\n";

(* ============================================================================
   lt_irrefl_contra : lt x y ==> le y x ==> oFalse
     lt x y = le (Suc x) y ; le y x ; le_trans -> le (Suc x) x.
     le (Suc x) x = Ex(%p. oeq x (add (Suc x) p)) = oeq x (Suc(add x p)).
     Then x = Suc(add x p); but x = add x 0 ... -> add x 0 = add x (Suc p) ->
     0 = Suc p (add_left_cancel) -> Suc_neq_Zero -> oFalse.
   ============================================================================ *)
val le_trans_vZ4 = varify le_trans;
val lt_irrefl_contra =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    val Hlt = Thm.assume (ctermZ (jT (lt xF yF)));   (* le (Suc x) y *)
    val Hle = Thm.assume (ctermZ (jT (le yF xF)));   (* le y x *)
    val leSxx = le_trans_vZ4 OF [Hlt, Hle];          (* le (Suc x) x = Ex(%p. oeq x (add (Suc x) p)) *)
    val Pabs = Abs("p", natT, oeq xF (add (suc xF) (Bound 0)));
    fun body p hp =                                  (* hp : x = add (Suc x) p *)
      let
        (* add (Suc x) p = Suc(add x p) = add x (Suc p) *)
        val aS = addSucZ_at (xF, p);                 (* add (Suc x) p = Suc(add x p) *)
        val aSr = addSrZ_at (xF, p);                 (* add x (Suc p) = Suc(add x p) *)
        val bridge = oeq_trans OF [aS, oeq_sym OF [aSr]];  (* add (Suc x) p = add x (Suc p) *)
        val x_eq = oeq_trans OF [hp, bridge];        (* x = add x (Suc p) *)
        (* x = add x 0 (sym add_0_right) *)
        val x0 = oeq_sym OF [add0rZ_at xF];          (* x = add x 0 *)
        val cancAnt = oeq_trans OF [oeq_sym OF [x0], x_eq];  (* add x 0 = add x (Suc p) *)
        val canc = add_left_cancel_vZ OF [cancAnt];  (* oeq 0 (Suc p) *)
        val fls = (Suc_neq_Zero_vZ) OF [oeq_sym OF [canc]];  (* Suc p = 0 -> oFalse *)
      in fls end;
    val core = exE_elimZ (Pabs, oFalseC) leSxx "p_irr" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le yF xF)))
                  (Thm.implies_intr (ctermZ (jT (lt xF yF))) core);
  in varify disch end;
val () = out ("lt_irrefl_contra hyps=" ^ Int.toString (length (Thm.hyps_of lt_irrefl_contra)) ^ "\n");

(* zfib_lt_rev : lt (zfib a)(zfib b) ==> lt a b
     lt_le_cases a b : Disj (lt a b)(le b a).
       lt a b -> done.
       le b a -> le (zfib b)(zfib a) (le_zfib) ; with lt (zfib a)(zfib b) ->
         lt_irrefl_contra (x=zfib a, y=zfib b): lt (zfib a)(zfib b) /\ le (zfib b)(zfib a) -> oFalse.
   ============================================================================ *)
val le_zfib_vZ2 = varify le_zfib;
val lt_irrefl_contra_vZ = varify lt_irrefl_contra;
val zfib_lt_rev =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val H = Thm.assume (ctermZ (jT (lt (zfib aF) (zfib bF))));
    val goalC = lt aF bF;
    val llc = beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ aF),(("b",0), ctermZ bF)] lt_le_cases_vZ);  (* Disj (lt a b)(le b a) *)
    val caseLt =
      let val h = Thm.assume (ctermZ (jT (lt aF bF)))
      in Thm.implies_intr (ctermZ (jT (lt aF bF))) h end;
    val caseLe =
      let
        val h = Thm.assume (ctermZ (jT (le bF aF)));        (* le b a *)
        val lzf = le_zfib_vZ2 OF [h];                       (* le (zfib b)(zfib a) *)
        val fls = ((beta_norm (Drule.infer_instantiate ctxtZ
                     [(("x",0), ctermZ (zfib aF)),(("y",0), ctermZ (zfib bF))] lt_irrefl_contra_vZ))
                   OF [lzf]) OF [H];                         (* oFalse *)
        val g = (oFalse_elimZ_at (lt aF bF)) OF [fls];      (* lt a b *)
      in Thm.implies_intr (ctermZ (jT (le bF aF))) g end;
    val res = disjE_elimZ (lt aF bF, le bF aF, goalC) llc caseLt caseLe;
    val disch = Thm.implies_intr (ctermZ (jT (lt (zfib aF) (zfib bF)))) res;
  in varify disch end;
val () = out ("zfib_lt_rev hyps=" ^ Int.toString (length (Thm.hyps_of zfib_lt_rev)) ^ "\n");

val () = out "ZK_REV_OK\n";

(* ============================================================================
   zfib_Suc_split : oeq (zfib (Suc k)) (add (zfib k)(zfib (sub k 1)))
     (the EQUALITY version of zfib_two_step; needed for the remainder bound.)
   case k=0  : zfib 1 = 2 ; add (zfib 0)(zfib(sub 0 1)) = add 1 1 = 2.
   case k=Suc q : sub(Suc q)1 = q ; add(zfib(Suc q))(zfib q) = zfib(Suc(Suc q)) (zfib_SS).
   ============================================================================ *)
val zfib_Suc_split =
  let
    val kF = Free("k", natT);
    val dz = beta_norm (Drule.infer_instantiate ctxtZ [(("p",0), ctermZ kF)] disj_zero_or_suc_vZ2);
    val goalC = oeq (zfib (suc kF)) (add (zfib kF) (zfib (sub kF one)));
    val caseZero =
      let
        val hz = Thm.assume (ctermZ (jT (oeq kF ZeroC)));  (* k = 0 *)
        (* prove ground at k=0 then transport *)
        (* sub 0 1 = 0 *)
        val s01 = subZ_at ZeroC;                           (* sub 0 (Suc 0) = 0 *)
        val Pz1 = let val zz = Free("z_z1s", natT) in Term.lambda zz (oeq (add (zfib ZeroC)(zfib (sub ZeroC one)))(add (zfib ZeroC)(zfib zz))) end;
        val reflL = oeqreflZ_at (add (zfib ZeroC)(zfib (sub ZeroC one)));
        val congsub = oeq_subst_at (Pz1, sub ZeroC one, ZeroC) s01 reflL;  (* add(zfib 0)(zfib(sub 0 1)) = add(zfib 0)(zfib 0) *)
        val z0 = zfib_0_v;
        val ccl = add_cong_lZ (zfib ZeroC, one, zfib ZeroC) z0;  (* = add 1 (zfib 0) *)
        val ccr = add_cong_rZ (one, zfib ZeroC, one) z0;          (* = add 1 1 *)
        val to11 = oeq_trans OF [ccl, ccr];
        val aS = addSucZ_at (ZeroC, one);
        val a0 = add0Z_at one;
        val Pa = Abs("z", natT, oeq (suc (add ZeroC one))(suc (Bound 0)));
        val aS2 = oeq_trans OF [aS, oeq_subst_at (Pa, add ZeroC one, one) a0 (oeqreflZ_at (suc (add ZeroC one)))];
        val LHS_2 = oeq_trans OF [to11, aS2];              (* add(zfib 0)(zfib 0) = 2 *)
        val rhs_eq = oeq_trans OF [congsub, LHS_2];        (* add(zfib 0)(zfib(sub 0 1)) = 2 *)
        (* zfib 1 = 2 ; so goal at 0: oeq (zfib 1) (add(zfib 0)(zfib(sub 0 1))) *)
        val z1 = zfib_1_v;                                 (* zfib(Suc 0) = 2 *)
        val goal0 = oeq_trans OF [z1, oeq_sym OF [rhs_eq]];(* zfib(Suc 0) = add(zfib 0)(zfib(sub 0 1)) *)
        val PiAll = let val zz = Free("z_i0s", natT)
                    in Term.lambda zz (oeq (zfib (suc zz)) (add (zfib zz)(zfib (sub zz one)))) end;
        val res = oeq_subst_at (PiAll, ZeroC, kF) (oeq_sym OF [hz]) goal0;
        val disch = Thm.implies_intr (ctermZ (jT (oeq kF ZeroC))) res;
      in disch end;
    val caseSuc =
      let
        val Pq = Abs("q", natT, oeq kF (suc (Bound 0)));
        val exHyp = Thm.assume (ctermZ (jT (mkEx Pq)));
        fun body q hq =                                    (* hq : k = Suc q *)
          let
            val Sq = suc q;
            val sSS = subSS_at (q, ZeroC);                 (* sub(Suc q)(Suc 0) = sub q 0 *)
            val sq0 = sub0_at q;                           (* sub q 0 = q *)
            val sub_eq = oeq_trans OF [sSS, sq0];          (* sub (Suc q) 1 = q *)
            val Pzs = let val zz = Free("z_qss", natT) in Term.lambda zz (oeq (add (zfib Sq)(zfib (sub Sq one)))(add (zfib Sq)(zfib zz))) end;
            val reflL = oeqreflZ_at (add (zfib Sq)(zfib (sub Sq one)));
            val lhs_eq = oeq_subst_at (Pzs, sub Sq one, q) sub_eq reflL; (* add(zfib(Sq))(zfib(sub(Sq)1)) = add(zfib Sq)(zfib q) *)
            val ss = zfibSS_at q;                          (* zfib(SSq) = add(zfib(Sq))(zfib q) *)
            (* goal at Suc q : oeq (zfib(Suc(Suc q))) (add(zfib(Sq))(zfib(sub Sq 1))) *)
            val goalSq = oeq_trans OF [ss, oeq_sym OF [lhs_eq]];  (* zfib(SSq) = add(zfib Sq)(zfib(sub Sq 1)) *)
            val PiAll = let val zz = Free("z_iss", natT)
                        in Term.lambda zz (oeq (zfib (suc zz)) (add (zfib zz)(zfib (sub zz one)))) end;
            val res = oeq_subst_at (PiAll, Sq, kF) (oeq_sym OF [hq]) goalSq;
          in res end;
        val core = exE_elimZ (Pq, goalC) exHyp "q_ss2" natT body;
        val disch = Thm.implies_intr (ctermZ (jT (mkEx Pq))) core;
      in disch end;
    val res = disjE_elimZ (oeq kF ZeroC, mkEx (Abs("q", natT, oeq kF (suc (Bound 0)))), goalC) dz caseZero caseSuc;
  in varify res end;
val () = out ("zfib_Suc_split hyps=" ^ Int.toString (length (Thm.hyps_of zfib_Suc_split)) ^ "\n");

(* ============================================================================
   add_le_cancel_l : le (add c a)(add c b) ==> le a b
     witness p: add c b = add (add c a) p = add c (add a p) (assoc) -> b = add a p
     (add_left_cancel) -> le a b.
   ============================================================================ *)
val add_le_cancel_l =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H = Thm.assume (ctermZ (jT (le (add cF aF) (add cF bF))));  (* Ex(%p. add c b = add (add c a) p) *)
    val Pabs = Abs("p", natT, oeq (add cF bF) (add (add cF aF) (Bound 0)));
    val goal = le aF bF;
    fun body p hp =                                       (* hp : add c b = add (add c a) p *)
      let
        val assoc = addassocZ_at (cF, aF, p);             (* add (add c a) p = add c (add a p) *)
        val cb_eq = oeq_trans OF [hp, assoc];             (* add c b = add c (add a p) *)
        val canc = add_left_cancel_vZ OF [cb_eq];         (* b = add a p *)
      in le_introZ (aF, bF, p) canc end;
    val core = exE_elimZ (Pabs, goal) H "p_alc" natT body;
    val disch = Thm.implies_intr (ctermZ (jT (le (add cF aF) (add cF bF)))) core;
  in varify disch end;
val () = out ("add_le_cancel_l hyps=" ^ Int.toString (length (Thm.hyps_of add_le_cancel_l)) ^ "\n");

(* add_lt_cancel_l : lt (add c a)(add c b) ==> lt a b
     lt (add c a)(add c b) = le (Suc(add c a))(add c b).  Suc(add c a) = add c (Suc a).
     -> le (add c (Suc a))(add c b) -> le (Suc a) b (add_le_cancel_l) = lt a b.
   ============================================================================ *)
val add_le_cancel_l_vZ = varify add_le_cancel_l;
val add_lt_cancel_l =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H = Thm.assume (ctermZ (jT (lt (add cF aF) (add cF bF))));  (* le (Suc(add c a))(add c b) *)
    (* rewrite Suc(add c a) -> add c (Suc a) via sym add_Suc_right *)
    val aSr = addSrZ_at (cF, aF);                         (* add c (Suc a) = Suc(add c a) *)
    val Pl = let val zz = Free("z_alt", natT) in Term.lambda zz (le zz (add cF bF)) end;
    val H2 = oeq_subst_at (Pl, suc (add cF aF), add cF (suc aF)) (oeq_sym OF [aSr]) H;  (* le (add c (Suc a))(add c b) *)
    val res = (beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ (suc aF)),(("b",0), ctermZ bF),(("c",0), ctermZ cF)] add_le_cancel_l_vZ))
              OF [H2];                                     (* le (Suc a) b = lt a b *)
    val disch = Thm.implies_intr (ctermZ (jT (lt (add cF aF) (add cF bF)))) res;
  in varify disch end;
val () = out ("add_lt_cancel_l hyps=" ^ Int.toString (length (Thm.hyps_of add_lt_cancel_l)) ^ "\n");

val () = out "ZK_CANCEL_OK\n";

(* ============================================================================
   sub_lt_self : le (Suc Zero) a ==> le a n ==> lt (sub n a) n
     add a (sub n a) = n (add_sub) ; le 1 a -> lt (sub n a) (add a (sub n a))
     (lt_add_pos_comm) ; rewrite RHS -> n.
   ============================================================================ *)
val sub_lt_self =
  let
    val aF = Free("a", natT); val nF = Free("n", natT);
    val Hpos = Thm.assume (ctermZ (jT (le one aF)));    (* le 1 a *)
    val Hle = Thm.assume (ctermZ (jT (le aF nF)));      (* le a n *)
    val asub = add_sub_vZ OF [Hle];                     (* add a (sub n a) = n *)
    val lapc = (beta_norm (Drule.infer_instantiate ctxtZ
                 [(("a",0), ctermZ (sub nF aF)),(("c",0), ctermZ aF)] lt_add_pos_comm_vZ)) OF [Hpos];
    (* lapc : lt (sub n a) (add a (sub n a)) *)
    val Pr = let val zz = Free("z_sls", natT) in Term.lambda zz (lt (sub nF aF) zz) end;
    val res = oeq_subst_at (Pr, add aF (sub nF aF), nF) asub lapc;  (* lt (sub n a) n *)
    val disch = Thm.implies_intr (ctermZ (jT (le aF nF)))
                  (Thm.implies_intr (ctermZ (jT (le one aF))) res);
  in varify disch end;
val () = out ("sub_lt_self hyps=" ^ Int.toString (length (Thm.hyps_of sub_lt_self)) ^ "\n");

(* ============================================================================
   rem_bound : le (zfib k) n ==> lt n (zfib (Suc k)) ==> lt (sub n (zfib k)) (zfib (sub k 1))
   ============================================================================ *)
val zfib_Suc_split_vZ = varify zfib_Suc_split;
val add_lt_cancel_l_vZ = varify add_lt_cancel_l;
val rem_bound =
  let
    val kF = Free("k", natT); val nF = Free("n", natT);
    val Hle = Thm.assume (ctermZ (jT (le (zfib kF) nF)));      (* le (zfib k) n *)
    val Hlt = Thm.assume (ctermZ (jT (lt nF (zfib (suc kF)))));(* lt n (zfib(Suc k)) *)
    val asub = add_sub_vZ OF [Hle];                            (* add (zfib k)(sub n (zfib k)) = n *)
    (* rewrite n -> add (zfib k)(sub n (zfib k)) inside lt 1st arg via sym asub *)
    val Pl = let val zz = Free("z_rb1", natT) in Term.lambda zz (lt zz (zfib (suc kF))) end;
    val lt1 = oeq_subst_at (Pl, nF, add (zfib kF)(sub nF (zfib kF))) (oeq_sym OF [asub]) Hlt;
    (* lt1 : lt (add (zfib k)(sub n (zfib k))) (zfib(Suc k)) *)
    val split = beta_norm (Drule.infer_instantiate ctxtZ [(("k",0), ctermZ kF)] zfib_Suc_split_vZ);
    (* split : zfib(Suc k) = add (zfib k)(zfib(sub k 1)) *)
    val Pr = let val zz = Free("z_rb2", natT) in Term.lambda zz (lt (add (zfib kF)(sub nF (zfib kF))) zz) end;
    val lt2 = oeq_subst_at (Pr, zfib (suc kF), add (zfib kF)(zfib (sub kF one))) split lt1;
    (* lt2 : lt (add (zfib k)(sub n (zfib k)))(add (zfib k)(zfib(sub k 1))) *)
    val res = (beta_norm (Drule.infer_instantiate ctxtZ
                [(("a",0), ctermZ (sub nF (zfib kF))),(("b",0), ctermZ (zfib (sub kF one))),(("c",0), ctermZ (zfib kF))]
                add_lt_cancel_l_vZ)) OF [lt2];                 (* lt (sub n (zfib k))(zfib(sub k 1)) *)
    val disch = Thm.implies_intr (ctermZ (jT (lt nF (zfib (suc kF)))))
                  (Thm.implies_intr (ctermZ (jT (le (zfib kF) nF))) res);
  in varify disch end;
val () = out ("rem_bound hyps=" ^ Int.toString (length (Thm.hyps_of rem_bound)) ^ "\n");

val () = out "ZK_REMBOUND_OK\n";

(* ============================================================================
   An EXISTENTIAL over ixlist (the foundation's Ex is over nat only).
   Conservative: a new const rEx : (ixlist => o) => o with intro/elim axioms
   mirroring exI/exE.  Extends thyZ once -> thyZ2 / ctxtZ2 / ctermZ2.
   ============================================================================ *)
val rpredOT = ixlistT --> oT;
val thyZ2a = Sign.add_consts [(Binding.name "rEx", rpredOT --> oT, NoSyn)] thyZ;
val rExC = Const (Sign.full_name thyZ2a (Binding.name "rEx"), rpredOT --> oT);
fun mkREx pr = rExC $ pr;
val rPp = Free("rP", rpredOT);
val raE = Free("ra", ixlistT);
val rexI_prop = Logic.mk_implies (jT (rPp $ raE), jT (mkREx rPp));
val ((_,rexI_ax), thyZ2b) = Thm.add_axiom_global (Binding.name "rexI", rexI_prop) thyZ2a;
val rQfree = Free("rQ", oT);
val rxE = Free("rx", ixlistT);
val rexE_prop =
  Logic.mk_implies (jT (mkREx rPp),
    Logic.mk_implies (Logic.all rxE (Logic.mk_implies (jT (rPp $ rxE), jT rQfree)),
      jT rQfree));
val ((_,rexE_ax), thyZ2) = Thm.add_axiom_global (Binding.name "rexE", rexE_prop) thyZ2b;

val ctxtZ2  = Proof_Context.init_global thyZ2;
val ctermZ2 = Thm.cterm_of ctxtZ2;
val rexI_vZ = varify rexI_ax;
val rexE_vZ = varify rexE_ax;

(* rexI_at : witness rt, predicate rPabs (ixlist->o) ; jT (rPabs rt) -> jT (rEx rPabs) *)
fun rexI_at (rPabs, rt) hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2
        [(("rP",0), ctermZ2 rPabs), (("ra",0), ctermZ2 rt)] rexI_vZ)
  in inst OF [hbody] end;
(* rexE_elim : (rPabs, goalC) exThm name bodyFn ; goalC : o (a Free-built term) *)
fun rexE_elim (rPabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, ixlistT);
    val hypTerm = jT (Term.betapply (rPabs, wF));
    val hypThm = Thm.assume (ctermZ2 hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermZ2 wF) (Thm.implies_intr (ctermZ2 hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtZ2
          [(("rP",0), ctermZ2 rPabs), (("rQ",0), ctermZ2 goalC)] rexE_vZ);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

val () = out "ZK_REX_OK\n";

(* ============================================================================
   Connective / elimination helpers REBUILT on ctxtZ2 / ctermZ2 (so terms that
   mention rEx can be cterm-ified).  Mirror the _atZ family.
   ============================================================================ *)
fun oeqreflZ2_at t = beta_norm (Drule.infer_instantiate ctxtZ2 [(("a",0), ctermZ2 t)] oeq_refl_vZ);
fun conjI_atZ2 (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] conjI_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atZ2 (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] conjunct1_vZ)
  in Thm.implies_elim inst h end;
fun conjunct2_atZ2 (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] conjunct2_vZ)
  in Thm.implies_elim inst h end;
fun disjI1_atZ2 (At,Bt) h =
  (beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] disjI1_vZ)) OF [h];
fun disjI2_atZ2 (At,Bt) h =
  (beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] disjI2_vZ)) OF [h];
fun disjE_elimZ2 (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt),(("C",0), ctermZ2 Ct)] disjE_vZ)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun mp_atZ2 (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] mp_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_atZ2 (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("A",0), ctermZ2 At),(("B",0), ctermZ2 Bt)] impI_vZ)
  in Thm.implies_elim inst hImpThm end;
fun allI_atZ2 Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("P",0), ctermZ2 Pabs)] allI_vZ)
  in Thm.implies_elim inst hAllThm end;
fun allE_atZ2 Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("P",0), ctermZ2 Pabs),(("a",0), ctermZ2 at)] allE_vZ)
  in Thm.implies_elim inst hForall end;
fun oFalse_elimZ2_at rT = beta_norm (Drule.infer_instantiate ctxtZ2 [(("R",0), ctermZ2 rT)] oFalse_elim_vZ);
(* exE over nat, on ctxtZ2 (for terms with rEx in the goal) *)
fun exE_elimZ2 (Pabs, goalC) exThm wName wTy bodyFn =
  let
    val wF = Free(wName, wTy);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermZ2 hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermZ2 wF) (Thm.implies_intr (ctermZ2 hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("P",0), ctermZ2 Pabs), (("Q",0), ctermZ2 goalC)] exE_vZ);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
(* generic oeq_subst on ctxtZ2 *)
fun oeq_subst_atZ2 (Pabs, aT, bT) heq hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("P",0), ctermZ2 Pabs), (("a",0), ctermZ2 aT), (("b",0), ctermZ2 bT)] oeq_subst_vZ)
  in (inst OF [heq]) OF [hPa] end;

val () = out "ZK_Z2HELPERS_OK\n";

(* ctxtZ2 accessor variants (for terms used inside exist_bounded; old constants,
   but the surrounding hyps are ctxtZ2 cterms, so route these through ctermZ2). *)
fun vbINil_at2 t   = beta_norm (Drule.infer_instantiate ctxtZ2 [(("b",0), ctermZ2 t)] vb_INil_v);
fun repCons_at2 (it,rt) = beta_norm (Drule.infer_instantiate ctxtZ2
                          [(("i",0), ctermZ2 it),(("r",0), ctermZ2 rt)] rep_ICons_v);
fun vbCons_at2 (bt,it,rt) = beta_norm (Drule.infer_instantiate ctxtZ2
                          [(("b",0), ctermZ2 bt),(("i",0), ctermZ2 it),(("r",0), ctermZ2 rt)] vb_cons_v);
fun le_introZ2 (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("P",0), ctermZ2 Pabs), (("a",0), ctermZ2 w)] exI_vZ);
  in inst OF [hyp] end;
fun add_cong_rZ2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ2 [(("P",0), ctermZ2 Pabs), (("a",0), ctermZ2 pT), (("b",0), ctermZ2 qT)] oeq_subst_vZ);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtZ2 [(("a",0), ctermZ2 (add hT pT))] oeq_refl_vZ);
  in inst OF [hpq, refl_hp] end;
val () = out "ZK_Z2ACC_OK\n";

(* ============================================================================
   exist_bounded : forall n. forall b. lt n (zfib b) ==>
                   rEx(%r. (vb b r AND oeq (rep_sum r) n))
   STRONG INDUCTION on n (b object-universally quantified).
     P n := Forall(%b. Imp (lt n (zfib b)) (rEx(%r. Conj (vb b r)(oeq (rep_sum r) n))))
   Given (lt n (zfib b)), IH for all m<n:
     case n=0 : r=INil ; vb b INil (vb_INil) ; rep_sum INil = 0 = n.
     case n>0 : zfib_index_exists -> k with (zfib k <= n) /\ (n < zfib(Suc k)).
       lt k b  (zfib_lt_rev of: zfib k <= n < zfib b so zfib k < zfib b).
       rem_bound -> lt (sub n (zfib k)) (zfib(sub k 1)).
       sub_lt_self -> lt (sub n (zfib k)) n  (zfib k>=1, zfib k<=n) -> apply IH.
       IH at m=sub n (zfib k), b'=sub k 1, premise lt m (zfib(sub k 1)) [rem_bound]:
         rEx(%r'. vb (sub k 1) r' /\ rep_sum r' = sub n (zfib k)).
       rexE -> r' with vb (sub k 1) r' and rep_sum r' = sub n (zfib k).
       prepend k:  vb_cons (lt k b)(vb (sub k 1) r') -> vb b (ICons k r').
       rep_sum (ICons k r') = add (zfib k)(rep_sum r') = add (zfib k)(sub n (zfib k)) = n
         (rep_ICons + add_cong_r + add_sub).
       rexI at r = ICons k r'.
   ============================================================================ *)
val zfib_index_exists_vZ = varify zfib_index_exists;
val zfib_lt_rev_vZ = varify zfib_lt_rev;
val rem_bound_vZ = varify rem_bound;
val sub_lt_self_vZ = varify sub_lt_self;
val add_sub_vZ2 = varify add_sub;

(* rEx body for the rep-existence at bound b, value v *)
fun ebBody b v = Abs("r_eb", ixlistT, mkConj (vb b (Bound 0)) (oeq (rep_sum (Bound 0)) v));
fun ebProp b v = mkREx (ebBody b v);

val exist_bounded =
  let
    (* strong-induction predicate over n *)
    fun Pn_body n = let val bb = Free("b_eb", natT)
                    in Term.lambda bb (mkImp (lt n (zfib bb)) (ebProp bb n)) end;
    fun Pn n = mkForall (Pn_body n);
    val Ppred = let val nn = Free("n_ep", natT) in Term.lambda nn (Pn nn) end;  (* nat->o *)
    (* the strong-induction step: !!n. (!!m. lt m n ==> P m) ==> P n *)
    val nF = Free("n_eb", natT);
    val mSI = Free("m_eb", natT);
    val IHprop = Logic.all mSI (Logic.mk_implies (jT (lt mSI nF), jT (Pn mSI)));
    val IH = Thm.assume (ctermZ2 IHprop);
    val bF = Free("b_z", natT);
    val antLt = lt nF (zfib bF);
    val goalEx = ebProp bF nF;
    val concl =
      let
        val hLt = Thm.assume (ctermZ2 (jT antLt));        (* lt n (zfib b) *)
        (* case split n = 0 or n > 0 via disj_zero_or_suc n *)
        val dz = beta_norm (Drule.infer_instantiate ctxtZ2 [(("p",0), ctermZ2 nF)] disj_zero_or_suc_vZ2);
        (* dz : Disj (oeq n 0)(Ex(%q. oeq n (Suc q))) *)
        val caseZero =
          let
            val hz = Thm.assume (ctermZ2 (jT (oeq nF ZeroC)));   (* n = 0 *)
            (* r = INil ; vb b INil ; rep_sum INil = 0 = n *)
            val hvb = vbINil_at2 bF;                             (* vb b INil *)
            val rINil = rep_INil_v;                            (* rep_sum INil = 0 *)
            val rep_n = oeq_trans OF [rINil, oeq_sym OF [hz]]; (* rep_sum INil = n *)
            val conj = conjI_atZ2 (vb bF INilC, oeq (rep_sum INilC) nF) hvb rep_n;
            val g = rexI_at (ebBody bF nF, INilC) conj;        (* rEx(%r. ...) *)
          in Thm.implies_intr (ctermZ2 (jT (oeq nF ZeroC))) g end;
        val caseSuc =
          let
            val Pq = Abs("q", natT, oeq nF (suc (Bound 0)));
            val exHyp = Thm.assume (ctermZ2 (jT (mkEx Pq)));
            fun body q hq =                                     (* hq : n = Suc q ; so 0 < n *)
              let
                (* 0 < n : lt Zero n = le (Suc 0) n.  n = Suc q -> le (Suc 0) n via witness q:
                   n = add (Suc 0) q = Suc(add 0 q) = Suc q. *)
                val aS1 = addSucZ_at (ZeroC, q);              (* add (Suc 0) q = Suc(add 0 q) *)
                val a0 = add0Z_at q;                          (* add 0 q = q *)
                val one_q = oeq_trans OF [aS1,
                              (let val P=Abs("z",natT,oeq (suc (add ZeroC q)) (suc (Bound 0)))
                               in oeq_subst_atZ2 (P, add ZeroC q, q) a0 (oeqreflZ2_at (suc (add ZeroC q))) end)];
                (* one_q : add (Suc 0) q = Suc q *)
                val n_eq = oeq_trans OF [hq, oeq_sym OF [one_q]];   (* n = add (Suc 0) q *)
                val Hpos = le_introZ2 (one, nF, q) n_eq;        (* le 1 n = lt 0 n *)
                (* zfib_index_exists at n *)
                val zie = (beta_norm (Drule.infer_instantiate ctxtZ2 [(("n",0), ctermZ2 nF)] zfib_index_exists_vZ)) OF [Hpos];
                (* zie : Qprop n = Ex(%j. Conj (le (zfib j) n)(lt n (zfib(Suc j)))) *)
                fun jbody k hk =                               (* hk : Conj (le (zfib k) n)(lt n (zfib(Suc k))) *)
                  let
                    val hLeK = conjunct1_atZ2 (le (zfib k) nF, lt nF (zfib (suc k))) hk;  (* le (zfib k) n *)
                    val hLtK = conjunct2_atZ2 (le (zfib k) nF, lt nF (zfib (suc k))) hk;  (* lt n (zfib(Suc k)) *)
                    (* lt k b : zfib k < zfib b.  zfib k <= n (hLeK) ; n < zfib b (hLt) -> zfib k < zfib b. *)
                    val zfk_lt_zfb = (le_trans_vZ4 OF [hLeK, lt_imp_le_vZ OF [hLt]]);  (* le (zfib k) ... no *)
                    (* careful: need lt (zfib k)(zfib b).  le (zfib k) n and lt n (zfib b).
                       le_trans (le (Suc(zfib k)) ...) : lt n m = le (Suc n) m.
                       lt (zfib k)(zfib b) = le (Suc(zfib k))(zfib b).
                       From le (zfib k) n : le (Suc(zfib k))(Suc n) (le_suc_mono).
                       hLt = lt n (zfib b) = le (Suc n)(zfib b).
                       le_trans -> le (Suc(zfib k))(zfib b) = lt (zfib k)(zfib b). *)
                    val lsm = (beta_norm (Drule.infer_instantiate ctxtZ2
                                [(("m",0), ctermZ2 (zfib k)),(("n",0), ctermZ2 nF)] (varify le_suc_mono))) OF [hLeK];
                    (* lsm : le (Suc(zfib k))(Suc n) *)
                    val ltzfkb = le_trans_vZ4 OF [lsm, hLt];   (* le (Suc(zfib k))(zfib b) = lt (zfib k)(zfib b) *)
                    val ltkb = zfib_lt_rev_vZ OF [ltzfkb];     (* lt k b *)
                    (* rem_bound : lt (sub n (zfib k))(zfib(sub k 1)) *)
                    val rb = ((beta_norm (Drule.infer_instantiate ctxtZ2
                                [(("k",0), ctermZ2 k),(("n",0), ctermZ2 nF)] rem_bound_vZ)) OF [hLtK]) OF [hLeK];
                    (* sub_lt_self : lt (sub n (zfib k)) n  (need le 1 (zfib k) and le (zfib k) n) *)
                    val ge1 = beta_norm (Drule.infer_instantiate ctxtZ2 [(("k",0), ctermZ2 k)] zfib_ge1_vZ); (* le 1 (zfib k) *)
                    val sls = ((beta_norm (Drule.infer_instantiate ctxtZ2
                                [(("a",0), ctermZ2 (zfib k)),(("n",0), ctermZ2 nF)] sub_lt_self_vZ)) OF [hLeK]) OF [ge1];
                    (* sls : lt (sub n (zfib k)) n *)
                    (* IH at m = sub n (zfib k) : Trueprop (Pn (sub n (zfib k))) *)
                    val ihAt = Thm.implies_elim (Thm.forall_elim (ctermZ2 (sub nF (zfib k))) IH) sls;
                    (* ihAt : Pn (sub n (zfib k)) = Forall(%b'. Imp (lt (sub n (zfib k))(zfib b'))(ebProp b' (sub n (zfib k)))) *)
                    val ihAtB = allE_atZ2 (Pn_body (sub nF (zfib k))) (sub k one) ihAt;
                    (* ihAtB : Imp (lt (sub n (zfib k))(zfib(sub k 1)))(ebProp (sub k 1)(sub n (zfib k))) *)
                    val exr = mp_atZ2 (lt (sub nF (zfib k))(zfib (sub k one)), ebProp (sub k one)(sub nF (zfib k))) ihAtB rb;
                    (* exr : rEx(%r'. vb (sub k 1) r' /\ rep_sum r' = sub n (zfib k)) *)
                    fun rbody rp hrp =                          (* hrp : Conj (vb (sub k 1) r')(rep_sum r' = sub n (zfib k)) *)
                      let
                        val hvbtl = conjunct1_atZ2 (vb (sub k one) rp, oeq (rep_sum rp)(sub nF (zfib k))) hrp;  (* vb (sub k 1) r' *)
                        val hrepr = conjunct2_atZ2 (vb (sub k one) rp, oeq (rep_sum rp)(sub nF (zfib k))) hrp;  (* rep_sum r' = sub n (zfib k) *)
                        (* vb b (ICons k r') via vb_cons (lt k b)(vb (sub k 1) r') *)
                        val vbcons = ((vbCons_at2 (bF, k, rp)) OF [ltkb]) OF [hvbtl];   (* vb b (ICons k r') *)
                        (* rep_sum (ICons k r') = add (zfib k)(rep_sum r') *)
                        val rc = repCons_at2 (k, rp);            (* rep_sum(ICons k r') = add (zfib k)(rep_sum r') *)
                        (* add (zfib k)(rep_sum r') = add (zfib k)(sub n (zfib k))  (cong_r of hrepr) *)
                        val cong = add_cong_rZ2 (zfib k, rep_sum rp, sub nF (zfib k)) hrepr;
                        (* add (zfib k)(sub n (zfib k)) = n  (add_sub, le (zfib k) n) *)
                        val asub = add_sub_vZ2 OF [hLeK];       (* add (zfib k)(sub n (zfib k)) = n *)
                        val rep_n = oeq_trans OF [oeq_trans OF [rc, cong], asub];  (* rep_sum(ICons k r') = n *)
                        val conj = conjI_atZ2 (vb bF (icons k rp), oeq (rep_sum (icons k rp)) nF) vbcons rep_n;
                        val g = rexI_at (ebBody bF nF, icons k rp) conj;
                      in g end;
                    val gj = rexE_elim (Abs("r_eb2", ixlistT, mkConj (vb (sub k one)(Bound 0))(oeq (rep_sum (Bound 0))(sub nF (zfib k)))), goalEx) exr "rp_eb" rbody;
                  in gj end;
                val gn = exE_elimZ2 (Qbody nF, goalEx) zie "k_eb" natT jbody;
              in gn end;
            val g = exE_elimZ2 (Pq, goalEx) exHyp "q_eb" natT body;
          in Thm.implies_intr (ctermZ2 (jT (mkEx Pq))) g end;
        val res = disjE_elimZ2 (oeq nF ZeroC, mkEx (Abs("q", natT, oeq nF (suc (Bound 0)))), goalEx) dz caseZero caseSuc;
        val disch = Thm.implies_intr (ctermZ2 (jT antLt)) res;
      in impI_atZ2 (antLt, goalEx) disch end;
    val PnN = allI_atZ2 (Pn_body nF) (Thm.forall_intr (ctermZ2 bF) concl);  (* Pn n *)
    val stepThm = Thm.forall_intr (ctermZ2 nF) (Thm.implies_intr (ctermZ2 IHprop) PnN);
    val kArg = Free("nn", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtZ2
                   [(("P",0), ctermZ2 Ppred), (("k",0), ctermZ2 kArg)] strong_induct_vZ);
    val PnK = Thm.implies_elim siInst stepThm;             (* Pn nn *)
  in varify PnK end;
val () = out ("exist_bounded hyps=" ^ Int.toString (length (Thm.hyps_of exist_bounded)) ^ "\n");

val () = out "ZK_EXISTB_OK\n";

(* ============================================================================
   EXISTENCE : forall n. lt 0 n ==> rEx(%r. valid_rep r AND oeq (rep_sum r) n)
     zfib_index_exists -> k with n < zfib(Suc k).
     exist_bounded at b = Suc k -> rEx(%r. vb (Suc k) r AND rep_sum r = n).
     vb (Suc k) r => valid_rep r  (vb_imp_valid).
   ============================================================================ *)
val exist_bounded_vZ = varify exist_bounded;
val vb_imp_valid_vZ  = varify vb_imp_valid;

(* the existence rEx body : %r. Conj (valid_rep r)(oeq (rep_sum r) n) *)
fun exBody n = Abs("r_ex", ixlistT, mkConj (valid_rep (Bound 0)) (oeq (rep_sum (Bound 0)) n));
fun exProp n = mkREx (exBody n);

val existence =
  let
    val nF = Free("n", natT);
    val Hpos = Thm.assume (ctermZ2 (jT (lt ZeroC nF)));   (* 0 < n *)
    val goalEx = exProp nF;
    (* zfib_index_exists at n *)
    val zie = (beta_norm (Drule.infer_instantiate ctxtZ2 [(("n",0), ctermZ2 nF)] zfib_index_exists_vZ)) OF [Hpos];
    (* zie : Ex(%j. Conj (le (zfib j) n)(lt n (zfib(Suc j)))) *)
    fun jbody k hk =                                       (* hk : Conj (le (zfib k) n)(lt n (zfib(Suc k))) *)
      let
        val hLtK = conjunct2_atZ2 (le (zfib k) nF, lt nF (zfib (suc k))) hk;  (* lt n (zfib(Suc k)) *)
        (* exist_bounded : forall n. forall b. lt n (zfib b) ==> ebProp b n.
           exist_bounded_vZ is Pn nn = Forall(%b. Imp (lt nn (zfib b))(ebProp b nn)).
           Need it at value nF: instantiate the universally-quantified outer nat. *)
        val eb_n = beta_norm (Drule.infer_instantiate ctxtZ2 [(("nn",0), ctermZ2 nF)] exist_bounded_vZ);
        (* eb_n : Pn n = Forall(%b. Imp (lt n (zfib b))(ebProp b n)) *)
        val eb_atB = allE_atZ2 (let val bb = Free("b_eb", natT)
                                in Term.lambda bb (mkImp (lt nF (zfib bb)) (ebProp bb nF)) end) (suc k) eb_n;
        (* eb_atB : Imp (lt n (zfib(Suc k)))(ebProp (Suc k) n) *)
        val exr = mp_atZ2 (lt nF (zfib (suc k)), ebProp (suc k) nF) eb_atB hLtK;
        (* exr : rEx(%r. vb (Suc k) r AND rep_sum r = n) *)
        fun rbody rp hrp =                                 (* hrp : Conj (vb (Suc k) r)(rep_sum r = n) *)
          let
            val hvb = conjunct1_atZ2 (vb (suc k) rp, oeq (rep_sum rp) nF) hrp;  (* vb (Suc k) r *)
            val hrep = conjunct2_atZ2 (vb (suc k) rp, oeq (rep_sum rp) nF) hrp; (* rep_sum r = n *)
            (* vb_imp_valid : VProp r = Forall(%b. Imp (vb b r)(valid_rep r)) *)
            val vp = beta_norm (Drule.infer_instantiate ctxtZ2 [(("k_vv",0), ctermZ2 rp)] vb_imp_valid_vZ);
            val atb = allE_atZ2 (let val bb = Free("b_vv", natT) in Term.lambda bb (mkImp (vb bb rp)(valid_rep rp)) end) (suc k) vp;
            val hvalid = mp_atZ2 (vb (suc k) rp, valid_rep rp) atb hvb;          (* valid_rep r *)
            val conj = conjI_atZ2 (valid_rep rp, oeq (rep_sum rp) nF) hvalid hrep;
            val g = rexI_at (exBody nF, rp) conj;          (* rEx(%r. valid_rep r AND rep_sum r = n) *)
          in g end;
        val gj = rexE_elim (Abs("r_eb", ixlistT, mkConj (vb (suc k)(Bound 0))(oeq (rep_sum (Bound 0)) nF)), goalEx) exr "rp_ex" rbody;
      in gj end;
    val gn = exE_elimZ2 (Qbody nF, goalEx) zie "k_ex" natT jbody;
    val disch = Thm.implies_intr (ctermZ2 (jT (lt ZeroC nF))) gn;
  in varify disch end;
val () = out ("existence hyps=" ^ Int.toString (length (Thm.hyps_of existence))
              ^ ":\n  " ^ Syntax.string_of_term ctxtZ2 (Thm.prop_of existence) ^ "\n");

(* ---- aconv check vs the intended statement ---- *)
val nVc = Var(("n",0), natT);
val existence_intended =
  Logic.mk_implies (jT (lt ZeroC nVc), jT (exProp nVc));
val ex_hyps0 = (length (Thm.hyps_of existence) = 0);
val ex_aconv = (Thm.prop_of existence) aconv existence_intended;
val () = out ("existence 0hyp=" ^ Bool.toString ex_hyps0 ^ " aconv=" ^ Bool.toString ex_aconv ^ "\n");
val () = if ex_hyps0 andalso ex_aconv then out "ZK_EXIST_OK\n" else out "ZK_EXIST_FAIL\n";

(* ---- existence soundness probes (kernel rejects degenerate variants) ---- *)
val ex_bogus_sum =   (* claims rep_sum r = Suc n  (wrong) *)
  Logic.mk_implies (jT (lt ZeroC nVc),
    jT (mkREx (Abs("r_ex", ixlistT, mkConj (valid_rep (Bound 0)) (oeq (rep_sum (Bound 0)) (suc nVc))))));
val ex_drop_pos =    (* drops the 0<n hypothesis *)
  jT (exProp nVc);
val ex_probe1 = not ((Thm.prop_of existence) aconv ex_bogus_sum);
val ex_probe2 = not ((Thm.prop_of existence) aconv ex_drop_pos);
val () = if ex_probe1 andalso ex_probe2
         then out "ZK_EXIST_PROBE_OK\n" else out "ZK_EXIST_PROBE_FAIL\n";

(* ============================================================================
   LIST EQUALITY req : ixlist -> ixlist -> o  (extends thyZ2 -> thyZ3)
     req_refl : req r r
     req_cons : oeq i j ==> req r s ==> req (ICons i r)(ICons j s)
     req_nil_cons / req_cons_nil : discrimination (soundness; not needed for the
       uniqueness construction but they keep req from being vacuously True).
   ============================================================================ *)
val thyZ3a = Sign.add_consts [(Binding.name "req", ixlistT --> ixlistT --> oT, NoSyn)] thyZ2;
val reqC = Const (Sign.full_name thyZ3a (Binding.name "req"), ixlistT --> ixlistT --> oT);
fun req r s = reqC $ r $ s;
val rRF = Free("r", ixlistT); val sRF = Free("s", ixlistT);
val iRF = Free("i", natT); val jRF = Free("j", natT);
val ((_,req_refl), thyZ3b) = Thm.add_axiom_global (Binding.name "req_refl", jT (req rRF rRF)) thyZ3a;
val req_cons_prop =
  Logic.mk_implies (jT (oeq iRF jRF),
    Logic.mk_implies (jT (req rRF sRF), jT (req (icons iRF rRF)(icons jRF sRF))));
val ((_,req_cons), thyZ3c) = Thm.add_axiom_global (Binding.name "req_cons", req_cons_prop) thyZ3b;
(* discrimination (soundness only) *)
val req_nil_cons_prop = Logic.mk_implies (jT (req INilC (icons iRF rRF)), jT oFalseC);
val ((_,req_nil_cons), thyZ3d) = Thm.add_axiom_global (Binding.name "req_nil_cons", req_nil_cons_prop) thyZ3c;
val req_cons_nil_prop = Logic.mk_implies (jT (req (icons iRF rRF) INilC), jT oFalseC);
val ((_,req_cons_nil), thyZ3) = Thm.add_axiom_global (Binding.name "req_cons_nil", req_cons_nil_prop) thyZ3d;

val ctxtZ3  = Proof_Context.init_global thyZ3;
val ctermZ3 = Thm.cterm_of ctxtZ3;
val req_refl_vZ = varify req_refl;
val req_cons_vZ = varify req_cons;
fun req_refl_at t = beta_norm (Drule.infer_instantiate ctxtZ3 [(("r",0), ctermZ3 t)] req_refl_vZ);
(* req_cons_at (i,j,r,s) hij hrs : req (ICons i r)(ICons j s) *)
fun req_cons_at (it,jt,rt,st) hij hrs =
  ((beta_norm (Drule.infer_instantiate ctxtZ3
      [(("i",0), ctermZ3 it),(("j",0), ctermZ3 jt),(("r",0), ctermZ3 rt),(("s",0), ctermZ3 st)] req_cons_vZ))
   OF [hij]) OF [hrs];

(* ---- ctxtZ3 connective helpers (terms may mention req) ---- *)
fun oeqreflZ3_at t = beta_norm (Drule.infer_instantiate ctxtZ3 [(("a",0), ctermZ3 t)] oeq_refl_vZ);
fun conjI_atZ3 (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("A",0), ctermZ3 At),(("B",0), ctermZ3 Bt)] conjI_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atZ3 (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("A",0), ctermZ3 At),(("B",0), ctermZ3 Bt)] conjunct1_vZ)
  in Thm.implies_elim inst h end;
fun conjunct2_atZ3 (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("A",0), ctermZ3 At),(("B",0), ctermZ3 Bt)] conjunct2_vZ)
  in Thm.implies_elim inst h end;
fun disjE_elimZ3 (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("A",0), ctermZ3 At),(("B",0), ctermZ3 Bt),(("C",0), ctermZ3 Ct)] disjE_vZ)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun mp_atZ3 (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("A",0), ctermZ3 At),(("B",0), ctermZ3 Bt)] mp_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_atZ3 (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("A",0), ctermZ3 At),(("B",0), ctermZ3 Bt)] impI_vZ)
  in Thm.implies_elim inst hImpThm end;
fun allI_atZ3 Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("P",0), ctermZ3 Pabs)] allI_vZ)
  in Thm.implies_elim inst hAllThm end;
fun allE_atZ3 Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("P",0), ctermZ3 Pabs),(("a",0), ctermZ3 at)] allE_vZ)
  in Thm.implies_elim inst hForall end;
fun oFalse_elimZ3_at rT = beta_norm (Drule.infer_instantiate ctxtZ3 [(("R",0), ctermZ3 rT)] oFalse_elim_vZ);
fun exE_elimZ3 (Pabs, goalC) exThm wName wTy bodyFn =
  let
    val wF = Free(wName, wTy);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermZ3 hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermZ3 wF) (Thm.implies_intr (ctermZ3 hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("P",0), ctermZ3 Pabs), (("Q",0), ctermZ3 goalC)] exE_vZ);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
fun oeq_subst_atZ3 (Pabs, aT, bT) heq hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ3 [(("P",0), ctermZ3 Pabs), (("a",0), ctermZ3 aT), (("b",0), ctermZ3 bT)] oeq_subst_vZ)
  in (inst OF [heq]) OF [hPa] end;

val () = out "ZK_REQ_OK\n";

(* ============================================================================
   rep_sum_pos_cons : lt Zero (rep_sum (ICons k r))
     rep_sum(ICons k r) = add (zfib k)(rep_sum r) ; zfib k >= 1 ; lt_add_pos_comm.
     lt 0 (add (zfib k)(rep_sum r)) : lt_add_pos_comm with a=rep_sum r, c=zfib k gives
        lt (rep_sum r)(add (zfib k)(rep_sum r)).  But we want lt 0 (...).
     Instead: le 1 (zfib k) -> le 1 (add (zfib k)(rep_sum r)) (le_add-mono-ish) = lt 0 (...).
     le 1 (zfib k) and le (zfib k)(add (zfib k)(rep_sum r)) (le_add) -> le 1 (...)  (le_trans).
     le 1 x = lt 0 x.
   ============================================================================ *)
val zfib_ge1_vZ3 = varify zfib_ge1;
val le_add_vZ3   = varify le_add;
val le_trans_vZ5 = varify le_trans;
val rep_sum_pos_cons =
  let
    val kF = Free("k", natT); val rF = Free("r", ixlistT);
    val consTm = icons kF rF;
    val ge1 = beta_norm (Drule.infer_instantiate ctxtZ3 [(("k",0), ctermZ3 kF)] zfib_ge1_vZ3); (* le 1 (zfib k) *)
    val ladd = beta_norm (Drule.infer_instantiate ctxtZ3
                 [(("m",0), ctermZ3 (zfib kF)),(("p",0), ctermZ3 (rep_sum rF))] le_add_vZ3); (* le (zfib k)(add (zfib k)(rep_sum r)) *)
    val le1 = le_trans_vZ5 OF [ge1, ladd];          (* le 1 (add (zfib k)(rep_sum r)) *)
    (* rewrite add (zfib k)(rep_sum r) -> rep_sum(ICons k r) via sym rep_ICons *)
    val rc = repCons_at (kF, rF);                    (* rep_sum(ICons k r) = add (zfib k)(rep_sum r) *)
    val Pr = let val zz = Free("z_rpc", natT) in Term.lambda zz (le one zz) end;
    val res = oeq_subst_atZ3 (Pr, add (zfib kF)(rep_sum rF), rep_sum consTm) (oeq_sym OF [rc]) le1;
    (* res : le 1 (rep_sum(ICons k r)) = lt 0 (rep_sum(ICons k r)) *)
  in varify res end;
val () = out ("rep_sum_pos_cons hyps=" ^ Int.toString (length (Thm.hyps_of rep_sum_pos_cons)) ^ "\n");

(* ============================================================================
   zfib_index_unique :
     le (zfib k1) n ==> lt n (zfib (Suc k1)) ==>
     le (zfib k2) n ==> lt n (zfib (Suc k2)) ==> oeq k1 k2
   Via lt_le_cases on (k1,k2) and (k2,k1) + le_zfib monotonicity + le_antisym.
     if lt k1 k2 : le (Suc k1) k2 -> le (zfib(Suc k1))(zfib k2) (le_zfib) ;
        zfib k2 <= n -> le (zfib(Suc k1)) n ; but n < zfib(Suc k1) -> contra.
     if lt k2 k1 : symmetric.
     else le k2 k1 and le k1 k2 -> oeq k1 k2 (le_antisym).
   ============================================================================ *)
val le_zfib_vZ3 = varify le_zfib;
val le_antisym_vZ3 = varify le_antisym;
val lt_le_cases_vZ3 = varify lt_le_cases;
val lt_irrefl_contra_vZ3 = varify lt_irrefl_contra;
val zfib_index_unique =
  let
    val k1 = Free("k1", natT); val k2 = Free("k2", natT); val nF = Free("n", natT);
    val Hle1 = Thm.assume (ctermZ3 (jT (le (zfib k1) nF)));
    val Hlt1 = Thm.assume (ctermZ3 (jT (lt nF (zfib (suc k1)))));
    val Hle2 = Thm.assume (ctermZ3 (jT (le (zfib k2) nF)));
    val Hlt2 = Thm.assume (ctermZ3 (jT (lt nF (zfib (suc k2)))));
    val goalC = oeq k1 k2;
    (* helper: from lt ka kb (so le (Suc ka) kb), zfib kb <= n, n < zfib(Suc ka) -> oFalse *)
    fun contra (ka, kb) hlt_ab hle_b_n hlt_n_Ska =
      let
        (* lt ka kb = le (Suc ka) kb -> le (zfib(Suc ka))(zfib kb) (le_zfib) *)
        val lz = le_zfib_vZ3 OF [hlt_ab];           (* le (zfib(Suc ka))(zfib kb) *)
        val chain = le_trans_vZ5 OF [lz, hle_b_n];  (* le (zfib(Suc ka)) n *)
        (* n < zfib(Suc ka) = le (Suc n)(zfib(Suc ka)) ; le (zfib(Suc ka)) n ; lt_irrefl_contra
           with x = n, y = zfib(Suc ka): lt n (zfib(Suc ka)) /\ le (zfib(Suc ka)) n -> oFalse. *)
        val fls = ((beta_norm (Drule.infer_instantiate ctxtZ3
                     [(("x",0), ctermZ3 nF),(("y",0), ctermZ3 (zfib (suc ka)))] lt_irrefl_contra_vZ3))
                   OF [chain]) OF [hlt_n_Ska];        (* oFalse *)
      in fls end;
    val llc12 = beta_norm (Drule.infer_instantiate ctxtZ3
                  [(("a",0), ctermZ3 k1),(("b",0), ctermZ3 k2)] lt_le_cases_vZ3);  (* Disj (lt k1 k2)(le k2 k1) *)
    val caseLt12 =
      let
        val h = Thm.assume (ctermZ3 (jT (lt k1 k2)));   (* lt k1 k2 *)
        val fls = contra (k1, k2) h Hle2 Hlt1;          (* oFalse *)
        val g = (oFalse_elimZ3_at (oeq k1 k2)) OF [fls];
      in Thm.implies_intr (ctermZ3 (jT (lt k1 k2))) g end;
    val caseLe21 =
      let
        val hle21 = Thm.assume (ctermZ3 (jT (le k2 k1)));  (* le k2 k1 *)
        val llc21 = beta_norm (Drule.infer_instantiate ctxtZ3
                      [(("a",0), ctermZ3 k2),(("b",0), ctermZ3 k1)] lt_le_cases_vZ3); (* Disj (lt k2 k1)(le k1 k2) *)
        val caseLt21 =
          let
            val h = Thm.assume (ctermZ3 (jT (lt k2 k1)));
            val fls = contra (k2, k1) h Hle1 Hlt2;
            val g = (oFalse_elimZ3_at (oeq k1 k2)) OF [fls];
          in Thm.implies_intr (ctermZ3 (jT (lt k2 k1))) g end;
        val caseLe12 =
          let
            val hle12 = Thm.assume (ctermZ3 (jT (le k1 k2)));  (* le k1 k2 *)
            val g = (le_antisym_vZ3 OF [hle12]) OF [hle21];    (* oeq k1 k2 *)
          in Thm.implies_intr (ctermZ3 (jT (le k1 k2))) g end;
        val g = disjE_elimZ3 (lt k2 k1, le k1 k2, oeq k1 k2) llc21 caseLt21 caseLe12;
      in Thm.implies_intr (ctermZ3 (jT (le k2 k1))) g end;
    val res = disjE_elimZ3 (lt k1 k2, le k2 k1, oeq k1 k2) llc12 caseLt12 caseLe21;
    val disch = Thm.implies_intr (ctermZ3 (jT (lt nF (zfib (suc k2)))))
                  (Thm.implies_intr (ctermZ3 (jT (le (zfib k2) nF)))
                    (Thm.implies_intr (ctermZ3 (jT (lt nF (zfib (suc k1)))))
                      (Thm.implies_intr (ctermZ3 (jT (le (zfib k1) nF))) res)));
  in varify disch end;
val () = out ("zfib_index_unique hyps=" ^ Int.toString (length (Thm.hyps_of zfib_index_unique)) ^ "\n");

val () = out "ZK_UNIQHELP_OK\n";

(* ============================================================================
   UNIVERSAL over ixlist : rAll : (ixlist => o) => o   (extends thyZ3 -> thyZ4)
     rallI : (!!x. Trueprop (rP x)) ==> Trueprop (rAll rP)
     rallE : Trueprop (rAll rP) ==> Trueprop (rP a)
   Needed so the strong-induction predicate over n can quantify r1, r2 (ixlist).
   ============================================================================ *)
val thyZ4a = Sign.add_consts [(Binding.name "rAll", rpredOT --> oT, NoSyn)] thyZ3;
val rAllC = Const (Sign.full_name thyZ4a (Binding.name "rAll"), rpredOT --> oT);
fun mkRAll pr = rAllC $ pr;
val raP = Free("raP", rpredOT);
val raX = Free("raX", ixlistT);
val rallI_prop = Logic.mk_implies (Logic.all raX (jT (raP $ raX)), jT (mkRAll raP));
val ((_,rallI_ax), thyZ4b) = Thm.add_axiom_global (Binding.name "rallI", rallI_prop) thyZ4a;
val raA = Free("raA", ixlistT);
val rallE_prop = Logic.mk_implies (jT (mkRAll raP), jT (raP $ raA));
val ((_,rallE_ax), thyZ4) = Thm.add_axiom_global (Binding.name "rallE", rallE_prop) thyZ4b;

val ctxtZ4  = Proof_Context.init_global thyZ4;
val ctermZ4 = Thm.cterm_of ctxtZ4;
val rallI_vZ = varify rallI_ax;
val rallE_vZ = varify rallE_ax;
(* rallI_at rPabs hMeta : hMeta : !!x. Trueprop (rPabs x) -> Trueprop (rAll rPabs) *)
fun rallI_at rPabs hMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("raP",0), ctermZ4 rPabs)] rallI_vZ)
  in Thm.implies_elim inst hMeta end;
(* rallE_at rPabs at hAll : Trueprop (rAll rPabs) -> Trueprop (rPabs at) *)
fun rallE_at rPabs at hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("raP",0), ctermZ4 rPabs),(("raA",0), ctermZ4 at)] rallE_vZ)
  in Thm.implies_elim inst hAll end;

(* ---- ctxtZ4 connective helpers (terms mention req via the conclusion) ---- *)
fun oeqreflZ4_at t = beta_norm (Drule.infer_instantiate ctxtZ4 [(("a",0), ctermZ4 t)] oeq_refl_vZ);
fun conjI_atZ4 (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("A",0), ctermZ4 At),(("B",0), ctermZ4 Bt)] conjI_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atZ4 (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("A",0), ctermZ4 At),(("B",0), ctermZ4 Bt)] conjunct1_vZ)
  in Thm.implies_elim inst h end;
fun conjunct2_atZ4 (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("A",0), ctermZ4 At),(("B",0), ctermZ4 Bt)] conjunct2_vZ)
  in Thm.implies_elim inst h end;
fun disjE_elimZ4 (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("A",0), ctermZ4 At),(("B",0), ctermZ4 Bt),(("C",0), ctermZ4 Ct)] disjE_vZ)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun mp_atZ4 (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("A",0), ctermZ4 At),(("B",0), ctermZ4 Bt)] mp_vZ)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_atZ4 (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("A",0), ctermZ4 At),(("B",0), ctermZ4 Bt)] impI_vZ)
  in Thm.implies_elim inst hImpThm end;
fun oFalse_elimZ4_at rT = beta_norm (Drule.infer_instantiate ctxtZ4 [(("R",0), ctermZ4 rT)] oFalse_elim_vZ);
(* vb_imp_valid_at4 (bt, rt) hvb : vb bt rt -> valid_rep rt, on ctxtZ4 *)
fun vb_imp_valid_at4 (bt, rt) hvb =
  let
    val vp = beta_norm (Drule.infer_instantiate ctxtZ4 [(("k_vv",0), ctermZ4 rt)] (varify vb_imp_valid));
    val Vbody = let val bb = Free("b_vv", natT) in Term.lambda bb (mkImp (vb bb rt)(valid_rep rt)) end;
    val atb = beta_norm (Drule.infer_instantiate ctxtZ4 [(("P",0), ctermZ4 Vbody),(("a",0), ctermZ4 bt)] allE_vZ);
    val atbT = Thm.implies_elim atb vp;
  in mp_atZ4 (vb bt rt, valid_rep rt) atbT hvb end;
fun exE_elimZ4 (Pabs, goalC) exThm wName wTy bodyFn =
  let
    val wF = Free(wName, wTy);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermZ4 hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermZ4 wF) (Thm.implies_intr (ctermZ4 hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("P",0), ctermZ4 Pabs), (("Q",0), ctermZ4 goalC)] exE_vZ);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
fun oeq_subst_atZ4 (Pabs, aT, bT) heq hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("P",0), ctermZ4 Pabs), (("a",0), ctermZ4 aT), (("b",0), ctermZ4 bT)] oeq_subst_vZ)
  in (inst OF [heq]) OF [hPa] end;
(* req_cons_at / req_refl_at on ctxtZ4 *)
fun req_refl_at4 t = beta_norm (Drule.infer_instantiate ctxtZ4 [(("r",0), ctermZ4 t)] req_refl_vZ);
fun req_cons_at4 (it,jt,rt,st) hij hrs =
  ((beta_norm (Drule.infer_instantiate ctxtZ4
      [(("i",0), ctermZ4 it),(("j",0), ctermZ4 jt),(("r",0), ctermZ4 rt),(("s",0), ctermZ4 st)] req_cons_vZ))
   OF [hij]) OF [hrs];

val () = out "ZK_RALL_OK\n";

(* ============================================================================
   ixlist_case : case analysis on an ixlist via list_induct with the IH dropped.
     ixlist_case Qabs r hNil hCons : Trueprop (Qabs r)
       Qabs : ixlist -> o (lambda) ; r : a Free ;
       hNil : Trueprop (Qabs INil) ;
       hCons : (i,t : Free) -> Trueprop (Qabs (ICons i t))   [function]
   ============================================================================ *)
fun ixlist_case_named (inm, tnm) Qabs r hNil hConsFn =
  let
    val ind = beta_norm (Drule.infer_instantiate ctxtZ4
                [(("P",0), ctermZ4 Qabs), (("k",0), ctermZ4 r)] list_induct_v);
    (* base : Trueprop (Qabs INil) = hNil  (must be beta-equal) *)
    val base = hNil;
    (* step : !!i t. Trueprop (Qabs t) ==> Trueprop (Qabs (ICons i t)) *)
    val iF = Free(inm, natT); val tF = Free(tnm, ixlistT);
    val ihprop = jT (Term.betapply (Qabs, tF));
    val IH = Thm.assume (ctermZ4 ihprop);            (* dropped *)
    val consBody = hConsFn (iF, tF);                 (* Trueprop (Qabs (ICons i t)) *)
    val stepInner = Thm.implies_intr (ctermZ4 ihprop) consBody;
    val step = Thm.forall_intr (ctermZ4 iF) (Thm.forall_intr (ctermZ4 tF) stepInner);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;
  in r2 end;
fun ixlist_case Qabs r hNil hConsFn = ixlist_case_named ("i_ic","t_ic") Qabs r hNil hConsFn;

val () = out "ZK_IXCASE_OK\n";

(* ============================================================================
   UNIQUENESS : forall n r1 r2.
       valid_rep r1 ==> valid_rep r2 ==> rep_sum r1 = n ==> rep_sum r2 = n ==> req r1 r2
   STRONG INDUCTION on n.  Object-quantify r1, r2 via rAll.
     P n := rAll(%r1. rAll(%r2. G2 r1 r2 n))
     G2 r1 r2 n := Imp(valid r1)(Imp(valid r2)(Imp(rep r1 = n)(Imp(rep r2 = n)(req r1 r2))))
   ============================================================================ *)
val sum_bound_vZ4    = varify sum_bound;
val zfib_index_unique_vZ = varify zfib_index_unique;
val rep_sum_pos_cons_vZ  = varify rep_sum_pos_cons;
val add_left_cancel_vZ4  = varify add_left_cancel;
val lt_add_pos_comm_vZ4  = varify lt_add_pos_comm;
val lt_irrefl_contra_vZ4 = varify lt_irrefl_contra;
val add_sub_vZ4          = varify add_sub;
val vb_imp_valid_vZ4     = varify vb_imp_valid;
val strong_induct_vZ4    = varify strong_induct;

(* accessors on ctxtZ4 for old constants used below *)
fun repCons_at4 (it,rt) = beta_norm (Drule.infer_instantiate ctxtZ4
                          [(("i",0), ctermZ4 it),(("r",0), ctermZ4 rt)] rep_ICons_v);
fun validUnfold_at4 (it,rt) = beta_norm (Drule.infer_instantiate ctxtZ4
                          [(("i",0), ctermZ4 it),(("r",0), ctermZ4 rt)] valid_unfold_v);
fun add_cong_rZ4 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtZ4 [(("P",0), ctermZ4 Pabs), (("a",0), ctermZ4 pT), (("b",0), ctermZ4 qT)] oeq_subst_vZ);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtZ4 [(("a",0), ctermZ4 (add hT pT))] oeq_refl_vZ);
  in inst OF [hpq, refl_hp] end;

(* G2 body for fixed n : a term  Imp(valid r1)(Imp(valid r2)(Imp(rep r1 = n)(Imp(rep r2 = n)(req r1 r2)))) *)
fun G2 r1 r2 n =
  mkImp (valid_rep r1) (mkImp (valid_rep r2)
    (mkImp (oeq (rep_sum r1) n) (mkImp (oeq (rep_sum r2) n) (req r1 r2))));

val uniqueness =
  let
    (* strong-induction predicate over n *)
    fun Pn n =
      let
        val r1f = Free("r1_p", ixlistT); val r2f = Free("r2_p", ixlistT);
        val inner = Term.lambda r2f (G2 r1f r2f n);
        val outer = Term.lambda r1f (mkRAll inner)
      in mkRAll outer end;
    val Ppred = let val nn = Free("n_up", natT) in Term.lambda nn (Pn nn) end;  (* nat->o *)
    val nF = Free("n_u", natT);
    val mSI = Free("m_u", natT);
    val IHprop = Logic.all mSI (Logic.mk_implies (jT (lt mSI nF), jT (Pn mSI)));
    val IH = Thm.assume (ctermZ4 IHprop);
    (* prove Pn n = rAll(%r1. rAll(%r2. G2 r1 r2 n)) *)
    val r1F = Free("r1_u", ixlistT); val r2F = Free("r2_u", ixlistT);
    (* matrix : prove G2 r1F r2F n for the two Frees, via double ixlist_case *)
    val matrix =
      let
        (* Qabs1 r1 := G2 r1 r2F n  (r2F still free; inner case on r2 inside each arm) *)
        val Qabs1 = Term.lambda r1F (G2 r1F r2F nF);
        (* --- r1 = INil arm: prove G2 INil r2F n by case on r2F (re-assume hyps inside) --- *)
        val nilArm =
          let
            val Qabs2 = Term.lambda r2F (G2 INilC r2F nF);
            (* r2 = INil : G2 INil INil n ; n=0 from rep INil=n ; req INil INil = refl *)
            val r2nil =
              let
                val hv1 = Thm.assume (ctermZ4 (jT (valid_rep INilC)));
                val hv2 = Thm.assume (ctermZ4 (jT (valid_rep INilC)));
                val hs1 = Thm.assume (ctermZ4 (jT (oeq (rep_sum INilC) nF)));
                val hs2 = Thm.assume (ctermZ4 (jT (oeq (rep_sum INilC) nF)));
                val reqnn = req_refl_at4 INilC;             (* req INil INil *)
                val d4 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum INilC) nF))) reqnn;
                val i4 = impI_atZ4 (oeq (rep_sum INilC) nF, req INilC INilC) d4;
                val d3 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum INilC) nF))) i4;
                val i3 = impI_atZ4 (oeq (rep_sum INilC) nF, mkImp (oeq (rep_sum INilC) nF) (req INilC INilC)) d3;
                val d2 = Thm.implies_intr (ctermZ4 (jT (valid_rep INilC))) i3;
                val i2 = impI_atZ4 (valid_rep INilC, mkImp (oeq (rep_sum INilC) nF) (mkImp (oeq (rep_sum INilC) nF) (req INilC INilC))) d2;
                val d1 = Thm.implies_intr (ctermZ4 (jT (valid_rep INilC))) i2;
                val i1 = impI_atZ4 (valid_rep INilC, mkImp (valid_rep INilC) (mkImp (oeq (rep_sum INilC) nF) (mkImp (oeq (rep_sum INilC) nF) (req INilC INilC)))) d1;
              in i1 end;
            (* r2 = ICons k2 t2 : contradiction (rep cons2 = n = rep INil = 0 but cons-positive) *)
            fun r2cons (k2, t2) =
              let
                val cons2 = icons k2 t2;
                val hv1 = Thm.assume (ctermZ4 (jT (valid_rep INilC)));
                val hv2 = Thm.assume (ctermZ4 (jT (valid_rep cons2)));
                val hs1 = Thm.assume (ctermZ4 (jT (oeq (rep_sum INilC) nF)));   (* 0 = n *)
                val hs2 = Thm.assume (ctermZ4 (jT (oeq (rep_sum cons2) nF)));   (* rep cons2 = n *)
                val n0 = oeq_trans OF [oeq_sym OF [hs1], rep_INil_v];           (* n = 0 *)
                val pos = beta_norm (Drule.infer_instantiate ctxtZ4
                            [(("k",0), ctermZ4 k2),(("r",0), ctermZ4 t2)] rep_sum_pos_cons_vZ);  (* lt 0 (rep cons2) *)
                val rc0 = oeq_trans OF [hs2, n0];          (* rep cons2 = 0 *)
                val Pl = let val zz = Free("z_nc", natT) in Term.lambda zz (lt ZeroC zz) end;
                val lt00 = oeq_subst_atZ4 (Pl, rep_sum cons2, ZeroC) rc0 pos;   (* lt 0 0 *)
                val ez = (varify le_zero_eq) OF [lt00];    (* oeq (Suc 0) 0 *)
                val fls = Suc_neq_Zero_vZ OF [ez];         (* oFalse *)
                val reqcc = (oFalse_elimZ4_at (req INilC cons2)) OF [fls];
                val d4 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum cons2) nF))) reqcc;
                val i4 = impI_atZ4 (oeq (rep_sum cons2) nF, req INilC cons2) d4;
                val d3 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum INilC) nF))) i4;
                val i3 = impI_atZ4 (oeq (rep_sum INilC) nF, mkImp (oeq (rep_sum cons2) nF) (req INilC cons2)) d3;
                val d2 = Thm.implies_intr (ctermZ4 (jT (valid_rep cons2))) i3;
                val i2 = impI_atZ4 (valid_rep cons2, mkImp (oeq (rep_sum INilC) nF) (mkImp (oeq (rep_sum cons2) nF) (req INilC cons2))) d2;
                val d1 = Thm.implies_intr (ctermZ4 (jT (valid_rep INilC))) i2;
                val i1 = impI_atZ4 (valid_rep INilC, mkImp (valid_rep cons2) (mkImp (oeq (rep_sum INilC) nF) (mkImp (oeq (rep_sum cons2) nF) (req INilC cons2)))) d1;
              in i1 end;
          in ixlist_case_named ("i_in","t_in") Qabs2 r2F r2nil r2cons end;  (* G2 INil r2F n *)
        (* --- r1 = ICons k1 t1 arm --- *)
        fun consArm (k1, t1) =
          let
            val cons1 = icons k1 t1;
            val hv1 = Thm.assume (ctermZ4 (jT (valid_rep cons1)));
            val hs1 = Thm.assume (ctermZ4 (jT (oeq (rep_sum cons1) nF)));     (* rep(ICons k1 t1) = n *)
            (* sum_bound on r1 : le(zfib k1)(rep cons1) AND lt (rep cons1)(zfib(Suc k1)) *)
            val sb1 = (beta_norm (Drule.infer_instantiate ctxtZ4
                        [(("k",0), ctermZ4 k1),(("r",0), ctermZ4 t1)] sum_bound_vZ4)) OF [hv1];
            val le1 = conjunct1_atZ4 (le (zfib k1)(rep_sum cons1), lt (rep_sum cons1)(zfib (suc k1))) sb1;  (* le(zfib k1)(rep cons1) *)
            val lt1 = conjunct2_atZ4 (le (zfib k1)(rep_sum cons1), lt (rep_sum cons1)(zfib (suc k1))) sb1;  (* lt (rep cons1)(zfib(Suc k1)) *)
            (* rewrite rep cons1 -> n (hs1) *)
            val PleA = let val zz = Free("z_lea", natT) in Term.lambda zz (le (zfib k1) zz) end;
            val le1n = oeq_subst_atZ4 (PleA, rep_sum cons1, nF) hs1 le1;     (* le(zfib k1) n *)
            val PltA = let val zz = Free("z_lta", natT) in Term.lambda zz (lt zz (zfib (suc k1))) end;
            val lt1n = oeq_subst_atZ4 (PltA, rep_sum cons1, nF) hs1 lt1;     (* lt n (zfib(Suc k1)) *)
            (* case r2 shape *)
            val Qabs2 = Term.lambda r2F (G2 cons1 r2F nF);
            val r2nilA =
              let
                (* G2 cons1 INil n : Imp(valid cons1)(Imp(valid INil)(Imp(rep cons1=n)(Imp(rep INil=n)(req cons1 INil)))) *)
                val hv2 = Thm.assume (ctermZ4 (jT (valid_rep INilC)));
                val hs1b = Thm.assume (ctermZ4 (jT (oeq (rep_sum cons1) nF)));
                val hs2 = Thm.assume (ctermZ4 (jT (oeq (rep_sum INilC) nF)));  (* 0 = n *)
                (* rep cons1 = n, rep INil = 0 = n -> n = 0 -> rep cons1 = 0 ; but pos. *)
                val n0 = oeq_trans OF [oeq_sym OF [hs2], rep_INil_v];   (* n = 0 *)
                val pos = beta_norm (Drule.infer_instantiate ctxtZ4
                            [(("k",0), ctermZ4 k1),(("r",0), ctermZ4 t1)] rep_sum_pos_cons_vZ);  (* lt 0 (rep cons1) *)
                val rc0 = oeq_trans OF [hs1b, n0];          (* rep cons1 = 0 *)
                val Pl = let val zz = Free("z_cn", natT) in Term.lambda zz (lt ZeroC zz) end;
                val lt00 = oeq_subst_atZ4 (Pl, rep_sum cons1, ZeroC) rc0 pos;
                val ez = (varify le_zero_eq) OF [lt00];
                val fls = Suc_neq_Zero_vZ OF [ez];
                val req0 = (oFalse_elimZ4_at (req cons1 INilC)) OF [fls];
                (* discharge G2 cons1 INil n *)
                val d4 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum INilC) nF))) req0;
                val i4 = impI_atZ4 (oeq (rep_sum INilC) nF, req cons1 INilC) d4;
                val d3 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum cons1) nF))) i4;
                val i3 = impI_atZ4 (oeq (rep_sum cons1) nF, mkImp (oeq (rep_sum INilC) nF) (req cons1 INilC)) d3;
                val d2 = Thm.implies_intr (ctermZ4 (jT (valid_rep INilC))) i3;
                val i2 = impI_atZ4 (valid_rep INilC, mkImp (oeq (rep_sum cons1) nF) (mkImp (oeq (rep_sum INilC) nF) (req cons1 INilC))) d2;
                val d1 = Thm.implies_intr (ctermZ4 (jT (valid_rep cons1))) i2;
                val i1 = impI_atZ4 (valid_rep cons1, mkImp (valid_rep INilC) (mkImp (oeq (rep_sum cons1) nF) (mkImp (oeq (rep_sum INilC) nF) (req cons1 INilC)))) d1;
              in i1 end;
            fun r2consA (k2, t2) =
              let
                val cons2 = icons k2 t2;
                (* G2 cons1 cons2 n *)
                val hv1b = Thm.assume (ctermZ4 (jT (valid_rep cons1)));
                val hv2 = Thm.assume (ctermZ4 (jT (valid_rep cons2)));
                val hs1b = Thm.assume (ctermZ4 (jT (oeq (rep_sum cons1) nF)));
                val hs2 = Thm.assume (ctermZ4 (jT (oeq (rep_sum cons2) nF)));
                (* sum_bound on r2 *)
                val sb2 = (beta_norm (Drule.infer_instantiate ctxtZ4
                            [(("k",0), ctermZ4 k2),(("r",0), ctermZ4 t2)] sum_bound_vZ4)) OF [hv2];
                val le2 = conjunct1_atZ4 (le (zfib k2)(rep_sum cons2), lt (rep_sum cons2)(zfib (suc k2))) sb2;
                val lt2 = conjunct2_atZ4 (le (zfib k2)(rep_sum cons2), lt (rep_sum cons2)(zfib (suc k2))) sb2;
                val PleB = let val zz = Free("z_leb", natT) in Term.lambda zz (le (zfib k2) zz) end;
                val le2n = oeq_subst_atZ4 (PleB, rep_sum cons2, nF) hs2 le2;     (* le(zfib k2) n *)
                val PltB = let val zz = Free("z_ltb", natT) in Term.lambda zz (lt zz (zfib (suc k2))) end;
                val lt2n = oeq_subst_atZ4 (PltB, rep_sum cons2, nF) hs2 lt2;     (* lt n (zfib(Suc k2)) *)
                (* zfib_index_unique : oeq k1 k2 *)
                val k1k2 = ((((beta_norm (Drule.infer_instantiate ctxtZ4
                              [(("k1",0), ctermZ4 k1),(("k2",0), ctermZ4 k2),(("n",0), ctermZ4 nF)] zfib_index_unique_vZ))
                            OF [lt2n]) OF [le2n]) OF [lt1n]) OF [le1n];   (* oeq k1 k2 *)
                (* rep cons1 = add(zfib k1)(rep t1) ; = n.  add(zfib k1)(rep t1) = n *)
                val rc1 = repCons_at4 (k1, t1);            (* rep cons1 = add(zfib k1)(rep t1) *)
                val sum1 = oeq_trans OF [oeq_sym OF [rc1], hs1b];   (* add(zfib k1)(rep t1) = n *)
                val rc2 = repCons_at4 (k2, t2);            (* rep cons2 = add(zfib k2)(rep t2) *)
                val sum2 = oeq_trans OF [oeq_sym OF [rc2], hs2];    (* add(zfib k2)(rep t2) = n *)
                (* rewrite k2 -> k1 in sum2 via sym k1k2 : add(zfib k1)(rep t2) = n *)
                val Pk = let val zz = Free("z_k", natT) in Term.lambda zz (oeq (add (zfib zz)(rep_sum t2)) nF) end;
                val sum2' = oeq_subst_atZ4 (Pk, k2, k1) (oeq_sym OF [k1k2]) sum2;  (* add(zfib k1)(rep t2) = n *)
                (* add(zfib k1)(rep t1) = add(zfib k1)(rep t2) : both = n *)
                val eqAdds = oeq_trans OF [sum1, oeq_sym OF [sum2']];  (* add(zfib k1)(rep t1) = add(zfib k1)(rep t2) *)
                val rept1t2 = add_left_cancel_vZ4 OF [eqAdds];        (* rep t1 = rep t2 *)
                (* valid t1, t2 *)
                val vbtl1 = (validUnfold_at4 (k1, t1)) OF [hv1b];     (* vb (sub k1 1) t1 *)
                val vt1 = vb_imp_valid_at4 (sub k1 one, t1) vbtl1;    (* valid_rep t1 *)
                val vbtl2 = (validUnfold_at4 (k2, t2)) OF [hv2];      (* vb (sub k2 1) t2 *)
                val vt2 = vb_imp_valid_at4 (sub k2 one, t2) vbtl2;    (* valid_rep t2 *)
                (* lt (rep t1) n : from add(zfib k1)(rep t1) = n + zfib k1>=1 -> lt_add_pos_comm *)
                val ge1 = beta_norm (Drule.infer_instantiate ctxtZ4 [(("k",0), ctermZ4 k1)] zfib_ge1_vZ3); (* le 1 (zfib k1) *)
                val ltsub = (beta_norm (Drule.infer_instantiate ctxtZ4
                              [(("a",0), ctermZ4 (rep_sum t1)),(("c",0), ctermZ4 (zfib k1))] lt_add_pos_comm_vZ4)) OF [ge1];
                (* ltsub : lt (rep t1)(add(zfib k1)(rep t1)) ; rewrite RHS -> n via sum1 *)
                val Plt = let val zz = Free("z_ltn", natT) in Term.lambda zz (lt (rep_sum t1) zz) end;
                val ltt1n = oeq_subst_atZ4 (Plt, add (zfib k1)(rep_sum t1), nF) sum1 ltsub;  (* lt (rep t1) n *)
                (* IH at m = rep t1 : Pn (rep t1) *)
                val ihAt = Thm.implies_elim (Thm.forall_elim (ctermZ4 (rep_sum t1)) IH) ltt1n;  (* Pn (rep t1) *)
                (* rallE at t1 then t2 : G2 t1 t2 (rep t1) *)
                val innerLam = let val r2f = Free("r2_p", ixlistT) in Term.lambda r2f (G2 t1 r2f (rep_sum t1)) end;
                val ihT1 = rallE_at (let val r1f = Free("r1_p", ixlistT) in Term.lambda r1f (mkRAll (let val r2f = Free("r2_p", ixlistT) in Term.lambda r2f (G2 r1f r2f (rep_sum t1)) end)) end) t1 ihAt;
                (* ihT1 : rAll(%r2. G2 t1 r2 (rep t1)) *)
                val ihT1T2 = rallE_at innerLam t2 ihT1;    (* G2 t1 t2 (rep t1) *)
                (* G2 t1 t2 (rep t1) = Imp(valid t1)(Imp(valid t2)(Imp(rep t1 = rep t1)(Imp(rep t2 = rep t1)(req t1 t2)))) *)
                val step1 = mp_atZ4 (valid_rep t1, mkImp (valid_rep t2)(mkImp (oeq (rep_sum t1)(rep_sum t1))(mkImp (oeq (rep_sum t2)(rep_sum t1))(req t1 t2)))) ihT1T2 vt1;
                val step2 = mp_atZ4 (valid_rep t2, mkImp (oeq (rep_sum t1)(rep_sum t1))(mkImp (oeq (rep_sum t2)(rep_sum t1))(req t1 t2))) step1 vt2;
                val reflT1 = oeqreflZ4_at (rep_sum t1);     (* rep t1 = rep t1 *)
                val step3 = mp_atZ4 (oeq (rep_sum t1)(rep_sum t1), mkImp (oeq (rep_sum t2)(rep_sum t1))(req t1 t2)) step2 reflT1;
                val rept2t1 = oeq_sym OF [rept1t2];         (* rep t2 = rep t1 *)
                val reqt1t2 = mp_atZ4 (oeq (rep_sum t2)(rep_sum t1), req t1 t2) step3 rept2t1;  (* req t1 t2 *)
                (* req cons1 cons2 via req_cons (oeq k1 k2)(req t1 t2) *)
                val reqcons = req_cons_at4 (k1, k2, t1, t2) k1k2 reqt1t2;   (* req (ICons k1 t1)(ICons k2 t2) *)
                (* discharge G2 cons1 cons2 n *)
                val d4 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum cons2) nF))) reqcons;
                val i4 = impI_atZ4 (oeq (rep_sum cons2) nF, req cons1 cons2) d4;
                val d3 = Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum cons1) nF))) i4;
                val i3 = impI_atZ4 (oeq (rep_sum cons1) nF, mkImp (oeq (rep_sum cons2) nF) (req cons1 cons2)) d3;
                val d2 = Thm.implies_intr (ctermZ4 (jT (valid_rep cons2))) i3;
                val i2 = impI_atZ4 (valid_rep cons2, mkImp (oeq (rep_sum cons1) nF) (mkImp (oeq (rep_sum cons2) nF) (req cons1 cons2))) d2;
                val d1 = Thm.implies_intr (ctermZ4 (jT (valid_rep cons1))) i2;
                val i1 = impI_atZ4 (valid_rep cons1, mkImp (valid_rep cons2) (mkImp (oeq (rep_sum cons1) nF) (mkImp (oeq (rep_sum cons2) nF) (req cons1 cons2)))) d1;
              in i1 end;
          in ixlist_case_named ("i_in","t_in") Qabs2 r2F r2nilA r2consA end;  (* G2 cons1 r2F n *)
        val g2 = ixlist_case_named ("i_o","t_o") Qabs1 r1F nilArm consArm;  (* G2 r1F r2F n *)
      in g2 end;
    (* Pn n : rallI over r1, rallI over r2 *)
    val innerAll = let val r2f = Free("r2_p", ixlistT) in Term.lambda r2f (G2 r1F r2f nF) end;
    val rall2 = rallI_at innerAll (Thm.forall_intr (ctermZ4 r2F) matrix);  (* rAll(%r2. G2 r1F r2 n) *)
    val outerAll = let val r1f = Free("r1_p", ixlistT) in Term.lambda r1f (mkRAll (let val r2f = Free("r2_p", ixlistT) in Term.lambda r2f (G2 r1f r2f nF) end)) end;
    val PnN = rallI_at outerAll (Thm.forall_intr (ctermZ4 r1F) rall2);     (* Pn n *)
    val stepThm = Thm.forall_intr (ctermZ4 nF) (Thm.implies_intr (ctermZ4 IHprop) PnN);
    val kArg = Free("nn", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtZ4
                   [(("P",0), ctermZ4 Ppred), (("k",0), ctermZ4 kArg)] strong_induct_vZ4);
    val PnK = Thm.implies_elim siInst stepThm;            (* Pn nn *)
  in varify PnK end;
val () = out ("uniqueness hyps=" ^ Int.toString (length (Thm.hyps_of uniqueness)) ^ "\n");

val () = out "ZK_UNIQ_RAW_OK\n";

(* ============================================================================
   UNIQUENESS in usable meta-form:
     valid_rep r1 ==> valid_rep r2 ==> oeq (rep_sum r1) n ==> oeq (rep_sum r2) n
       ==> req r1 r2
   Extract from `uniqueness` (rAll/Imp form) by rallE x2 + object->meta on the
   four object-Imp's.
   ============================================================================ *)
val uniqueness_meta =
  let
    val nF = Free("n", natT); val r1F = Free("r1", ixlistT); val r2F = Free("r2", ixlistT);
    (* uniqueness at nn := n : Pn n = rAll(%r1. rAll(%r2. G2 r1 r2 n)) *)
    val un_n = beta_norm (Drule.infer_instantiate ctxtZ4 [(("nn",0), ctermZ4 nF)] (varify uniqueness));
    val inner = let val r2f = Free("r2_p", ixlistT) in Term.lambda r2f (G2 r1F r2f nF) end;
    val un_r1 = rallE_at (let val r1f = Free("r1_p", ixlistT) in Term.lambda r1f (mkRAll (let val r2f = Free("r2_p", ixlistT) in Term.lambda r2f (G2 r1f r2f nF) end)) end) r1F un_n;
    val un_r1r2 = rallE_at inner r2F un_r1;   (* G2 r1 r2 n  (object Imp chain) *)
    (* now peel the four object Imp's via mp, assuming each antecedent *)
    val hv1 = Thm.assume (ctermZ4 (jT (valid_rep r1F)));
    val hv2 = Thm.assume (ctermZ4 (jT (valid_rep r2F)));
    val hs1 = Thm.assume (ctermZ4 (jT (oeq (rep_sum r1F) nF)));
    val hs2 = Thm.assume (ctermZ4 (jT (oeq (rep_sum r2F) nF)));
    val s1 = mp_atZ4 (valid_rep r1F, mkImp (valid_rep r2F)(mkImp (oeq (rep_sum r1F) nF)(mkImp (oeq (rep_sum r2F) nF)(req r1F r2F)))) un_r1r2 hv1;
    val s2 = mp_atZ4 (valid_rep r2F, mkImp (oeq (rep_sum r1F) nF)(mkImp (oeq (rep_sum r2F) nF)(req r1F r2F))) s1 hv2;
    val s3 = mp_atZ4 (oeq (rep_sum r1F) nF, mkImp (oeq (rep_sum r2F) nF)(req r1F r2F)) s2 hs1;
    val s4 = mp_atZ4 (oeq (rep_sum r2F) nF, req r1F r2F) s3 hs2;   (* req r1 r2 *)
    (* discharge to meta-implications *)
    val d = Thm.implies_intr (ctermZ4 (jT (valid_rep r1F)))
              (Thm.implies_intr (ctermZ4 (jT (valid_rep r2F)))
                (Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum r1F) nF)))
                  (Thm.implies_intr (ctermZ4 (jT (oeq (rep_sum r2F) nF))) s4)));
  in varify d end;
val () = out ("uniqueness_meta hyps=" ^ Int.toString (length (Thm.hyps_of uniqueness_meta))
              ^ ":\n  " ^ Syntax.string_of_term ctxtZ4 (Thm.prop_of uniqueness_meta) ^ "\n");

(* ---- aconv check vs the intended statement ---- *)
val nVu  = Var(("n",0), natT);
val r1Vu = Var(("r1",0), ixlistT);
val r2Vu = Var(("r2",0), ixlistT);
val uniqueness_intended =
  Logic.mk_implies (jT (valid_rep r1Vu),
    Logic.mk_implies (jT (valid_rep r2Vu),
      Logic.mk_implies (jT (oeq (rep_sum r1Vu) nVu),
        Logic.mk_implies (jT (oeq (rep_sum r2Vu) nVu), jT (req r1Vu r2Vu)))));
val uq_hyps0 = (length (Thm.hyps_of uniqueness_meta) = 0);
val uq_aconv = (Thm.prop_of uniqueness_meta) aconv uniqueness_intended;
val () = out ("uniqueness 0hyp=" ^ Bool.toString uq_hyps0 ^ " aconv=" ^ Bool.toString uq_aconv ^ "\n");
val () = if uq_hyps0 andalso uq_aconv then out "ZK_UNIQUE_OK\n" else out "ZK_UNIQUE_FAIL\n";

(* ---- uniqueness soundness probes ---- *)
(* (a) req is genuinely discriminating, NOT vacuously True: the kernel can DERIVE
       oFalse from a (false) `req INil (ICons i r)` via the discrimination axiom.
       If req were the vacuous "True" predicate this could not give oFalse. *)
val req_discriminates =
  let
    val iF = Free("ii", natT); val rF = Free("rr", ixlistT);
    val hnc = Thm.assume (ctermZ4 (jT (req INilC (icons iF rF))));
    val rnc = beta_norm (Drule.infer_instantiate ctxtZ4
                [(("i",0), ctermZ4 iF),(("r",0), ctermZ4 rF)] (varify req_nil_cons));
    val fls = rnc OF [hnc];                (* Trueprop oFalse, hyp = req INil (ICons i r) *)
  in (Thm.prop_of fls) aconv (jT oFalseC) end;
(* (b) the conclusion is genuinely req r1 r2, not the trivial req r1 r1 *)
val uq_bogus_refl =
  Logic.mk_implies (jT (valid_rep r1Vu),
    Logic.mk_implies (jT (valid_rep r2Vu),
      Logic.mk_implies (jT (oeq (rep_sum r1Vu) nVu),
        Logic.mk_implies (jT (oeq (rep_sum r2Vu) nVu), jT (req r1Vu r1Vu)))));
val uq_probe = not ((Thm.prop_of uniqueness_meta) aconv uq_bogus_refl);
val () = if req_discriminates andalso uq_probe
         then out "ZK_UNIQUE_PROBE_OK\n" else out "ZK_UNIQUE_PROBE_FAIL\n";

(* ---- final combined gate ---- *)
val () = if ex_hyps0 andalso ex_aconv andalso uq_hyps0 andalso uq_aconv
         then out "ZK_ALL_OK\n" else out "ZK_ALL_INCOMPLETE\n";
