(* ======================================================================
   WILSON'S IFF — the full primality criterion, in Isabelle/Pure.

     wilson_iff : ⊢ 1 < n ⟹ (prime2 n ⟺ cong n ((n−1)!) (n−1))

   i.e. for n > 1, n is (structurally) prime IFF (n−1)! ≡ −1 (mod n).
   ((n−1)! = lprod (upto (n−1)); −1 ≡ n−1 mod n; ⟺ = Conj of the two
   implications; prime2 = the genuine structural prime.)

   Spliced via common::with_wilson (= …→wilson_inverse→isabelle_wilson,
   carrying the PROVEN Wilson theorem). This file = the Wilson CONVERSE
   delta (isabelle_wilson_converse.sml, proving wc_converse: composite n,
   4<n ⟹ (n−1)! ≡ 0) FOLLOWED BY the iff-assembly delta. Both wilson and
   wc_converse are PROVEN theorems — NOT re-axiomatized; the delta adds 0
   axioms. Only classical assumption = ex_middle (via the derived
   prime_cases case-split).

   Forward: instantiate the proven `wilson` at n. Backward (contrapositive):
   1<n ∧ ¬prime2 n ⟹ composite; the 4<n case applies wc_converse (≡0≢−1
   since 0<n−1<n); the n=4 case is computed from scratch (3!=6≡2≢3).

   ultracode wf_1c71659d-8ce. Markers: WILSON_IFF_OK + WIFF_DELTA_DONE.
   ====================================================================== *)

(* ============================================================================
   WILSON'S CONVERSE — BASE + SCAFFOLDING (delta on the with_wilson_inverse chain).
   ----------------------------------------------------------------------------
   Establishes, on the final Wilson context (thyW / ctxtW / ctermW):

     factorial n  := lprod (upto (sub n 1))            [ = (n-1)! ]
     composite n  := ?a. 1<a /\ a<n /\ a | n           [ object-level conjunction ]

   and proves the two scaffolding lemmas the converse seats need, each 0-hyp:

     key_div_pair :  ~(oeq x y) ==> lmem x L ==> lmem y L
                       ==> dvd (mult x y) (lprod L)
        (two distinct list members x<>y => x*y divides the list product;
         via `extract` x, then `extract` y in lremove x L (mem_remove_bwd))

     factor_in_range : 1<a ==> a<n ==> lmem a (upto (sub n 1))
        (a factor of n in [2..n-1] sits in the factorial's factor list)

   No new constant, no new axiom: factorial/composite are ML abbreviations over
   the existing lprod/upto/sub/dvd/mult/lt machinery, and the lemmas are pure
   kernel inference re-using `extract`, `mem_remove_bwd`, `lmem_upto_bwd` from the
   chain.  Markers: BASE_OK on success.
   ============================================================================ *)
val () = out "WC_BASE_BEGIN\n";

(* ---- ML abbreviations (term builders) ---- *)
val oneC = suc ZeroC;
fun factorial n = lprod (uptoF (sub n oneC));
fun composite n =
  mkEx (Term.lambda (Free("a_co", natT))
    (mkConj (lt oneC (Free("a_co", natT)))
       (mkConj (lt (Free("a_co", natT)) n)
               (dvd (Free("a_co", natT)) n))));

(* sanity: the abbreviations build a well-typed cterm on ctxtW *)
val () = (ignore (ctermW (jT (oeq (factorial (Free("n",natT))) (factorial (Free("n",natT))))));
          ignore (ctermW (jT (composite (Free("n",natT)))));
          out "WC_DEFS_TYPECHECK_OK\n");

(* ---- re-varify the list lemmas we reuse onto ctxtW ---- *)
val extract_vW         = varify extract;
val mem_remove_bwd_vW  = varify mem_remove_bwd;

(* ---- combinators on ctxtW for the reused list lemmas ---- *)
(* extract : lmem x L ==> oeq (lprod L) (mult x (lprod (lremove x L))) *)
fun extract_W (xt, Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("x",0), ctermW xt),(("L",0), ctermW Lt)] extract_vW)
  in Thm.implies_elim inst hmem end;
(* mem_remove_bwd : Conj (lmem y L)(neg (oeq y x)) ==> lmem y (lremove x L) *)
fun mem_remove_bwd_W (yt, xt, Lt) hconj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("y",0), ctermW yt),(("x",0), ctermW xt),(("L",0), ctermW Lt)] mem_remove_bwd_vW)
  in Thm.implies_elim inst hconj end;

(* flip an inequality: neg (oeq x y) ==> neg (oeq y x)  (via oeq_sym).
   NOTE: neg A = Imp A oFalse is an OBJECT implication, so the result must be
   re-wrapped with impI_W (a meta implies_intr yields jT(oeq y x) ==> jT oFalse,
   which is NOT jT (neg (oeq y x))). *)
fun neg_oeq_flip_W (xt, yt) hneq =
  let val hyx = Thm.assume (ctermW (jT (oeq yt xt)))
      val hxy = oeq_sym_vW OF [hyx]                       (* oeq x y *)
      val fls = mp_W (oeq xt yt, oFalseC) hneq hxy        (* jT oFalse *)
      val metaImp = Thm.implies_intr (ctermW (jT (oeq yt xt))) fls
  in impI_W (oeq yt xt, oFalseC) metaImp end;             (* jT (neg (oeq y x)) *)

val () = out "WC_HELPERS_READY\n";

(* ============================================================================
   key_div_pair : ~(oeq x y) ==> lmem x L ==> lmem y L ==> dvd (mult x y)(lprod L)
   ----------------------------------------------------------------------------
   lprod L = x * lprod(lremove x L)            (extract x)
           = x * (y * lprod(lremove y (lremove x L)))   (extract y, y in lremove x L)
           = (x*y) * R                          (mult_assoc, R the residual product)
   so dvd (mult x y)(lprod L) with witness R.
   ============================================================================ *)
val key_div_pair =
  let
    val xF = Free("x", natT); val yF = Free("y", natT); val LF = Free("L", natlistT)
    val hneqP = jT (neg (oeq xF yF)) ; val hneq = Thm.assume (ctermW hneqP)
    val hmxP  = jT (lmem xF LF)      ; val hmx  = Thm.assume (ctermW hmxP)
    val hmyP  = jT (lmem yF LF)      ; val hmy  = Thm.assume (ctermW hmyP)

    (* extract x from L *)
    val e1 = extract_W (xF, LF) hmx                 (* oeq (lprod L) (mult x (lprod (lremove x L))) *)
    val rmx = lremove xF LF

    (* y is still in lremove x L : need neg (oeq y x), Conj (lmem y L)(neg (oeq y x)) *)
    val negYX = neg_oeq_flip_W (xF, yF) hneq        (* neg (oeq y x) *)
    val cjMY  = conjI_W (lmem yF LF, neg (oeq yF xF)) hmy negYX
    val hmy_rmx = mem_remove_bwd_W (yF, xF, LF) cjMY   (* lmem y (lremove x L) *)

    (* extract y from lremove x L *)
    val e2 = extract_W (yF, rmx) hmy_rmx            (* oeq (lprod (lremove x L)) (mult y R) *)
    val rmy = lremove yF rmx
    val Rt  = lprod rmy                             (* the residual product (witness) *)

    (* chain: lprod L = x * (y * R) *)
    val e2lift = mult_cong_r_W (xF, lprod rmx, mult yF Rt) e2   (* mult x (lprod rmx) = mult x (mult y R) *)
    val e_x_y_R = oeq_trans_vW OF [e1, e2lift]      (* lprod L = x * (y * R) *)

    (* x*(y*R) = (x*y)*R  via mult_assoc (sym) *)
    val assoc = multassoc_W (xF, yF, Rt)            (* (x*y)*R = x*(y*R) *)
    val assoc_s = oeq_sym_vW OF [assoc]             (* x*(y*R) = (x*y)*R *)
    val e_final = oeq_trans_vW OF [e_x_y_R, assoc_s]  (* lprod L = (x*y)*R *)

    (* dvd (mult x y)(lprod L) : witness R, body oeq (lprod L)(mult (mult x y) R) *)
    val dvdThm = dvd_intro_W (mult xF yF, lprod LF, Rt) e_final

    val d3 = Thm.implies_intr (ctermW hmyP) dvdThm
    val d2 = Thm.implies_intr (ctermW hmxP) d3
    val d1 = Thm.implies_intr (ctermW hneqP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of key_div_pair) = 0 then out "OK key_div_pair\n" else out "FAIL key_div_pair\n";

(* combinator form *)
fun key_div_pair_W (xt, yt, Lt) hneq hmx hmy =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("x",0), ctermW xt),(("y",0), ctermW yt),(("L",0), ctermW Lt)] key_div_pair)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hneq) hmx) hmy end;

(* ============================================================================
   factor_in_range : 1<a ==> a<n ==> lmem a (upto (sub n 1))
   ----------------------------------------------------------------------------
   need Conj (lt 0 a)(le a (sub n 1)), then lmem_upto_bwd.
     lt 0 a  : from 1<a (= lt 1 a = le 2 a) and le 1 2, transitivity.
     le a (sub n 1) : a<n with n = Suc q (n>1 from a>1), so sub n 1 = q and
                      a < Suc q ==> a <= q = sub n 1  (lt_suc_imp_le).
   ============================================================================ *)
val factor_in_range =
  let
    val aF = Free("a", natT); val nF = Free("n", natT)
    val h1aP = jT (lt oneC aF)  ; val h1a = Thm.assume (ctermW h1aP)
    val hanP = jT (lt aF nF)    ; val han = Thm.assume (ctermW hanP)

    (* lt 0 a  =  le 1 a *)
    val le_1_2 =
      let val aSr = addSr_W (oneC, ZeroC)
          val a0r = add0r_W oneC
          val s   = Suc_cong_vW OF [a0r]
          val sum = oeq_trans_vW OF [aSr, s]
          val sumS= oeq_sym_vW OF [sum]
      in le_intro_W (oneC, suc oneC, suc ZeroC) sumS end
    val lt0a = le_trans_W (oneC, suc oneC, aF) le_1_2 h1a   (* le 1 a = lt 0 a *)

    (* n = Suc q  (n>1 since 1<a<n => 1<n) *)
    val lt1n = lt_trans_W (oneC, aF, nF) h1a han            (* lt 1 n *)
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                   [(("p",0), ctermW nF)] pos_pred)) lt1n   (* Ex q. oeq n (Suc q) *)
    val goalC = lmem aF (uptoF (sub nF oneC))
    fun predBody q (hq:thm) =                                (* hq : oeq n (Suc q) *)
      let
        (* sub n 1 = q : from sub (Suc q) 1 = q  rewritten by n = Suc q (sym) *)
        val e1 = subSS_W (q, ZeroC)
        val e2 = sub0_W q
        val subSucq = oeq_trans_vW OF [e1, e2]               (* sub (Suc q) 1 = q *)
        val hq_s = oeq_sym_vW OF [hq]                        (* Suc q = n *)
        val Psub = Term.lambda (Free("z_su", natT)) (oeq (sub (Free("z_su", natT)) oneC) q)
        val subN_q = oeq_rw_W (Psub, suc q, nF) hq_s subSucq (* sub n 1 = q *)

        (* a < n rewritten to a < Suc q *)
        val Plt = Term.lambda (Free("z_lt", natT)) (lt aF (Free("z_lt", natT)))
        val ltaSq = oeq_rw_W (Plt, nF, suc q) hq han         (* lt a (Suc q) *)
        val le_a_q = lt_suc_imp_le_W (aF, q) ltaSq           (* le a q *)

        (* le a q  rewritten to le a (sub n 1) via subN_q (sym) *)
        val subN_q_s = oeq_sym_vW OF [subN_q]                (* q = sub n 1 *)
        val Ple = Term.lambda (Free("z_le", natT)) (le aF (Free("z_le", natT)))
        val le_a_subn = oeq_rw_W (Ple, q, sub nF oneC) subN_q_s le_a_q  (* le a (sub n 1) *)

        val cj = conjI_W (lt ZeroC aF, le aF (sub nF oneC)) lt0a le_a_subn
        val mem = lmem_upto_bwd_W (aF, sub nF oneC) cj       (* lmem a (upto (sub n 1)) *)
      in mem end
    val res = exE_W (Abs("q", natT, oeq nF (suc (Bound 0))), goalC) predEx "q_fr" predBody
    val d2 = Thm.implies_intr (ctermW hanP) res
    val d1 = Thm.implies_intr (ctermW h1aP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of factor_in_range) = 0 then out "OK factor_in_range\n" else out "FAIL factor_in_range\n";

(* combinator form *)
fun factor_in_range_W (at, nt) h1a han =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("n",0), ctermW nt)] factor_in_range)
  in Thm.implies_elim (Thm.implies_elim inst h1a) han end;

(* ============================================================================
   VALIDATION : aconv intended, 0-hyp, soundness probes.
   ============================================================================ *)
val xV = Var(("x",0),natT); val yV = Var(("y",0),natT); val LV = Var(("L",0),natlistT);
val aVf = Var(("a",0),natT); val nVf = Var(("n",0),natT);

val key_intended =
  Logic.mk_implies (jT (neg (oeq xV yV)),
    Logic.mk_implies (jT (lmem xV LV),
      Logic.mk_implies (jT (lmem yV LV),
        jT (dvd (mult xV yV) (lprod LV)))));
val r_key = (length (Thm.hyps_of key_div_pair) = 0)
            andalso ((Thm.prop_of key_div_pair) aconv key_intended);
val () = if r_key then out "OK key_div_pair aconv intended\n" else out "FAIL key_div_pair aconv\n";

val fir_intended =
  Logic.mk_implies (jT (lt oneC aVf),
    Logic.mk_implies (jT (lt aVf nVf),
      jT (lmem aVf (uptoF (sub nVf oneC)))));
val r_fir = (length (Thm.hyps_of factor_in_range) = 0)
            andalso ((Thm.prop_of factor_in_range) aconv fir_intended);
val () = if r_fir then out "OK factor_in_range aconv intended\n" else out "FAIL factor_in_range aconv\n";

(* probe: key_div_pair genuinely needs the x<>y premise *)
val probe_key_needs_neq =
  let val bogus = Logic.mk_implies (jT (lmem xV LV),
        Logic.mk_implies (jT (lmem yV LV), jT (dvd (mult xV yV)(lprod LV))))
  in not ((Thm.prop_of key_div_pair) aconv bogus) end;
val () = if probe_key_needs_neq then out "PROBE_OK key_div_pair keeps x<>y\n"
         else out "PROBE_FAIL key_div_pair\n";

(* probe: factor_in_range genuinely needs 1<a *)
val probe_fir_needs_1a =
  let val bogus = Logic.mk_implies (jT (lt aVf nVf), jT (lmem aVf (uptoF (sub nVf oneC))))
  in not ((Thm.prop_of factor_in_range) aconv bogus) end;
val () = if probe_fir_needs_1a then out "PROBE_OK factor_in_range keeps 1<a\n"
         else out "PROBE_FAIL factor_in_range\n";

val () =
  if r_key andalso r_fir andalso probe_key_needs_neq andalso probe_fir_needs_1a
  then out "BASE_OK\n"
  else out "BASE_FAILED\n";
(* ============================================================================
   WILSON'S CONVERSE (direct, elementary):
       composite n ==> lt 4 n ==> dvd n (factorial n)
   i.e. if n is composite and n>4 then n | (n-1)!.
   ----------------------------------------------------------------------------
   On the final Wilson context (thyW / ctxtW / ctermW), building on the
   foundation delta (factorial, composite, key_div_pair, factor_in_range).
   No new constant, no new axiom; pure kernel inference.  Marker WC_CONVERSE_OK.
   ============================================================================ *)
val () = out "WC_DIRECT_BEGIN\n";

val twoC  = suc (suc ZeroC);
val four  = suc (suc (suc (suc ZeroC)));
fun mult0l_W t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_0_vW);

(* ---- dvd_trans re-varified onto ctxtW ---- *)
val dvd_trans_vW = varify dvd_trans;
fun dvd_trans_W (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] dvd_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* ============================ ARITHMETIC HELPERS ============================ *)

(* lt_intro_W (m,n,w) : oeq n (add m (suc w)) ==> lt m n *)
fun lt_intro_W (mt, nt, wt) heq =
  let val ar = addSr_W (mt, wt)
      val al = addSuc_W (mt, wt)
      val al_s = oeq_sym_vW OF [al]
      val bridge = oeq_trans_vW OF [ar, al_s]
      val nwit = oeq_trans_vW OF [heq, bridge]
  in le_intro_W (suc mt, nt, wt) nwit end;

(* two_mult_W a : oeq (mult 2 a) (add a a) *)
fun two_mult_W aT =
  let val s1 = multSuc_W (suc ZeroC, aT)
      val s2 = multSuc_W (ZeroC, aT)
      val s3 = mult0l_W aT
      val s2b = oeq_trans_vW OF [s2, add_cong_r_W (aT, mult ZeroC aT, ZeroC) s3]
      val s2c = oeq_trans_vW OF [s2b, add0r_W aT]
      val s1b = oeq_trans_vW OF [s1, add_cong_r_W (aT, mult (suc ZeroC) aT, aT) s2c]
  in s1b end;

(* ---- one_lt_b : oeq n (mult a b) ==> lt 1 a ==> lt a n ==> lt 1 b ---- *)
val one_lt_b =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val nF = Free("n", natT)
    val hnEqP = jT (oeq nF (mult aF bF)) ; val hnEq = Thm.assume (ctermW hnEqP)
    val h1aP  = jT (lt oneC aF)          ; val h1a  = Thm.assume (ctermW h1aP)
    val hanP  = jT (lt aF nF)            ; val han  = Thm.assume (ctermW hanP)
    val goalC = lt oneC bF
    val djb = dzos_W bF
    val cZ =
      let val hbz = Thm.assume (ctermW (jT (oeq bF ZeroC)))
          val mab_a0 = mult_cong_r_W (aF, bF, ZeroC) hbz
          val a0 = mult0r_W aF
          val mab0 = oeq_trans_vW OF [mab_a0, a0]
          val nEq0 = oeq_trans_vW OF [hnEq, mab0]
          val ltAbs = Abs("p", natT, oeq nF (add (suc aF) (Bound 0)))
          fun ltbody p (hp:thm) =
            let val asp = addSuc_W (aF, p)
                val n_suc = oeq_trans_vW OF [hp, asp]
                val n_suc_s = oeq_sym_vW OF [n_suc]
                val suc_eq_0 = oeq_trans_vW OF [n_suc_s, nEq0]
                val fls = Suc_neq_Zero_W (add aF p) suc_eq_0
            in oFalse_elim_W goalC OF [fls] end
          val res = exE_W (ltAbs, goalC) han "p_z" ltbody
      in Thm.implies_intr (ctermW (jT (oeq bF ZeroC))) res end
    val cS =
      let val bsAbs = Abs("q", natT, oeq bF (suc (Bound 0)))
          val hbsP = jT (mkEx bsAbs) ; val hbs = Thm.assume (ctermW hbsP)
          fun qbody q (hq:thm) =
            let
              val djq = dzos_W q
              val qsAbs = Abs("q2", natT, oeq q (suc (Bound 0)))
              val sqZ =
                let val hqz = Thm.assume (ctermW (jT (oeq q ZeroC)))
                    val bq_s = Suc_cong_vW OF [hqz]
                    val b_s0 = oeq_trans_vW OF [hq, bq_s]
                    val mab_a1 = mult_cong_r_W (aF, bF, suc ZeroC) b_s0
                    val a1 = mult1r_W aF
                    val mab_a = oeq_trans_vW OF [mab_a1, a1]
                    val nEqa = oeq_trans_vW OF [hnEq, mab_a]
                    val Plt = Term.lambda (Free("z_aa", natT)) (lt aF (Free("z_aa", natT)))
                    val ltaa = oeq_rw_W (Plt, nF, aF) nEqa han
                    val fls = lt_irrefl_W aF ltaa
                in Thm.implies_intr (ctermW (jT (oeq q ZeroC))) (oFalse_elim_W goalC OF [fls]) end
              val sqS =
                let val hqsP = jT (mkEx qsAbs) ; val hqs = Thm.assume (ctermW hqsP)
                    fun q2body q2 (hq2:thm) =
                      let
                        val sq2 = Suc_cong_vW OF [hq2]
                        val b_ss = oeq_trans_vW OF [hq, sq2]
                        val a1 = addSuc_W (suc ZeroC, q2)
                        val a2 = addSuc_W (ZeroC, q2)
                        val a3 = add0_W q2
                        val inner = oeq_trans_vW OF [a2, Suc_cong_vW OF [a3]]
                        val addexp = oeq_trans_vW OF [a1, Suc_cong_vW OF [inner]]
                        val addexp_s = oeq_sym_vW OF [addexp]
                        val bwit = oeq_trans_vW OF [b_ss, addexp_s]
                        val res = le_intro_W (suc oneC, bF, q2) bwit
                      in res end
                    val r = exE_W (qsAbs, goalC) hqs "q2_s" q2body
                in Thm.implies_intr (ctermW hqsP) r end
            in disjE_W (oeq q ZeroC, mkEx qsAbs, goalC) djq sqZ sqS end
          val r = exE_W (bsAbs, goalC) hbs "q_s" qbody
      in Thm.implies_intr (ctermW hbsP) r end
    val res = disjE_W (oeq bF ZeroC, mkEx (Abs("q", natT, oeq bF (suc (Bound 0)))), goalC) djb cZ cS
    val d3 = Thm.implies_intr (ctermW hanP) res
    val d2 = Thm.implies_intr (ctermW h1aP) d3
    val d1 = Thm.implies_intr (ctermW hnEqP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of one_lt_b) = 0 then out "OK one_lt_b\n" else out "FAIL one_lt_b\n";
fun one_lt_b_W (at,bt,nt) hnEq h1a han =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("b",0), ctermW bt),(("n",0), ctermW nt)] one_lt_b)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hnEq) h1a) han end;

(* ---- b_lt_n : oeq n (mult a b) ==> lt 1 a ==> lt 1 b ==> lt b n ---- *)
val b_lt_n =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val nF = Free("n", natT)
    val hnEqP = jT (oeq nF (mult aF bF)) ; val hnEq = Thm.assume (ctermW hnEqP)
    val h1aP  = jT (lt oneC aF)          ; val h1a  = Thm.assume (ctermW h1aP)
    val h1bP  = jT (lt oneC bF)          ; val h1b  = Thm.assume (ctermW h1bP)
    val goalC = lt bF nF
    val twoCl = suc (suc ZeroC)
    val aleAbs = Abs("p", natT, oeq aF (add twoCl (Bound 0)))
    fun aBody ka (hka:thm) =
      let
        val aa = suc ka
        val e1 = addSuc_W (suc ZeroC, ka)
        val e2 = addSuc_W (ZeroC, ka)
        val e3 = add0_W ka
        val inner = oeq_trans_vW OF [e2, Suc_cong_vW OF [e3]]
        val a_exp = oeq_trans_vW OF [e1, Suc_cong_vW OF [inner]]
        val a_eq_sucaa = oeq_trans_vW OF [hka, a_exp]
        val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                       [(("p",0), ctermW bF)] pos_pred)) h1b
        val bsAbs = Abs("q", natT, oeq bF (suc (Bound 0)))
        fun bBody bp (hbp:thm) =
          let
            val Pm = Term.lambda (Free("z_ma", natT)) (oeq (mult aF bF) (mult (Free("z_ma", natT)) bF))
            val mab_msuc = oeq_rw_W (Pm, aF, suc aa) a_eq_sucaa (oeqRefl_W (mult aF bF))
            val msuc_exp = multSuc_W (aa, bF)
            val mab_addb = oeq_trans_vW OF [mab_msuc, msuc_exp]
            val n_addb = oeq_trans_vW OF [hnEq, mab_addb]
            val Y = mult aa bF
            val aa_exp = multSuc_W (ka, bF)
            val ZcoreR = mult ka bF
            val b_addExp =
              let val Pb = Term.lambda (Free("z_bb", natT)) (oeq (add bF ZcoreR) (add (Free("z_bb", natT)) ZcoreR))
                  val reb = oeq_rw_W (Pb, bF, suc bp) hbp (oeqRefl_W (add bF ZcoreR))
                  val asuc = addSuc_W (bp, ZcoreR)
              in oeq_trans_vW OF [reb, asuc] end
            val Zc = add bp ZcoreR
            val Y_sucZ = oeq_trans_vW OF [aa_exp, b_addExp]
            val Pn = Term.lambda (Free("z_nn", natT)) (oeq nF (add bF (Free("z_nn", natT))))
            val n_addbsuc = oeq_rw_W (Pn, Y, suc Zc) Y_sucZ n_addb
            val absuc = addSr_W (bF, Zc)
            val asb = addSuc_W (bF, Zc)
            val asb_s = oeq_sym_vW OF [asb]
            val n_addsucb = oeq_trans_vW OF [oeq_trans_vW OF [n_addbsuc, absuc], asb_s]
            val res = le_intro_W (suc bF, nF, Zc) n_addsucb
          in res end
        val r = exE_W (bsAbs, goalC) predEx "bp_h2" bBody
      in r end
    val res = exE_W (aleAbs, goalC) h1a "ka_h2" aBody
    val d3 = Thm.implies_intr (ctermW h1bP) res
    val d2 = Thm.implies_intr (ctermW h1aP) d3
    val d1 = Thm.implies_intr (ctermW hnEqP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of b_lt_n) = 0 then out "OK b_lt_n\n" else out "FAIL b_lt_n\n";
fun b_lt_n_W (at,bt,nt) hnEq h1a h1b =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("b",0), ctermW bt),(("n",0), ctermW nt)] b_lt_n)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hnEq) h1a) h1b end;

(* ---- mult_2_2 : oeq (mult 2 2) 4 ---- *)
val mult_2_2 =
  let
    val s1 = multSuc_W (suc ZeroC, twoC)
    val s2 = multSuc_W (ZeroC, twoC)
    val s3 = mult0l_W twoC
    val s2b = oeq_trans_vW OF [s2, add_cong_r_W (twoC, mult ZeroC twoC, ZeroC) s3]
    val s2c = oeq_trans_vW OF [s2b, add0r_W twoC]
    val s1b = oeq_trans_vW OF [s1, add_cong_r_W (twoC, mult (suc ZeroC) twoC, twoC) s2c]
    val a1 = addSuc_W (suc ZeroC, twoC)
    val a2 = addSuc_W (ZeroC, twoC)
    val a3 = add0_W twoC
    val a2b = oeq_trans_vW OF [a2, Suc_cong_vW OF [a3]]
    val a1b = oeq_trans_vW OF [a1, Suc_cong_vW OF [a2b]]
    val res = oeq_trans_vW OF [s1b, a1b]
  in varify res end;

(* ---- two_lt_a : oeq n (mult a a) ==> lt 1 a ==> lt 4 n ==> lt 2 a ---- *)
val two_lt_a =
  let
    val aF = Free("a", natT); val nF = Free("n", natT)
    val hnEqP = jT (oeq nF (mult aF aF)) ; val hnEq = Thm.assume (ctermW hnEqP)
    val h1aP  = jT (lt oneC aF)          ; val h1a  = Thm.assume (ctermW h1aP)
    val h4P   = jT (lt four nF)          ; val h4   = Thm.assume (ctermW h4P)
    val goalC = lt twoC aF
    val em = em_W (lt twoC aF)
    val cPos = let val h = Thm.assume (ctermW (jT (lt twoC aF)))
               in Thm.implies_intr (ctermW (jT (lt twoC aF))) h end
    val cNeg = let val hneg = Thm.assume (ctermW (jT (neg (lt twoC aF))))
                   val le_a_2 = nlt_le_W (twoC, aF) hneg
                   val le_2_a = h1a
                   val a_eq_2 = le_antisym_W (aF, twoC) le_a_2 le_2_a
                   val Pm = Term.lambda (Free("z_m1", natT)) (oeq nF (mult (Free("z_m1", natT)) (Free("z_m1", natT))))
                   val n_22 = oeq_rw_W (Pm, aF, twoC) a_eq_2 hnEq
                   val n_4 = oeq_trans_vW OF [n_22, mult_2_2]
                   val Plt = Term.lambda (Free("z_l1", natT)) (lt four (Free("z_l1", natT)))
                   val lt44 = oeq_rw_W (Plt, nF, four) n_4 h4
                   val fls = lt_irrefl_W four lt44
               in Thm.implies_intr (ctermW (jT (neg (lt twoC aF)))) (oFalse_elim_W goalC OF [fls]) end
    val res = disjE_W (lt twoC aF, neg (lt twoC aF), goalC) em cPos cNeg
    val d3 = Thm.implies_intr (ctermW h4P) res
    val d2 = Thm.implies_intr (ctermW h1aP) d3
    val d1 = Thm.implies_intr (ctermW hnEqP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of two_lt_a) = 0 then out "OK two_lt_a\n" else out "FAIL two_lt_a\n";
fun two_lt_a_W (at,nt) hnEq h1a h4 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("n",0), ctermW nt)] two_lt_a)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hnEq) h1a) h4 end;

(* ---- two_a_lt_n : oeq n (mult a a) ==> lt 2 a ==> lt (mult 2 a) n ---- *)
val two_a_lt_n =
  let
    val aF = Free("a", natT); val nF = Free("n", natT)
    val three = suc (suc (suc ZeroC))
    val hnEqP = jT (oeq nF (mult aF aF)) ; val hnEq = Thm.assume (ctermW hnEqP)
    val h2aP  = jT (lt twoC aF)          ; val h2a  = Thm.assume (ctermW h2aP)
    val goalC = lt (mult twoC aF) nF
    val aleAbs = Abs("p", natT, oeq aF (add three (Bound 0)))
    fun aBody ka (hka:thm) =
      let
        val e1 = addSuc_W (suc (suc ZeroC), ka)
        val e2 = addSuc_W (suc ZeroC, ka)
        val e3 = addSuc_W (ZeroC, ka)
        val e4 = add0_W ka
        val i3 = oeq_trans_vW OF [e3, Suc_cong_vW OF [e4]]
        val i2 = oeq_trans_vW OF [e2, Suc_cong_vW OF [i3]]
        val i1 = oeq_trans_vW OF [e1, Suc_cong_vW OF [i2]]
        val a_eq = oeq_trans_vW OF [hka, i1]
        val ap = suc (suc (suc ka))
        val Pm1 = Term.lambda (Free("z_q1", natT)) (oeq (mult aF aF) (mult (Free("z_q1", natT)) aF))
        val maa_ap = oeq_rw_W (Pm1, aF, ap) a_eq (oeqRefl_W (mult aF aF))
        val m1 = multSuc_W (suc (suc ka), aF)
        val m2 = multSuc_W (suc ka, aF)
        val m3 = multSuc_W (ka, aF)
        val step3 = m3
        val step2 = oeq_trans_vW OF [m2, add_cong_r_W (aF, mult (suc ka) aF, add aF (mult ka aF)) step3]
        val step1 = oeq_trans_vW OF [m1, add_cong_r_W (aF, mult (suc (suc ka)) aF, add aF (add aF (mult ka aF))) step2]
        val maa_full = oeq_trans_vW OF [maa_ap, step1]
        val n_full = oeq_trans_vW OF [hnEq, maa_full]
        val X = add aF (mult ka aF)
        val assoc0 = addassoc_W (aF, aF, X)
        val assoc = oeq_sym_vW OF [assoc0]
        val n_assoc = oeq_trans_vW OF [n_full, assoc]
        val X_rw =
          let val Px = Term.lambda (Free("z_x1", natT)) (oeq (add aF (mult ka aF)) (add (Free("z_x1", natT)) (mult ka aF)))
              val rX = oeq_rw_W (Px, aF, ap) a_eq (oeqRefl_W (add aF (mult ka aF)))
              val asuc = addSuc_W (suc (suc ka), mult ka aF)
          in oeq_trans_vW OF [rX, asuc] end
        val W = add (suc (suc ka)) (mult ka aF)
        val Pn = Term.lambda (Free("z_n1", natT)) (oeq nF (add (add aF aF) (Free("z_n1", natT))))
        val n_suc = oeq_rw_W (Pn, X, suc W) X_rw n_assoc
        val lt_aa = lt_intro_W (add aF aF, nF, W) n_suc
        val tm = two_mult_W aF
        val tm_s = oeq_sym_vW OF [tm]
        val Plt = Term.lambda (Free("z_lt2", natT)) (lt (Free("z_lt2", natT)) nF)
        val res = oeq_rw_W (Plt, add aF aF, mult twoC aF) tm_s lt_aa
      in res end
    val res = exE_W (aleAbs, goalC) h2a "ka_h4" aBody
    val d2 = Thm.implies_intr (ctermW h2aP) res
    val d1 = Thm.implies_intr (ctermW hnEqP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of two_a_lt_n) = 0 then out "OK two_a_lt_n\n" else out "FAIL two_a_lt_n\n";
fun two_a_lt_n_W (at,nt) hnEq h2a =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("n",0), ctermW nt)] two_a_lt_n)
  in Thm.implies_elim (Thm.implies_elim inst hnEq) h2a end;

(* ---- a_lt_two_a : lt 1 a ==> lt a (mult 2 a) ---- *)
val a_lt_two_a =
  let
    val aF = Free("a", natT)
    val h1aP = jT (lt oneC aF) ; val h1a = Thm.assume (ctermW h1aP)
    val goalC = lt aF (mult twoC aF)
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                   [(("p",0), ctermW aF)] pos_pred)) h1a
    val asAbs = Abs("q", natT, oeq aF (suc (Bound 0)))
    fun aBody ap (hap:thm) =
      let
        val tm = two_mult_W aF
        val Pa = Term.lambda (Free("z_t2", natT)) (oeq (add aF aF) (add aF (Free("z_t2", natT))))
        val aa_rw = oeq_rw_W (Pa, aF, suc ap) hap (oeqRefl_W (add aF aF))
        val m2a_form = oeq_trans_vW OF [tm, aa_rw]
        val res = lt_intro_W (aF, mult twoC aF, ap) m2a_form
      in res end
    val res = exE_W (asAbs, goalC) predEx "ap_h5" aBody
  in varify (Thm.implies_intr (ctermW h1aP) res) end;
val () = if length (Thm.hyps_of a_lt_two_a) = 0 then out "OK a_lt_two_a\n" else out "FAIL a_lt_two_a\n";
fun a_lt_two_a_W at h1a =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("a",0), ctermW at)] a_lt_two_a)) h1a;

(* ---- a_neq_two_a : lt 1 a ==> neg (oeq a (mult 2 a)) ---- *)
val a_neq_two_a =
  let
    val aF = Free("a", natT)
    val h1aP = jT (lt oneC aF) ; val h1a = Thm.assume (ctermW h1aP)
    val la2a = a_lt_two_a_W aF h1a
    val heq = Thm.assume (ctermW (jT (oeq aF (mult twoC aF))))
    val Plt = Term.lambda (Free("z_na", natT)) (lt aF (Free("z_na", natT)))
    val heq_s = oeq_sym_vW OF [heq]
    val ltaa = oeq_rw_W (Plt, mult twoC aF, aF) heq_s la2a
    val fls = lt_irrefl_W aF ltaa
    val metaImp = Thm.implies_intr (ctermW (jT (oeq aF (mult twoC aF)))) fls
    val negThm = impI_W (oeq aF (mult twoC aF), oFalseC) metaImp
  in varify (Thm.implies_intr (ctermW h1aP) negThm) end;
val () = if length (Thm.hyps_of a_neq_two_a) = 0 then out "OK a_neq_two_a\n" else out "FAIL a_neq_two_a\n";
fun a_neq_two_a_W at h1a =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("a",0), ctermW at)] a_neq_two_a)) h1a;

(* ---- mult_a_two_a : oeq n (mult a a) ==> oeq (mult a (mult 2 a)) (mult 2 n) ---- *)
val mult_a_two_a =
  let
    val aF = Free("a", natT); val nF = Free("n", natT)
    val hnEqP = jT (oeq nF (mult aF aF)) ; val hnEq = Thm.assume (ctermW hnEqP)
    val c1 = multcomm_W (aF, mult twoC aF)
    val c2 = multassoc_W (twoC, aF, aF)
    val c3 = mult_cong_r_W (twoC, mult aF aF, nF) (oeq_sym_vW OF [hnEq])
    val res = oeq_trans_vW OF [oeq_trans_vW OF [c1, c2], c3]
  in varify (Thm.implies_intr (ctermW hnEqP) res) end;
val () = if length (Thm.hyps_of mult_a_two_a) = 0 then out "OK mult_a_two_a\n" else out "FAIL mult_a_two_a\n";
fun mult_a_two_a_W (at,nt) hnEq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("n",0), ctermW nt)] mult_a_two_a)) hnEq;

(* ---- n_dvd_two_n_W n : dvd n (mult 2 n) ---- *)
fun n_dvd_two_n_W nT =
  let val comm = multcomm_W (twoC, nT)
  in dvd_intro_W (nT, mult twoC nT, twoC) comm end;

val () = out "WC_HELPERS_ALL_READY\n";

(* ============================ THE CONVERSE THEOREM ============================ *)
val wc_converse =
  let
    val nF = Free("n", natT)
    val hcompP = jT (composite nF) ; val hcomp = Thm.assume (ctermW hcompP)
    val h4P = jT (lt four nF) ; val h4 = Thm.assume (ctermW h4P)
    val goalC = dvd nF (factorial nF)
    val Lt = uptoF (sub nF oneC)   (* lprod Lt = factorial n *)
    (* compAbs matches composite's existential body *)
    val compAbs = Term.lambda (Free("a_co", natT))
      (mkConj (lt oneC (Free("a_co", natT)))
        (mkConj (lt (Free("a_co", natT)) nF) (dvd (Free("a_co", natT)) nF)))
    fun aBody a (hbody:thm) =
      let
        val h1a  = conjunct1_W (lt oneC a, mkConj (lt a nF)(dvd a nF)) hbody
        val rest = conjunct2_W (lt oneC a, mkConj (lt a nF)(dvd a nF)) hbody
        val han  = conjunct1_W (lt a nF, dvd a nF) rest
        val hdvd = conjunct2_W (lt a nF, dvd a nF) rest      (* dvd a n = ?k. oeq n (mult a k) *)
        val dvdAbs = Abs("k", natT, oeq nF (mult a (Bound 0)))
        fun bBody b (hb:thm) =   (* hb : oeq n (mult a b) *)
          let
            val h1b = one_lt_b_W (a, b, nF) hb h1a han       (* lt 1 b *)
            val hbn = b_lt_n_W (a, b, nF) hb h1a h1b         (* lt b n *)
            val emab = em_W (oeq a b)                         (* Disj (oeq a b) (neg (oeq a b)) *)
            (* ---- CASE a = b (square) ---- *)
            val cEq =
              let val heqab = Thm.assume (ctermW (jT (oeq a b)))
                  (* hb : oeq n (mult a b) -> rewrite b->a : oeq n (mult a a) *)
                  val hba = oeq_sym_vW OF [heqab]             (* oeq b a *)
                  val Pmaa = Term.lambda (Free("z_sq", natT)) (oeq nF (mult a (Free("z_sq", natT))))
                  val hnaa = oeq_rw_W (Pmaa, b, a) hba hb     (* oeq n (mult a a) *)
                  val h2a = two_lt_a_W (a, nF) hnaa h1a h4    (* lt 2 a *)
                  val h2aLtN = two_a_lt_n_W (a, nF) hnaa h2a  (* lt (mult 2 a) n *)
                  val one_lt_2a = lt_trans_W (oneC, a, mult twoC a) h1a (a_lt_two_a_W a h1a)  (* lt 1 (mult 2 a) *)
                  val mem_a  = factor_in_range_W (a, nF) h1a han        (* lmem a Lt *)
                  val mem_2a = factor_in_range_W (mult twoC a, nF) one_lt_2a h2aLtN  (* lmem 2a Lt *)
                  val hneq_a2a = a_neq_two_a_W a h1a          (* neg (oeq a (mult 2 a)) *)
                  val dvd_pair = key_div_pair_W (a, mult twoC a, Lt) hneq_a2a mem_a mem_2a
                                 (* dvd (mult a (mult 2 a)) (lprod Lt) = dvd (..) (factorial n) *)
                  (* rewrite mult a (mult 2 a) -> mult 2 n *)
                  val mform = mult_a_two_a_W (a, nF) hnaa     (* mult a (mult 2 a) = mult 2 n *)
                  val Pd = Term.lambda (Free("z_d1", natT)) (dvd (Free("z_d1", natT)) (factorial nF))
                  val dvd_2n_L = oeq_rw_W (Pd, mult a (mult twoC a), mult twoC nF) mform dvd_pair
                                 (* dvd (mult 2 n) (factorial n) *)
                  val n_dvd_2n = n_dvd_two_n_W nF             (* dvd n (mult 2 n) *)
                  val res = dvd_trans_W (nF, mult twoC nF, factorial nF) n_dvd_2n dvd_2n_L
              in Thm.implies_intr (ctermW (jT (oeq a b))) res end
            (* ---- CASE a <> b ---- *)
            val cNeq =
              let val hneqab = Thm.assume (ctermW (jT (neg (oeq a b))))
                  val mem_a = factor_in_range_W (a, nF) h1a han    (* lmem a Lt *)
                  val mem_b = factor_in_range_W (b, nF) h1b hbn    (* lmem b Lt *)
                  val dvd_ab_L = key_div_pair_W (a, b, Lt) hneqab mem_a mem_b
                                 (* dvd (mult a b) (lprod Lt) = dvd (mult a b) (factorial n) *)
                  (* rewrite mult a b -> n via hb (sym) *)
                  val hba_n = oeq_sym_vW OF [hb]               (* mult a b = n *)
                  val Pd = Term.lambda (Free("z_d2", natT)) (dvd (Free("z_d2", natT)) (factorial nF))
                  val res = oeq_rw_W (Pd, mult a b, nF) hba_n dvd_ab_L   (* dvd n (factorial n) *)
              in Thm.implies_intr (ctermW (jT (neg (oeq a b)))) res end
            val res = disjE_W (oeq a b, neg (oeq a b), goalC) emab cEq cNeq
          in res end
        val r = exE_W (dvdAbs, goalC) hdvd "b_co" bBody
      in r end
    val res = exE_W (compAbs, goalC) hcomp "a_co2" aBody
    val d2 = Thm.implies_intr (ctermW h4P) res
    val d1 = Thm.implies_intr (ctermW hcompP) d2
  in varify d1 end;

val () = if length (Thm.hyps_of wc_converse) = 0 then out "WC_CONV_0HYP\n" else out "WC_CONV_HASHYP\n";

(* aconv check against the intended statement *)
val nVc = Var(("n",0), natT);
val wc_intended =
  Logic.mk_implies (jT (composite nVc),
    Logic.mk_implies (jT (lt four nVc), jT (dvd nVc (factorial nVc))));
val r_wc = (length (Thm.hyps_of wc_converse) = 0)
           andalso ((Thm.prop_of wc_converse) aconv wc_intended);
val () = if r_wc then out "WC_CONV_ACONV_OK\n" else out "WC_CONV_ACONV_FAIL\n";

(* soundness probe: must keep BOTH premises (composite + lt 4) *)
val probe_drop_comp =
  let val bogus = Logic.mk_implies (jT (lt four nVc), jT (dvd nVc (factorial nVc)))
  in not ((Thm.prop_of wc_converse) aconv bogus) end;
val probe_drop_4 =
  let val bogus = Logic.mk_implies (jT (composite nVc), jT (dvd nVc (factorial nVc)))
  in not ((Thm.prop_of wc_converse) aconv bogus) end;
val () = if probe_drop_comp then out "PROBE_OK keeps composite premise\n" else out "PROBE_FAIL drop composite\n";
val () = if probe_drop_4    then out "PROBE_OK keeps lt 4 premise\n"    else out "PROBE_FAIL drop lt4\n";

val () = if r_wc andalso probe_drop_comp andalso probe_drop_4
         then out "WC_CONVERSE_OK\n" else out "WC_CONVERSE_FAILED\n";
val () = out "WC_ALL_OK\n";

(* ============================================================================
   WILSON'S IFF — the full primality criterion.

     wilson_iff : 1 < n ==> (prime2 n  <->  cong n ((n-1)!) (n-1))

   (n-1)! is `factorial n = lprod (upto (sub n 1))`; -1 (mod n) is the residue
   n-1 = sub n 1.  The biconditional <-> is encoded as the object Conj of the
   two implications:  Conj (Imp (prime2 n) C) (Imp C (prime2 n)),
   with C = cong n ((n-1)!) (n-1).

   FORWARD  (prime2 n => C): instantiate Wilson's theorem at n.
   BACKWARD (C => prime2 n): contrapositive.  From 1<n, prime_cases gives
     prime2 n (done) OR a proper divisor (composite n); composite n splits on
     em (lt 4 n) into
       (a) 4<n : wc_converse => n | (n-1)!, so (n-1)! == 0 != n-1 (0<n-1<n);
       (b) ~(4<n) : composite + 1<n forces n=4, and 3! = 6 == 2 != 3.
   ============================================================================ *)
val () = out "WIFF_DELTA_BEGIN\n";

(* ---- small literal builders + numeral arithmetic evaluators on ctxtW ---- *)
fun lit 0 = ZeroC | lit k = suc (lit (k-1));
val oneW = lit 1; val twoW = lit 2; val threeW = lit 3; val fourW = lit 4;

(* addEval a b : |- oeq (add (lit a)(lit b)) (lit (a+b)) *)
fun addEval 0 b = add0_W (lit b)
  | addEval a b =
      let val inner = addEval (a-1) b                       (* (a-1)+b = lit(a-1+b) *)
          val step  = addSuc_W (lit (a-1), lit b)           (* (suc(a-1))+b = suc((a-1)+b) *)
          val sc    = Suc_cong_vW OF [inner]                (* suc((a-1)+b) = suc(lit(a-1+b)) = lit(a+b) *)
      in oeq_trans_vW OF [step, sc] end;

(* multEval a b : |- oeq (mult (lit a)(lit b)) (lit (a*b)) *)
fun multEval 0 b = mult0l_W (lit b)
  | multEval a b =
      let val step  = multSuc_W (lit (a-1), lit b)          (* (suc(a-1))*b = b + (a-1)*b *)
          val inner = multEval (a-1) b                      (* (a-1)*b = lit((a-1)*b) *)
          val Pm    = Term.lambda (Free("z_me", natT)) (oeq (mult (lit a) (lit b)) (add (lit b) (Free("z_me", natT))))
          val step2 = oeq_rw_W (Pm, mult (lit (a-1)) (lit b), lit ((a-1)*b)) inner step  (* a*b = b + lit((a-1)*b) *)
          val ae    = addEval b ((a-1)*b)                   (* b + (a-1)*b = lit(a*b) *)
      in oeq_trans_vW OF [step2, ae] end;

(* subEval a b (a>=b) : |- oeq (sub (lit a)(lit b)) (lit (a-b)) *)
fun subEval a 0 = sub0_W (lit a)
  | subEval a b =
      let val step  = subSS_W (lit (a-1), lit (b-1))        (* sub (suc(a-1))(suc(b-1)) = sub (a-1)(b-1) *)
      in oeq_trans_vW OF [step, subEval (a-1) (b-1)] end;

(* ---- shared term abbreviations ---- *)
val factW  = factorial;                          (* factorial n = lprod (upto (sub n 1)) *)
fun pm1W n = sub n oneW;                          (* the residue -1 == n-1 *)
fun congFn n = cong n (factW n) (pm1W n);         (* cong n ((n-1)!) (n-1) *)

(* ---- varify prime_cases (0-hyp schematic thm built on ctxtC) onto ctxtW ---- *)
val prime_cases_vW = varify prime_cases;
fun prime_cases_W nt hlt1 =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] prime_cases_vW)) hlt1;
fun pc_pdAbs n = Term.lambda (Free("d_pd", natT))   (* prime_cases body: ((1<d/\d<n)/\d|n) *)
      (mkConj (mkConj (lt oneW (Free("d_pd", natT))) (lt (Free("d_pd", natT)) n))
              (dvd (Free("d_pd", natT)) n));
fun comp_aAbs n = Term.lambda (Free("a_co", natT))  (* composite body: (1<a/\(a<n/\a|n)) *)
      (mkConj (lt oneW (Free("a_co", natT)))
         (mkConj (lt (Free("a_co", natT)) n) (dvd (Free("a_co", natT)) n)));

(* ---- lt 1 n -> lt (sub n 1) n  (pos_pred + sub_lt_self) ---- *)
fun pm1_lt_W nt hlt1 =
  let
    val predEx = Thm.implies_elim
        (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW nt)] pos_pred)) hlt1
    val Pq = Abs("q", natT, oeq nt (suc (Bound 0)))
    fun body q (hq:thm) =
      Thm.implies_elim
        (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW nt),(("q",0), ctermW q)] sub_lt_self)) hq
  in exE_W (Pq, lt (pm1W nt) nt) predEx "q_pl" body end;

(* concrete lt a b (a<b) via le (suc a) b with witness w = b-(a+1) *)
fun ltLit a b =
  let val w = b - a - 1
      val ev = addEval (a+1) w                 (* oeq (lit(a+1)+lit w) (lit b) *)
      val ev_s = oeq_sym_vW OF [ev]            (* oeq (lit b) (lit(a+1) + lit w) *)
  in le_intro_W (lit (a+1), lit b, lit w) ev_s end;  (* le (suc a) b = lt a b *)

(* left_distrib varified onto ctxtW : mult c (add m n) = add (mult c m)(mult c n) *)
val left_distrib_vW = varify left_distrib;
fun left_distrib_W (cT, mT, nT) =
  beta_norm (Drule.infer_instantiate ctxtW
     [(("k",0), ctermW cT),(("m",0), ctermW mT),(("n",0), ctermW nT)] left_distrib_vW);

(* mult_le_mono_W (c,j,k) : le j k -> le (mult c j)(mult c k) *)
fun mult_le_mono_W (cT, jT', kT) hle =
  let
    val Le = Abs("p", natT, oeq kT (add jT' (Bound 0)))
    fun body p (hp:thm) =          (* hp : oeq k (add j p) *)
      let
        val Pm  = Term.lambda (Free("z_lm", natT)) (oeq (mult cT kT) (mult cT (Free("z_lm", natT))))
        val ck  = oeq_rw_W (Pm, kT, add jT' p) hp (oeqRefl_W (mult cT kT))  (* mult c k = mult c (j+p) *)
        val ld  = left_distrib_W (cT, jT', p)        (* mult c (j+p) = mult c j + mult c p *)
        val ck2 = oeq_trans_vW OF [ck, ld]           (* mult c k = mult c j + mult c p *)
      in le_intro_W (mult cT jT', mult cT kT, mult cT p) ck2 end
  in exE_W (Le, le (mult cT jT') (mult cT kT)) hle "p_lm" body end;

val () = out "WIFF_HELPERS_OK\n";

(* ============================================================================
   STEP 1: dvd n F  ==>  cong n F 0
   ============================================================================ *)
fun dvd_imp_cong_zero_W (nt, Ft) hdvd =
  let
    val dvdAbs = Abs("k", natT, oeq Ft (mult nt (Bound 0)))
    fun body k (hk:thm) =          (* hk : oeq F (mult n k) *)
      let val z0  = add0_W (mult nt k)              (* 0 + n*k = n*k *)
          val hk' = oeq_trans_vW OF [hk, oeq_sym_vW OF [z0]]  (* F = 0 + n*k *)
      in cong_introR_W (nt, Ft, ZeroC, k) hk' end
  in exE_W (dvdAbs, cong nt Ft ZeroC) hdvd "k_dz" body end;

val () = out "WIFF_STEP1_OK\n";

(* ============================================================================
   STEP 2: lt 1 n -> cong n F 0 -> ~ cong n F (n-1)
   ============================================================================ *)
fun not_cong_of_cong0_W (nt, Ft) hp1 hcong0 =
  let
    val pm1     = pm1W nt
    val hp0     = lt1_imp_lt0_W nt hp1                 (* lt 0 n *)
    val hpm1pos = sub_p1_pos_W nt hp1                  (* lt 0 (n-1) *)
    val hpm1lt  = pm1_lt_W nt hp1                      (* lt (n-1) n *)
    val hassP   = jT (cong nt Ft pm1)
    val hass    = Thm.assume (ctermW hassP)
    val cong0F  = cong_sym_W (nt, Ft, ZeroC) hcong0
    val cong0pm1= cong_trans_W (nt, ZeroC, Ft, pm1) cong0F hass
    val eq0pm1  = cong_range_unique_W (nt, ZeroC, pm1) hp1 hp0 hpm1lt cong0pm1  (* oeq 0 (n-1) *)
    val Plt     = Term.lambda (Free("z_nc", natT)) (lt ZeroC (Free("z_nc", natT)))
    val lt00    = oeq_rw_W (Plt, pm1, ZeroC) (oeq_sym_vW OF [eq0pm1]) hpm1pos   (* lt 0 0 *)
    val fls     = lt_irrefl_W ZeroC lt00
  in impI_W (cong nt Ft pm1, oFalseC) (Thm.implies_intr (ctermW hassP) fls) end;

val () = out "WIFF_STEP2_OK\n";

(* ============================================================================
   STEP 3 (n=4 case): factorial 4 = 6, and ~ cong 4 (factorial 4) (sub 4 1).
   ============================================================================ *)
(* upto 3 = lcons 3 (lcons 2 (lcons 1 lnil))  (leq chain) *)
val upto3_leq =
  let
    val u0 = uptoZero_W                                (* leq (upto 0) lnil *)
    val u1 = uptoSuc_W ZeroC ; val u2 = uptoSuc_W oneW ; val u3 = uptoSuc_W twoW
    val P1 = Term.lambda (Free("z_u1", natlistT)) (leq (uptoF oneW) (lcons oneW (Free("z_u1", natlistT))))
    val u1' = leq_rw_W (P1, uptoF ZeroC, lnilC) u0 u1
    val P2 = Term.lambda (Free("z_u2", natlistT)) (leq (uptoF twoW) (lcons twoW (Free("z_u2", natlistT))))
    val u2' = leq_rw_W (P2, uptoF oneW, lcons oneW lnilC) u1' u2
    val P3 = Term.lambda (Free("z_u3", natlistT)) (leq (uptoF threeW) (lcons threeW (Free("z_u3", natlistT))))
  in leq_rw_W (P3, uptoF twoW, lcons twoW (lcons oneW lnilC)) u2' u3 end;

(* lprod (upto 3) = 6 *)
val fact_list_eq_six =
  let
    val l1 = lcons oneW lnilC ; val l2 = lcons twoW l1 ; val l3 = lcons threeW l2
    val cnil = lprod_nil_vW2                           (* lprod lnil = 1 *)
    val c1 = lprodCons_W (oneW, lnilC)                 (* lprod l1 = 1 * lprod lnil *)
    val lp1 = oeq_trans_vW OF [ oeq_trans_vW OF [c1, mult_cong_r_W (oneW, lprod lnilC, oneW) cnil], multEval 1 1 ]  (* lprod l1 = 1 *)
    val c2 = lprodCons_W (twoW, l1)
    val lp2 = oeq_trans_vW OF [ oeq_trans_vW OF [c2, mult_cong_r_W (twoW, lprod l1, oneW) lp1], multEval 2 1 ]      (* lprod l2 = 2 *)
    val c3 = lprodCons_W (threeW, l2)
    val lp3 = oeq_trans_vW OF [ oeq_trans_vW OF [c3, mult_cong_r_W (threeW, lprod l2, twoW) lp2], multEval 3 2 ]    (* lprod l3 = 6 *)
    val lpf = lprod_cong_W (uptoF threeW, l3) upto3_leq   (* lprod (upto 3) = lprod l3 *)
  in oeq_trans_vW OF [lpf, lp3] end;

(* factorial 4 = lprod (upto (sub 4 1)) = lprod (upto 3) = 6 *)
val fact4_eq_six =
  let
    val Pf = Term.lambda (Free("z_f4", natT)) (oeq (factW fourW) (lprod (uptoF (Free("z_f4", natT)))))
    val refl = oeqRefl_W (factW fourW)                          (* factW 4 = lprod (upto (sub 4 1)) (defeq) *)
    val f_to_3 = oeq_rw_W (Pf, sub fourW oneW, threeW) (subEval 4 1) refl  (* factW 4 = lprod (upto 3) *)
  in oeq_trans_vW OF [f_to_3, fact_list_eq_six] end;            (* factW 4 = 6 *)

val () = out "WIFF_FACT4_EQ_6_OK\n";

(* cong 4 6 2 : 6 = 2 + 4*1 (witness k=1) *)
val cong4_six_two =
  let
    val m41 = multEval 4 1                              (* 4*1 = 4 *)
    val a24 = addEval 2 4                               (* 2 + 4 = 6 *)
    (* 2 + (4*1) = 2 + 4 = 6 *)
    val Pa = Term.lambda (Free("z_aw", natT)) (oeq (add twoW (Free("z_aw", natT))) (lit 6))
    val sum = oeq_rw_W (Pa, fourW, mult fourW oneW) (oeq_sym_vW OF [m41]) a24  (* 2 + 4*1 = 6 *)
  in cong_introR_W (fourW, lit 6, twoW, oneW) (oeq_sym_vW OF [sum]) end;  (* cong 4 6 2 *)

(* cong 4 (factorial 4) 2 *)
val cong4_fact_two =
  let val Pc = Term.lambda (Free("z_cf", natT)) (cong fourW (Free("z_cf", natT)) twoW)
  in oeq_rw_W (Pc, lit 6, factW fourW) (oeq_sym_vW OF [fact4_eq_six]) cong4_six_two end;

(* ~ cong 4 (factorial 4) (sub 4 1)  (sub 4 1 = 3) *)
val not_cong4 =
  let
    (* first build ~ cong 4 (factW 4) 3, then rewrite 3 -> sub 4 1 *)
    val lt14 = ltLit 1 4 ; val lt24 = ltLit 2 4 ; val lt34 = ltLit 3 4
    val hassP = jT (cong fourW (factW fourW) threeW)
    val hass  = Thm.assume (ctermW hassP)
    val cong2f = cong_sym_W (fourW, factW fourW, twoW) cong4_fact_two   (* cong 4 2 (factW 4) *)
    val cong23 = cong_trans_W (fourW, twoW, factW fourW, threeW) cong2f hass  (* cong 4 2 3 *)
    val eq23  = cong_range_unique_W (fourW, twoW, threeW) lt14 lt24 lt34 cong23  (* oeq 2 3 *)
    (* oeq 2 3 = oeq (suc 1)(suc 2) ; Suc_inj -> oeq 1 2 -> oeq 0 1 ; sym -> oeq (suc 0) 0 ; Suc_neq_Zero *)
    val eq12  = Suc_inj_W (oneW, twoW) eq23            (* oeq 1 2 *)
    val eq01  = Suc_inj_W (ZeroC, oneW) eq12           (* oeq 0 1 = oeq 0 (suc 0) *)
    val eq10  = oeq_sym_vW OF [eq01]                   (* oeq (suc 0) 0 *)
    val fls   = Suc_neq_Zero_W ZeroC eq10
    val not3  = impI_W (cong fourW (factW fourW) threeW, oFalseC)
                  (Thm.implies_intr (ctermW hassP) fls)  (* neg (cong 4 (factW 4) 3) *)
    (* rewrite 3 -> sub 4 1 inside neg (= Imp (cong .. 3) oFalse) *)
    val Pn = Term.lambda (Free("z_n3", natT)) (neg (cong fourW (factW fourW) (Free("z_n3", natT))))
    val three_eq_sub = oeq_sym_vW OF [subEval 4 1]      (* oeq 3 (sub 4 1) *)
  in oeq_rw_W (Pn, threeW, sub fourW oneW) three_eq_sub not3 end;  (* neg (cong 4 (factW 4) (sub 4 1)) *)

val () = out "WIFF_STEP3_OK\n";

(* ============================================================================
   BACKWARD : composite n -> 1<n -> ~ cong n (factW n) (n-1)
   ============================================================================ *)
fun not_cong_of_composite_W (nt, hcomp, hp1) =
  let
    (* em (lt 4 n) *)
    val em4 = em_W (lt fourW nt)
    val goalC = neg (congFn nt)
    (* case 4 < n : wc_converse gives dvd n (factW n) *)
    val caseGt =
      let
        val h4P = jT (lt fourW nt) ; val h4 = Thm.assume (ctermW h4P)
        (* wc_converse : composite n -> lt 4 n -> dvd n (factW n) *)
        val wc_inst = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] (varify wc_converse))
        val hdvd = Thm.implies_elim (Thm.implies_elim wc_inst hcomp) h4   (* dvd n (factW n) *)
        val cong0 = dvd_imp_cong_zero_W (nt, factW nt) hdvd               (* cong n (factW n) 0 *)
        val res = not_cong_of_cong0_W (nt, factW nt) hp1 cong0            (* neg (cong n (factW n)(n-1)) *)
      in Thm.implies_intr (ctermW h4P) res end
    (* case ~(4 < n) : composite + 1<n forces n = 4, then use not_cong4 *)
    val caseLe =
      let
        val hnle4P = jT (neg (lt fourW nt)) ; val hnle4 = Thm.assume (ctermW hnle4P)
        (* nlt_le : neg (lt d c) ==> le c d ; want le n 4 from neg (lt 4 n) => (d,c)=(4,n) *)
        val le_n4  = nlt_le_W (fourW, nt) hnle4                (* le n 4 *)
        val resInner =
          exE_W (comp_aAbs nt, neg (congFn nt)) hcomp "a_c4"
            (fn a => fn hbody =>
               let
                 val h1a  = conjunct1_W (lt oneW a, mkConj (lt a nt)(dvd a nt)) hbody  (* 1<a = le 2 a *)
                 val rest = conjunct2_W (lt oneW a, mkConj (lt a nt)(dvd a nt)) hbody
                 val han  = conjunct1_W (lt a nt, dvd a nt) rest                       (* a<n *)
                 val hdvd = conjunct2_W (lt a nt, dvd a nt) rest                       (* dvd a n = ?k. n = a*k *)
                 (* extract cofactor b : oeq n (mult a b) *)
                 val dvdAbs = Abs("k", natT, oeq nt (mult a (Bound 0)))
                 val pin =     (* oeq n 4 *)
                   exE_W (dvdAbs, oeq nt fourW) hdvd "b_c4"
                     (fn b => fn hb =>          (* hb : oeq n (mult a b) *)
                        let
                          val h1b = one_lt_b_W (a, b, nt) hb h1a han      (* lt 1 b = le 2 b *)
                          (* le 2 a (=h1a) , le 2 b (=h1b)
                             4 = 2*2 <= 2*b = b*2 <= b*a = a*b = n *)
                          val le_4_2b = mult_le_mono_W (twoW, twoW, b) h1b  (* le (2*2)(2*b) *)
                          val e22 = multEval 2 2                            (* 2*2 = 4 *)
                          val P4 = Term.lambda (Free("z_p4", natT)) (le (Free("z_p4", natT)) (mult twoW b))
                          val le_4_2b' = oeq_rw_W (P4, mult twoW twoW, fourW) e22 le_4_2b  (* le 4 (2*b) *)
                          val le_2a_ba = mult_le_mono_W (b, twoW, a) h1a    (* le (b*2)(b*a) *)
                          (* 2*b = b*2 *)
                          val c2b = multcomm_W (twoW, b)                    (* 2*b = b*2 *)
                          val P5 = Term.lambda (Free("z_p5", natT)) (le fourW (Free("z_p5", natT)))
                          val le_4_b2 = oeq_rw_W (P5, mult twoW b, mult b twoW) c2b le_4_2b'  (* le 4 (b*2) *)
                          val le_4_ba = le_trans_W (fourW, mult b twoW, mult b a) le_4_b2 le_2a_ba  (* le 4 (b*a) *)
                          (* b*a = a*b = n *)
                          val cba = multcomm_W (b, a)                       (* b*a = a*b *)
                          val P6 = Term.lambda (Free("z_p6", natT)) (le fourW (Free("z_p6", natT)))
                          val le_4_ab = oeq_rw_W (P6, mult b a, mult a b) cba le_4_ba  (* le 4 (a*b) *)
                          val hb_s = oeq_sym_vW OF [hb]                     (* mult a b = n *)
                          val le_4_n = oeq_rw_W (P6, mult a b, nt) hb_s le_4_ab  (* le 4 n *)
                          (* le n 4 (le_n4) + le 4 n => oeq n 4 *)
                        in le_antisym_W (nt, fourW) le_n4 le_4_n end)
                 (* rewrite goal neg (congFn n) using oeq n 4 -> not_cong4 at n=4 *)
                 val Pg = Term.lambda (Free("z_g4", natT))
                            (neg (cong (Free("z_g4", natT)) (factW (Free("z_g4", natT))) (sub (Free("z_g4", natT)) oneW)))
                 val pin_s = oeq_sym_vW OF [pin]                            (* oeq 4 n *)
               in oeq_rw_W (Pg, fourW, nt) pin_s not_cong4 end)
      in Thm.implies_intr (ctermW hnle4P) resInner end
  in disjE_W (lt fourW nt, neg (lt fourW nt), goalC) em4 caseGt caseLe end;

val () = out "WIFF_BACKWARD_OK\n";

(* ============================================================================
   FORWARD : Imp (prime2 n) (cong n (factW n)(n-1))  from Wilson.
   ============================================================================ *)
val wilson_vW = varify wilson;   (* prime2 p ==> cong p (lprod (upto (sub p 1)))(sub p 1) *)
fun forward_W nt =
  let
    val hpP = jT (prime2 nt) ; val hp = Thm.assume (ctermW hpP)
    val wi  = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW nt)] wilson_vW)
    val cg  = Thm.implies_elim wi hp     (* cong n (factW n)(n-1) ; note lprod(upto(sub n 1))=factW n, sub n 1=pm1 *)
  in impI_W (prime2 nt, congFn nt) (Thm.implies_intr (ctermW hpP) cg) end;

(* ============================================================================
   ASSEMBLE :  1<n ==> Conj (Imp (prime2 n) C) (Imp C (prime2 n))
   ============================================================================ *)
val wilson_iff =
  let
    val nF = Free("n", natT)
    val hp1P = jT (lt oneW nF) ; val hp1 = Thm.assume (ctermW hp1P)
    val C    = congFn nF
    (* FORWARD implication *)
    val fwd  = forward_W nF                       (* Imp (prime2 n) C *)
    (* BACKWARD implication : Imp C (prime2 n), via contrapositive *)
    val bwd =
      let
        val hcP = jT C ; val hc = Thm.assume (ctermW hcP)   (* assume cong n (factW n)(n-1) *)
        (* em (prime2 n) *)
        val emP = em_W (prime2 nF)
        val caseP =
          let val hpr = Thm.assume (ctermW (jT (prime2 nF)))
          in Thm.implies_intr (ctermW (jT (prime2 nF))) hpr end
        val caseNP =
          let
            val hnpr = Thm.assume (ctermW (jT (neg (prime2 nF))))   (* Imp (prime2 n) oFalse *)
            (* prime_cases n : Disj (prime2 n) (composite-existential, prime_cases grouping) *)
            val pc = prime_cases_W nF hp1
            (* convert prime_cases' divisor existential into composite n's grouping *)
            val toComposite =
                disjE_W (prime2 nF, mkEx (pc_pdAbs nF), composite nF) pc
                  (* prime2 case : contradicts ~prime2 -> ex falso composite *)
                  (let val hpr = Thm.assume (ctermW (jT (prime2 nF)))
                       val fls = mp_W (prime2 nF, oFalseC) hnpr hpr
                       val any = Thm.implies_elim (oFalse_elim_W (composite nF)) fls
                   in Thm.implies_intr (ctermW (jT (prime2 nF))) any end)
                  (* divisor case : reassociate the conjunction into composite *)
                  (let val hexP = jT (mkEx (pc_pdAbs nF))
                       val hex  = Thm.assume (ctermW hexP)
                       val r = exE_W (pc_pdAbs nF, composite nF) hex "d_tc"
                                 (fn d => fn hbody =>
                                    let
                                      (* hbody : Conj (Conj (1<d)(d<n)) (d|n) *)
                                      val inner = conjunct1_W (mkConj (lt oneW d)(lt d nF), dvd d nF) hbody
                                      val hdvd  = conjunct2_W (mkConj (lt oneW d)(lt d nF), dvd d nF) hbody
                                      val h1d   = conjunct1_W (lt oneW d, lt d nF) inner   (* 1<d *)
                                      val hdn   = conjunct2_W (lt oneW d, lt d nF) inner   (* d<n *)
                                      val cj2   = conjI_W (lt d nF, dvd d nF) hdn hdvd
                                      val cjf   = conjI_W (lt oneW d, mkConj (lt d nF)(dvd d nF)) h1d cj2
                                    in exI_W (comp_aAbs nF) d cjf end)
                   in Thm.implies_intr (ctermW hexP) r end)
            val hcomp = toComposite                       (* composite n *)
            val notCong = not_cong_of_composite_W (nF, hcomp, hp1)  (* neg (cong n (factW n)(n-1)) *)
            val fls = mp_W (C, oFalseC) notCong hc        (* oFalse (contradict assumed cong) *)
            val prime_from_false = Thm.implies_elim (oFalse_elim_W (prime2 nF)) fls
          in Thm.implies_intr (ctermW (jT (neg (prime2 nF)))) prime_from_false end
        val prime_n = disjE_W (prime2 nF, neg (prime2 nF), prime2 nF) emP caseP caseNP
      in impI_W (C, prime2 nF) (Thm.implies_intr (ctermW hcP) prime_n) end
    val iffConj = conjI_W (mkImp (prime2 nF) C, mkImp C (prime2 nF)) fwd bwd
  in varify (Thm.implies_intr (ctermW hp1P) iffConj) end;

val () = if length (Thm.hyps_of wilson_iff) = 0 then out "WIFF_0HYP\n" else out "WIFF_HASHYP\n";
val () = out "WIFF_ASSEMBLED\n";

(* ============================================================================
   VALIDATION : aconv intended + soundness probes.
   ============================================================================ *)
val nV   = Var(("n",0), natT);
val Cv   = cong nV (lprod (uptoF (sub nV oneW))) (sub nV oneW);
val iff_intended =
  Logic.mk_implies (jT (lt oneW nV),
    jT (mkConj (mkImp (prime2 nV) Cv) (mkImp Cv (prime2 nV))));
val r_iff = (length (Thm.hyps_of wilson_iff) = 0)
            andalso ((Thm.prop_of wilson_iff) aconv iff_intended);
val () = if r_iff then out "WIFF_ACONV_OK : 1<n ==> (prime2 n <-> cong n ((n-1)!) (n-1))\n"
         else (out ("WIFF_ACONV_FAIL\n  got      = "^Syntax.string_of_term ctxtW (Thm.prop_of wilson_iff)^"\n"
                    ^"  intended = "^Syntax.string_of_term ctxtW iff_intended^"\n"));

(* probe 1 : the iff genuinely needs the 1<n hypothesis (dropping it changes the prop) *)
val bogus_drop_1ltn =
  jT (mkConj (mkImp (prime2 nV) Cv) (mkImp Cv (prime2 nV)));
val probe_needs_1ltn = not ((Thm.prop_of wilson_iff) aconv bogus_drop_1ltn);
val () = if probe_needs_1ltn then out "PROBE_OK iff keeps the 1<n hypothesis\n"
         else out "PROBE_FAIL iff dropped 1<n\n";

(* probe 2 : the conclusion is a genuine biconditional (Conj of BOTH implications),
   not just the forward implication. *)
val bogus_fwd_only =
  Logic.mk_implies (jT (lt oneW nV), jT (mkImp (prime2 nV) Cv));
val probe_biconditional = not ((Thm.prop_of wilson_iff) aconv bogus_fwd_only);
val () = if probe_biconditional then out "PROBE_OK conclusion is a biconditional (both directions)\n"
         else out "PROBE_FAIL collapsed to forward-only\n";

(* probe 3 : the residue is (n-1) = -1, NOT 0 (would be the FALSE criterion). *)
val Cv0  = cong nV (lprod (uptoF (sub nV oneW))) ZeroC;
val bogus_residue0 =
  Logic.mk_implies (jT (lt oneW nV),
    jT (mkConj (mkImp (prime2 nV) Cv0) (mkImp Cv0 (prime2 nV))));
val probe_residue = not ((Thm.prop_of wilson_iff) aconv bogus_residue0);
val () = if probe_residue then out "PROBE_OK residue is (n-1) = -1, not 0\n"
         else out "PROBE_FAIL residue collapsed to 0\n";

val () =
  if r_iff andalso probe_needs_1ltn andalso probe_biconditional andalso probe_residue
  then out "WILSON_IFF_OK\n"
  else out "WILSON_IFF_FAILED\n";
val () = out "WIFF_DELTA_DONE\n";
