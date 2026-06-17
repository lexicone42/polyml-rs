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
