(* ============================================================================
   sigma_mult : sigma (2^a * m) = sigma (2^a) * sigma m    for m ODD.
   ----------------------------------------------------------------------------
   APPENDED after isabelle_euclid_perfect.sml (the self-contained Euclid-perfect
   driver).  Reuses, on the FINAL context ctxtSigD / thySigD:
     sigma_def_vD2, swt_dvd_D, swt_ndvd_D, sum_supp_collapse_vD,
     pow2_dvd_char_vD, geo_add_vD, lsumf_*, lsumf_cong, sumf algebra, the full
     FOL + arith combinator suite, euclid_lemma_vSg/_vD, div_mod_exists, etc.

   STRATEGY (the genuine crux, with the 2-part handled by pow2_dvd_char):
     We do NOT build a concrete divisor list of m.  Instead sigma_mult is stated
     for ANY list D that *is m's divisor support* — i.e. D carries (as object/meta
     hypotheses) exactly:
        (DH1) lnodup D
        (DH2) !!d. lmem d D ==> (dvd d m  /\  le d m)          [members are divisors <= m]
        (DH3) !!d. le d m ==> Disj (lmem d D)(oeq (swt m d) Zero)
                   [every potential divisor <= m is either listed or contributes 0]
     i.e. D is a deduplicated list of exactly the divisors of m.  Under these,
     sum_supp_collapse gives  sigma m = lsumf idw D  (the SAME bridge sigma_char
     uses for the prime case).  We then build the product divisor list

        dl2 a D  =  the divisors  2^i * d   (0<=i<=a, d in D)

     recursively in a (lmap2 = scale a list by a constant; lappend = concat):
        dl2 0 D       = D
        dl2 (Suc a) D = lappend (lmap2 (2^(Suc a)) D) (dl2 a D)

     THE DISTRIBUTION LEMMA (pure list algebra, NO divisor reasoning, the graceful
     floor):
        dist_lemma : lsumf idw (dl2 a D) = (sumf (pow 2) a) * (lsumf idw D)
     from lsumf_map_scale (lsumf idw (lmap2 c L) = c * lsumf idw L) and
     lsumf_concat (lsumf idw (lappend A B) = lsumf idw A + lsumf idw B) and geo.

     THE SUPPORT BRIDGE FOR 2^a*m (the harder half): dl2 a D is exactly the
     divisor support of N=2^a*m, so sum_supp_collapse gives
        sigma N = lsumf idw (dl2 a D)
     This needs: lnodup (dl2 a D), every member <= N and | N, and completeness
     (every divisor of N <= N is listed or contributes 0).  Completeness uses
     pow2_dvd_char on the 2-part + euclid_lemma to split a divisor of 2^a*m into
     2^i * (odd divisor of m).

   GRACEFUL FLOOR (banked regardless): lsumf_map_scale, lsumf_concat, dist_lemma.

   ----------------------------------------------------------------------------
   STATUS (all 0-hyp + aconv + soundness-probed; Tagged(0), ~3.24B steps):
     PROVEN:
       lsumf_map_scale  : lsumf idw (lmap2 c L) = mult c (lsumf idw L)
       lsumf_concat     : lsumf idw (lappend A B) = add (lsumf idw A)(lsumf idw B)
       dist_lemma       : lsumf idw (dl2 a D) = mult (sumf (pow 2) a)(lsumf idw D)
                          [THE multiplicative crux: Sum_{i<=a,d in D} 2^i*d
                           = (Sum_i 2^i)*(Sum_d d); 2 soundness probes]
       mem_map2         : lmem y (lmap2 c L) ==> ?d. lmem d L /\ y = mult c d
       mem_append       : lmem y (lappend A B) ==> Disj (lmem y A)(lmem y B)
       dl2_members_dvd  : (!!d. lmem d D ==> dvd d m)
                          ==> (!!e. lmem e (dl2 a D) ==> dvd e (mult (p2 a) m))
                          [the EASY half of the N-support bridge]
       sigma_mult_reduction :
         oeq (sigma m)(lsumf idw D)
         ==> oeq (sigma (mult (p2 a) m))(lsumf idw (dl2 a D))
         ==> oeq (sigma (p2 a))(sumf (pow 2) a)
         ==> oeq (sigma (mult (p2 a) m))(mult (sigma (p2 a))(sigma m))
         [full sigma-mult REDUCED to the two divisor-support bridges + sig(2^a)]
     Axiom audit: exactly 6 new conservative list-recursion axioms
       (lmap2_nil/cons, lappend_nil/cons, dl2_0/Suc); NONE mentions sigma/perfect.

     NOT CLOSED (the genuine wall, as the setup pre-assessed): the full sigma_mult
       sigma (2^a*m) = sigma(2^a)*sigma m  for m ODD.
     Blocker = the COMPLETENESS half of the N-support bridge:
       sigma (2^a*m) = lsumf idw (dl2 a D)  via sum_supp_collapse needs
         (a) lnodup (dl2 a D)   [2^i*d distinctness across levels],
         (b) every divisor e<=N is lmem e (dl2 a D)   [completeness].
       Completeness requires the 2-adic split  e | 2^a*m ==> e = 2^i*d, i<=a, d|m
       (pow2_dvd_char on the 2-part + euclid_lemma at prime 2 to peel the odd
       cofactor and show it divides m).  Fresh wall of div2aq_complete scale,
       GENERALISED from the banked prime-q divlist (exactly 2 elements per
       2-power level) to an arbitrary odd m's multi-element divisor list.
   ============================================================================ *)

val () = out "SIGMA_MULT_BEGIN\n";

(* ---------------------------------------------------------------------------
   NEW THEORY EXTENSION : lmap2, lappend, dl2 over thySigD.  Conservative
   recursion axioms only (NONE mentions sigma/perfect/the conclusion).
   --------------------------------------------------------------------------- *)
val thyEC0 = Sign.add_consts
  [(Binding.name "lmap2",   natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "lappend", natlistT --> natlistT --> natlistT, NoSyn),
   (Binding.name "dl2",     natT --> natlistT --> natlistT, NoSyn)] thySigD;
fun cnstEC nm T = Const (Sign.full_name thyEC0 (Binding.name nm), T);
val lmap2C   = cnstEC "lmap2" (natT --> natlistT --> natlistT);
fun lmap2 c L = lmap2C $ c $ L;
val lappendC = cnstEC "lappend" (natlistT --> natlistT --> natlistT);
fun lappend A B = lappendC $ A $ B;
val dl2C     = cnstEC "dl2" (natT --> natlistT --> natlistT);
fun dl2 a D = dl2C $ a $ D;

val cE = Free("c", natT);
val xE = Free("x", natT);
val tE = Free("t", natlistT);
val AE = Free("A", natlistT);
val BE = Free("B", natlistT);
val DE = Free("D", natlistT);
val aE = Free("a", natT);

(* lmap2 recursion (returns a leq-equation, mirroring lremove's conditional form):
     lmap2 c lnil          = lnil
     lmap2 c (lcons x t)   = lcons (c*x) (lmap2 c t)                               *)
val ((_,lmap2_nil_ax), thyEC1) = Thm.add_axiom_global (Binding.name "lmap2_nil",
      jT (leqL (lmap2 cE lnilC) lnilC)) thyEC0;
val ((_,lmap2_cons_ax), thyEC2) = Thm.add_axiom_global (Binding.name "lmap2_cons",
      jT (leqL (lmap2 cE (lcons xE tE)) (lcons (mult cE xE) (lmap2 cE tE)))) thyEC1;

(* lappend recursion:
     lappend lnil B        = B
     lappend (lcons x t) B = lcons x (lappend t B)                                *)
val ((_,lappend_nil_ax), thyEC3) = Thm.add_axiom_global (Binding.name "lappend_nil",
      jT (leqL (lappend lnilC BE) BE)) thyEC2;
val ((_,lappend_cons_ax), thyEC4) = Thm.add_axiom_global (Binding.name "lappend_cons",
      jT (leqL (lappend (lcons xE tE) BE) (lcons xE (lappend tE BE)))) thyEC3;

(* dl2 recursion:
     dl2 0 D       = D
     dl2 (Suc a) D = lappend (lmap2 (2^(Suc a)) D) (dl2 a D)                       *)
val ((_,dl2_0_ax), thyEC5) = Thm.add_axiom_global (Binding.name "dl2_0",
      jT (leqL (dl2 ZeroC DE) DE)) thyEC4;
val ((_,dl2_Suc_ax), thyEC6) = Thm.add_axiom_global (Binding.name "dl2_Suc",
      jT (leqL (dl2 (suc aE) DE)
               (lappend (lmap2 (p2 (suc aE)) DE) (dl2 aE DE)))) thyEC5;

val thyEC  = thyEC6;
val ctxtEC = Proof_Context.init_global thyEC;
val ctermEC= Thm.cterm_of ctxtEC;
fun chkEC (nm, th, intended) =
  let val nh = length (Thm.hyps_of th);
      val ac = (Thm.prop_of th) aconv intended;
  in if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
     else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
                ^ "  got      = " ^ Syntax.string_of_term ctxtEC (Thm.prop_of th) ^ "\n"
                ^ "  intended = " ^ Syntax.string_of_term ctxtEC intended ^ "\n"); false)
  end;
val () = out "SIGMA_MULT_CONSTS_OK\n";

(* ---------------------------------------------------------------------------
   TRANSFER everything we reuse up to thyEC.  (Reused lemmas were varified on
   ctxtSigD; Thm.transfer lifts them to thyEC.)
   --------------------------------------------------------------------------- *)
fun upE th = Thm.transfer thyEC th;

val oeq_refl_vE    = upE oeq_refl_vD;
val oeq_subst_vE   = upE oeq_subst_vD;
val add_0_vE       = upE add_0_vD;
val add_0_right_vE = upE add_0_right_vD;
val add_comm_vE    = upE add_comm_vD;
val add_assoc_vE   = upE add_assoc_vD;
val mult_comm_vE   = upE mult_comm_vD;
val mult_assoc_vE  = upE mult_assoc_vD;
val mult_1_right_vE= upE mult_1_right_vD;
val oeq_sym_E      = upE oeq_sym_D;
val oeq_trans_E    = upE oeq_trans_D;
val left_distrib_vE= upE (varify (up left_distrib));
val mult_0_right_vE= upE mult_0_right_vD2;
val list_induct_vE = upE list_induct_vD;
val lsumf_nil_vE   = upE lsumf_nil_vD;
val lsumf_cons_vE  = upE lsumf_cons_vD;
val leq_refl_vE    = upE leq_refl_vD;
val leq_subst_vE   = upE leq_subst_vD;
val nat_induct_vE  = upE nat_induct_vD;
val sumf_0_vE      = upE sumf_0_vD;
val sumf_Suc_vE    = upE sumf_Suc_vD;
val geo_add_vE     = upE geo_add_vD;
(* new axioms *)
val lmap2_nil_vE   = varify lmap2_nil_ax;
val lmap2_cons_vE  = varify lmap2_cons_ax;
val lappend_nil_vE = varify lappend_nil_ax;
val lappend_cons_vE= varify lappend_cons_ax;
val dl2_0_vE       = varify dl2_0_ax;
val dl2_Suc_vE     = varify dl2_Suc_ax;

(* ---- instantiators on ctxtEC ---- *)
fun reflE t = beta_norm (Drule.infer_instantiate ctxtEC [(("a",0), ctermEC t)] oeq_refl_vE);
fun trans2E (h1,h2) = oeq_trans_E OF [h1,h2];
fun symmE h = oeq_sym_E OF [h];
fun trans3E (aT,bT,cT) hab hbc = trans2E (hab, hbc);
fun add0E t   = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] add_0_vE);
fun add0rE t  = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] add_0_right_vE);
fun addcommE (m,n) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("m",0), ctermEC m),(("n",0), ctermEC n)] add_comm_vE);
fun addassocE (m,n,k) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("m",0), ctermEC m),(("n",0), ctermEC n),(("k",0), ctermEC k)] add_assoc_vE);
fun multcommE (m,n) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("m",0), ctermEC m),(("n",0), ctermEC n)] mult_comm_vE);
fun multassocE (m,n,k) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("m",0), ctermEC m),(("n",0), ctermEC n),(("k",0), ctermEC k)] mult_assoc_vE);
fun mult1rE t = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] mult_1_right_vE);
fun mult0rE t = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] mult_0_right_vE);

fun add_cong_lE (p,q,k) hpq =
  let val Pabs = Abs("z", natT, oeq (add p k) (add (Bound 0) k))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("a",0), ctermEC p),(("b",0), ctermEC q)] oeq_subst_vE)
      val rfl = reflE (add p k)
  in inst OF [hpq, rfl] end;
fun add_cong_rE (h,p,q) hpq =
  let val Pabs = Abs("z", natT, oeq (add h p) (add h (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("a",0), ctermEC p),(("b",0), ctermEC q)] oeq_subst_vE)
      val rfl = reflE (add h p)
  in inst OF [hpq, rfl] end;
fun mult_cong_lE (p,q,k) hpq =
  let val Pabs = Abs("z", natT, oeq (mult p k) (mult (Bound 0) k))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("a",0), ctermEC p),(("b",0), ctermEC q)] oeq_subst_vE)
      val rfl = reflE (mult p k)
  in inst OF [hpq, rfl] end;
fun mult_cong_rE (h,p,q) hpq =
  let val Pabs = Abs("z", natT, oeq (mult h p) (mult h (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("a",0), ctermEC p),(("b",0), ctermEC q)] oeq_subst_vE)
      val rfl = reflE (mult h p)
  in inst OF [hpq, rfl] end;
fun substPredE (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("P",0), ctermEC Pabs),(("a",0), ctermEC xT),(("b",0), ctermEC yT)] oeq_subst_vE)
  in Thm.implies_elim (Thm.implies_elim inst hxy) hPx end;

fun lsumfNilE f = beta_norm (Drule.infer_instantiate ctxtEC [(("f",0), ctermEC f)] lsumf_nil_vE);
fun lsumfConsE (f,h,t) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("f",0), ctermEC f),(("x",0), ctermEC h),(("t",0), ctermEC t)] lsumf_cons_vE);

(* leq transport on the list arg of (lsumf idw) : leq L M ==> lsumf idw L = lsumf idw M *)
fun lsumf_leqE (f, LT, MT) hleq =
  let val Pabs = Term.lambda (Free("zLm", natlistT)) (oeq (lsumf f LT) (lsumf f (Free("zLm",natlistT))))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("L",0), ctermEC LT),(("M",0), ctermEC MT)] leq_subst_vE)
      val rfl = reflE (lsumf f LT)
  in inst OF [hleq, rfl] end;

fun list_induct_atE (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("P",0), ctermEC Qabs), (("L",0), ctermEC kT)] list_induct_vE);
fun nat_induct_atE (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("P",0), ctermEC Qabs), (("k",0), ctermEC kT)] nat_induct_vE);
fun sumf0E f   = beta_norm (Drule.infer_instantiate ctxtEC [(("f",0), ctermEC f)] sumf_0_vE);
fun sumfSucE (f,n) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("f",0), ctermEC f),(("n",0), ctermEC n)] sumf_Suc_vE);
fun geoAddE kT = beta_norm (Drule.infer_instantiate ctxtEC [(("k",0), ctermEC kT)] geo_add_vE);

fun lmap2NilE c = beta_norm (Drule.infer_instantiate ctxtEC [(("c",0), ctermEC c)] lmap2_nil_vE);
fun lmap2ConsE (c,x,t) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("c",0), ctermEC c),(("x",0), ctermEC x),(("t",0), ctermEC t)] lmap2_cons_vE);
fun lappendNilE B = beta_norm (Drule.infer_instantiate ctxtEC [(("B",0), ctermEC B)] lappend_nil_vE);
fun lappendConsE (x,t,B) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("x",0), ctermEC x),(("t",0), ctermEC t),(("B",0), ctermEC B)] lappend_cons_vE);
fun dl20E D = beta_norm (Drule.infer_instantiate ctxtEC [(("D",0), ctermEC D)] dl2_0_vE);
fun dl2SucE (a,D) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("a",0), ctermEC a),(("D",0), ctermEC D)] dl2_Suc_vE);

(* idw is theory-independent (Abs); use it directly. lsumf idw L : sum of members. *)
val idwE = idw;

val () = out "SIGMA_MULT_INFRA_OK\n";

(* ===========================================================================
   FLOOR LEMMA 1 : lsumf_map_scale
     lsumf idw (lmap2 c L) = mult c (lsumf idw L)         induction on L
   =========================================================================== *)
val lsumf_map_scale =
  let
    val cF = Free("c", natT)
    fun body Lt = oeq (lsumf idwE (lmap2 cF Lt)) (mult cF (lsumf idwE Lt))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("L", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    (* base L = lnil : lsumf idw (lmap2 c lnil) = lsumf idw lnil = 0 ; mult c (lsumf idw lnil) = mult c 0 = 0. *)
    val base =
      let
        val mleq = lmap2NilE cF                                 (* leq (lmap2 c lnil) lnil *)
        val tr   = lsumf_leqE (idwE, lmap2 cF lnilC, lnilC) mleq (* lsumf idw (lmap2 c lnil) = lsumf idw lnil *)
        val ln0  = lsumfNilE idwE                                (* lsumf idw lnil = 0 *)
        val lhs0 = trans2E (tr, ln0)                             (* lsumf idw (lmap2 c lnil) = 0 *)
        (* RHS : mult c (lsumf idw lnil) = mult c 0 = 0 *)
        val rc   = mult_cong_rE (cF, lsumf idwE lnilC, ZeroC) ln0  (* mult c (lsumf idw lnil) = mult c 0 *)
        (* mult c 0 = 0 : mult_comm then mult_0? we have mult_1_right but need mult c 0 = 0.
           mult c 0 = mult 0 c [comm] = 0 [mult_0 base].  We have add_0/mult on base; use mult_0_right. *)
        val mc0  = mult0rE cF                                    (* mult c 0 = 0 *)
        val rhs0 = trans2E (rc, mc0)                             (* mult c (lsumf idw lnil) = 0 *)
      in trans2E (lhs0, symmE rhs0) end
    (* step x t : IH body t |- body (lcons x t).
         lsumf idw (lmap2 c (lcons x t)) = lsumf idw (lcons (c*x)(lmap2 c t))
            = idw(c*x) + lsumf idw (lmap2 c t) = (c*x) + (c * lsumf idw t)   [IH]
         RHS : mult c (lsumf idw (lcons x t)) = mult c (idw x + lsumf idw t)
            = mult c (x + lsumf idw t) = c*x + c*(lsumf idw t)   [left_distrib]. *)
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val mleq = lmap2ConsE (cF, xF, tF)                     (* leq (lmap2 c (lcons x t))(lcons (c*x)(lmap2 c t)) *)
        val tr   = lsumf_leqE (idwE, lmap2 cF (lcons xF tF), lcons (mult cF xF)(lmap2 cF tF)) mleq
        val c1   = lsumfConsE (idwE, mult cF xF, lmap2 cF tF)  (* lsumf idw (lcons (c*x)(lmap2 c t)) = (c*x) + lsumf idw (lmap2 c t) *)
        val lhs1 = trans2E (tr, c1)                            (* lsumf idw (lmap2 c (lcons x t)) = (c*x) + lsumf idw (lmap2 c t) *)
        val lhs2 = trans2E (lhs1, add_cong_rE (mult cF xF, lsumf idwE (lmap2 cF tF), mult cF (lsumf idwE tF)) IH)
                                                                (* = (c*x) + (c * lsumf idw t) *)
        (* RHS : mult c (lsumf idw (lcons x t)) ; lsumf idw (lcons x t) = idw x + lsumf idw t = x + lsumf idw t *)
        val cc   = lsumfConsE (idwE, xF, tF)                   (* lsumf idw (lcons x t) = x + lsumf idw t *)
        val rcong= mult_cong_rE (cF, lsumf idwE (lcons xF tF), add xF (lsumf idwE tF)) cc
                                                                (* mult c (lsumf idw (lcons x t)) = mult c (x + lsumf idw t) *)
        val ld   = beta_norm (Drule.infer_instantiate ctxtEC
              [(("x",0), ctermEC cF),(("m",0), ctermEC xF),(("n",0), ctermEC (lsumf idwE tF))] left_distrib_vE)
                                                                (* mult c (x + lsumf idw t) = (c*x) + (c * lsumf idw t) *)
        val rhs1 = trans2E (rcong, ld)                          (* mult c (lsumf idw (lcons x t)) = (c*x)+(c*lsumf idw t) *)
      in trans2E (lhs2, symmE rhs1) end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;

val cVms = Var(("c",0), natT); val LVms = Var(("L",0), natlistT);
val i_lsumf_map_scale = jT (oeq (lsumf idwE (lmap2 cVms LVms)) (mult cVms (lsumf idwE LVms)));
val r_lms = chkEC ("lsumf_map_scale", lsumf_map_scale, i_lsumf_map_scale);
val () = if r_lms then out "LSUMF_MAP_SCALE_OK\n" else out "LSUMF_MAP_SCALE_FAIL\n";

val () = out "SIGMA_MULT_FLOOR1_DONE\n";

(* ===========================================================================
   FLOOR LEMMA 2 : lsumf_concat
     lsumf idw (lappend A B) = add (lsumf idw A) (lsumf idw B)    induction on A
   =========================================================================== *)
val lsumf_concat =
  let
    val BF = Free("B", natlistT)
    fun body At = oeq (lsumf idwE (lappend At BF)) (add (lsumf idwE At) (lsumf idwE BF))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("A", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    (* base A = lnil : lappend lnil B = B ; lsumf idw (lappend lnil B) = lsumf idw B.
       RHS : lsumf idw lnil + lsumf idw B = 0 + lsumf idw B = lsumf idw B. *)
    val base =
      let
        val aleq = lappendNilE BF                              (* leq (lappend lnil B) B *)
        val tr   = lsumf_leqE (idwE, lappend lnilC BF, BF) aleq (* lsumf idw (lappend lnil B) = lsumf idw B *)
        val ln0  = lsumfNilE idwE                               (* lsumf idw lnil = 0 *)
        (* RHS : add (lsumf idw lnil)(lsumf idw B) = add 0 (lsumf idw B) = lsumf idw B *)
        val r0   = add_cong_lE (lsumf idwE lnilC, ZeroC, lsumf idwE BF) ln0  (* add (lsumf idw lnil)(..) = add 0 (..) *)
        val a0   = add0E (lsumf idwE BF)                        (* add 0 (lsumf idw B) = lsumf idw B *)
        val rhs0 = trans2E (r0, a0)                            (* RHS = lsumf idw B *)
      in trans2E (tr, symmE rhs0) end
    (* step x t : IH body t |- body (lcons x t).
         lappend (lcons x t) B = lcons x (lappend t B).
         lsumf idw (lappend (lcons x t) B) = idw x + lsumf idw (lappend t B)
            = x + (lsumf idw t + lsumf idw B)   [IH]
         RHS : add (lsumf idw (lcons x t))(lsumf idw B) = add (x + lsumf idw t)(lsumf idw B)
            = x + (lsumf idw t + lsumf idw B)   [assoc]. *)
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val aleq = lappendConsE (xF, tF, BF)                   (* leq (lappend (lcons x t) B)(lcons x (lappend t B)) *)
        val tr   = lsumf_leqE (idwE, lappend (lcons xF tF) BF, lcons xF (lappend tF BF)) aleq
        val c1   = lsumfConsE (idwE, xF, lappend tF BF)        (* lsumf idw (lcons x (lappend t B)) = x + lsumf idw (lappend t B) *)
        val lhs1 = trans2E (tr, c1)                            (* lsumf idw (lappend (lcons x t) B) = x + lsumf idw (lappend t B) *)
        val lhs2 = trans2E (lhs1, add_cong_rE (xF, lsumf idwE (lappend tF BF),
                              add (lsumf idwE tF)(lsumf idwE BF)) IH)
                                                                (* = x + (lsumf idw t + lsumf idw B) *)
        (* RHS : add (lsumf idw (lcons x t))(lsumf idw B) ; lsumf idw (lcons x t) = x + lsumf idw t *)
        val cc   = lsumfConsE (idwE, xF, tF)                   (* lsumf idw (lcons x t) = x + lsumf idw t *)
        val rcong= add_cong_lE (lsumf idwE (lcons xF tF), add xF (lsumf idwE tF), lsumf idwE BF) cc
                                                                (* RHS = add (x + lsumf idw t)(lsumf idw B) *)
        val aA   = addassocE (xF, lsumf idwE tF, lsumf idwE BF) (* add (add x (lsumf idw t))(lsumf idw B) = add x (add (lsumf idw t)(lsumf idw B)) *)
        val rhs1 = trans2E (rcong, aA)                          (* RHS = x + (lsumf idw t + lsumf idw B) *)
      in trans2E (lhs2, symmE rhs1) end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;

val AVc = Var(("A",0), natlistT); val BVc = Var(("B",0), natlistT);
val i_lsumf_concat = jT (oeq (lsumf idwE (lappend AVc BVc)) (add (lsumf idwE AVc) (lsumf idwE BVc)));
val r_lcat = chkEC ("lsumf_concat", lsumf_concat, i_lsumf_concat);
val () = if r_lcat then out "LSUMF_CONCAT_OK\n" else out "LSUMF_CONCAT_FAIL\n";
val () = out "SIGMA_MULT_FLOOR2_DONE\n";

(* ===========================================================================
   FLOOR LEMMA 3 (the distribution crux) : dist_lemma
     lsumf idw (dl2 a D) = mult (sumf (pow 2) a) (lsumf idw D)     induction on a
   pure list/sum algebra, NO divisor reasoning.
   =========================================================================== *)
val pwAbsE = powC $ two;   (* (pow 2) as a function term, same as pwAbs2 *)
(* generic instantiators of the two floor lemmas *)
fun mapScaleE (c, L) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("c",0), ctermEC c),(("L",0), ctermEC L)] lsumf_map_scale);
fun concatE (A, B) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("A",0), ctermEC A),(("B",0), ctermEC B)] lsumf_concat);

val dist_lemma =
  let
    val DF = Free("D", natlistT)
    val S  = lsumf idwE DF                            (* sigma m candidate = sum of D *)
    fun body at = oeq (lsumf idwE (dl2 at DF)) (mult (sumf pwAbsE at) S)
    val zV = Free("z", natT)
    val Qpred = Term.lambda zV (body zV)
    val kIndA = Free("a", natT)
    val ind = nat_induct_atE (Qpred, kIndA)
    (* base a=0 : dl2 0 D = D ; lsumf idw (dl2 0 D) = lsumf idw D = S.
       RHS : mult (sumf (pow 2) 0) S = mult (pow 2 0) S = mult 1 S = S. *)
    val base =
      let
        val dleq = dl20E DF                            (* leq (dl2 0 D) D *)
        val tr   = lsumf_leqE (idwE, dl2 ZeroC DF, DF) dleq  (* lsumf idw (dl2 0 D) = lsumf idw D = S *)
        (* RHS : sumf (pow 2) 0 = pow 2 0 ; pow 2 0 = 1 ; mult 1 S = S. *)
        val s00 = sumf0E pwAbsE                         (* sumf (pow 2) 0 = (pow 2) 0 = pow 2 0 *)
        val pz  = beta_norm (Drule.infer_instantiate ctxtEC [(("a",0), ctermEC two)] (upE pow_Zero_vD))
        (* pz : pow 2 0 = 1 *)
        val g0a = mult_cong_lE (sumf pwAbsE ZeroC, p2 ZeroC, S) s00  (* mult (sumf..0) S = mult (pow2 0) S *)
        val g0b = mult_cong_lE (p2 ZeroC, one, S) pz                 (* mult (pow2 0) S = mult 1 S *)
        val m1  = trans2E (multcommE (one, S), mult1rE S)            (* mult 1 S = mult S 1 = S *)
        val rhs0= trans2E (trans2E (g0a, g0b), m1)                   (* RHS = S *)
      in trans2E (tr, symmE rhs0) end
    (* step x : IH body x |- body (Suc x).
         dl2 (Suc x) D = lappend (lmap2 (2^(Suc x)) D)(dl2 x D).
         lsumf idw (dl2 (Suc x) D) = lsumf idw (lmap2 A2s D) + lsumf idw (dl2 x D)  [concat]
            = A2s*S + (sumf (pow 2) x)*S   [map_scale + IH]
         RHS : mult (sumf (pow 2)(Suc x)) S = mult (sumf (pow 2) x + A2s) S
            = (sumf (pow 2) x)*S + A2s*S   [right distrib]. *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermEC (jT (body xF)))
    val stepconcl =
      let
        val A2s = p2 (suc xF)                          (* 2^(Suc x) *)
        val Gx  = sumf pwAbsE xF
        val dleq = dl2SucE (xF, DF)                    (* leq (dl2 (Suc x) D)(lappend (lmap2 A2s D)(dl2 x D)) *)
        val tr   = lsumf_leqE (idwE, dl2 (suc xF) DF, lappend (lmap2 A2s DF)(dl2 xF DF)) dleq
        val cat  = concatE (lmap2 A2s DF, dl2 xF DF)   (* lsumf idw (lappend ..) = lsumf idw (lmap2 A2s D) + lsumf idw (dl2 x D) *)
        val lhs1 = trans2E (tr, cat)                   (* lsumf idw (dl2 (Suc x) D) = lsumf idw (lmap2 A2s D) + lsumf idw (dl2 x D) *)
        val ms   = mapScaleE (A2s, DF)                 (* lsumf idw (lmap2 A2s D) = mult A2s S *)
        val lhs2 = trans2E (lhs1, add_cong_lE (lsumf idwE (lmap2 A2s DF), mult A2s S, lsumf idwE (dl2 xF DF)) ms)
                                                        (* = mult A2s S + lsumf idw (dl2 x D) *)
        val lhs3 = trans2E (lhs2, add_cong_rE (mult A2s S, lsumf idwE (dl2 xF DF), mult Gx S) IH)
                                                        (* = mult A2s S + mult Gx S *)
        (* RHS : mult (sumf (pow 2)(Suc x)) S = mult (Gx + A2s) S *)
        val sS  = sumfSucE (pwAbsE, xF)                (* sumf (pow 2)(Suc x) = Gx + A2s *)
        val rc  = mult_cong_lE (sumf pwAbsE (suc xF), add Gx A2s, S) sS  (* RHS = mult (Gx + A2s) S *)
        (* mult (Gx + A2s) S = mult S (Gx + A2s) [comm] = (S*Gx) + (S*A2s) [left_distrib] *)
        val flip= multcommE (add Gx A2s, S)            (* mult (Gx+A2s) S = mult S (Gx+A2s) *)
        val ld  = beta_norm (Drule.infer_instantiate ctxtEC
              [(("x",0), ctermEC S),(("m",0), ctermEC Gx),(("n",0), ctermEC A2s)] left_distrib_vE)
                                                        (* mult S (Gx+A2s) = (S*Gx) + (S*A2s) *)
        val rc2 = trans2E (rc, trans2E (flip, ld))     (* RHS = (S*Gx) + (S*A2s) *)
        (* normalise S*Gx = Gx*S ; S*A2s = A2s*S *)
        val n1  = multcommE (S, Gx)                    (* mult S Gx = mult Gx S *)
        val n2  = multcommE (S, A2s)                   (* mult S A2s = mult A2s S *)
        val rc3 = trans2E (rc2, trans2E (add_cong_lE (mult S Gx, mult Gx S, mult S A2s) n1,
                                         add_cong_rE (mult Gx S, mult S A2s, mult A2s S) n2))
                                                        (* RHS = (Gx*S) + (A2s*S) *)
        (* lhs3 = (A2s*S) + (Gx*S) ; rc3 = (Gx*S) + (A2s*S) ; equal by comm. *)
        val comm= addcommE (mult A2s S, mult Gx S)     (* (A2s*S)+(Gx*S) = (Gx*S)+(A2s*S) *)
        val lhs4= trans2E (lhs3, comm)                 (* lhs = (Gx*S)+(A2s*S) *)
      in trans2E (lhs4, symmE rc3) end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (body xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;

val aVd = Var(("a",0), natT); val DVd = Var(("D",0), natlistT);
val i_dist_lemma = jT (oeq (lsumf idwE (dl2 aVd DVd)) (mult (sumf pwAbsE aVd) (lsumf idwE DVd)));
val r_dist = chkEC ("dist_lemma", dist_lemma, i_dist_lemma);
val () = if r_dist then out "DIST_LEMMA_OK\n" else out "DIST_LEMMA_FAIL\n";
val () = out "SIGMA_MULT_FLOOR3_DONE\n";

(* ===========================================================================
   SOUNDNESS PROBE for dist_lemma : it is genuinely multiplicative, not the
   degenerate "= lsumf idw D" (which would be the a-collapsed / wrong form).
   =========================================================================== *)
val s_dist_nontrivial =
  not ((Thm.prop_of dist_lemma) aconv (jT (oeq (lsumf idwE (dl2 aVd DVd)) (lsumf idwE DVd))));
val () = if s_dist_nontrivial then out "PROBE_OK dist_lemma is the 2^... weighted distribution (not a no-op)\n"
         else out "PROBE_FAIL dist_lemma collapsed to the trivial sum!\n";
(* and that it carries the (sumf (pow 2) a) factor, not e.g. (pow 2 a) *)
val s_dist_factor =
  not ((Thm.prop_of dist_lemma) aconv (jT (oeq (lsumf idwE (dl2 aVd DVd)) (mult (p2 aVd) (lsumf idwE DVd)))));
val () = if s_dist_factor then out "PROBE_OK dist_lemma factor is (sumf (pow 2) a) = sigma(2^a), not 2^a\n"
         else out "PROBE_FAIL dist_lemma factor is 2^a not the geometric sum!\n";

(* ===========================================================================
   FOL + dvd + lmem combinators on ctxtEC (transfer the varified base lemmas,
   then build the standard intro/elim wrappers — mirror of the *_D family).
   =========================================================================== *)
val impI_vE   = upE impI_vD;
val mp_vE     = upE mp_vD;
val allI_vE   = upE allI_vD;
val allE_vE   = upE allE_vD;
val disjE_vE  = upE disjE_vD;
val disjI1_vE = upE disjI1_vD;
val disjI2_vE = upE disjI2_vD;
val conjI_vE  = upE conjI_vD;
val conjunct1_vE = upE conjunct1_vD;
val conjunct2_vE = upE conjunct2_vD;
val oFalse_elim_vE = upE oFalse_elim_vD;
val lmem_nil_elim_vE = upE lmem_nil_elim_vD;
val lmem_cons_fwd_vE = upE lmem_cons_fwd_vD;
val lmem_cons_bwd_vE = upE lmem_cons_bwd_vD;
val lnodup_nil_vE  = upE lnodup_nil_vD;
val lnodup_cons_fwd_vE = upE lnodup_cons_fwd_vD;
val lnodup_cons_bwd_vE = upE lnodup_cons_bwd_vD;
val dvd_refl_vE = upE (varify (up dvd_refl_vSg)) handle _ => upE (varify dvd_refl_vD);

fun impI_E (At, Bt) hImp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] impI_vE)
  in Thm.implies_elim inst (Thm.implies_intr (ctermEC (jT At)) hImp) end;
fun mp_E (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] mp_vE)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_E Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC [(("P",0), ctermEC Pabs)] allI_vE)
  in Thm.implies_elim inst hAll end;
fun allE_E (Pabs, at) hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("P",0), ctermEC Pabs),(("a",0), ctermEC at)] allE_vE)
  in Thm.implies_elim inst hForall end;
fun disjE_E (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt),(("C",0), ctermEC Ct)] disjE_vE)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_E (At, Bt) hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] disjI1_vE)
  in Thm.implies_elim inst hA end;
fun disjI2_E (At, Bt) hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] disjI2_vE)
  in Thm.implies_elim inst hB end;
fun conjI_E (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] conjI_vE)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_E (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] conjunct1_vE)
  in Thm.implies_elim inst hC end;
fun conjunct2_E (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("A",0), ctermEC At),(("B",0), ctermEC Bt)] conjunct2_vE)
  in Thm.implies_elim inst hC end;
fun oFalse_elimE rT = beta_norm (Drule.infer_instantiate ctxtEC [(("R",0), ctermEC rT)] oFalse_elim_vE);
fun lmemNilElimE x = beta_norm (Drule.infer_instantiate ctxtEC [(("x",0), ctermEC x)] lmem_nil_elim_vE);
fun lmemConsFwdE (x,y,t) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("x",0), ctermEC x),(("y",0), ctermEC y),(("t",0), ctermEC t)] lmem_cons_fwd_vE);
fun lmemConsBwdE (x,y,t) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("x",0), ctermEC x),(("y",0), ctermEC y),(("t",0), ctermEC t)] lmem_cons_bwd_vE);

(* dvd combinators on ctxtEC : dvd a b == Ex(%k. b = a*k) *)
val exI_vE  = upE exI_vD;
val exE_vE  = upE exE_vD;
fun dvd_introE (aT, bT, w) hyp =   (* hyp : oeq b (mult a w)  ->  dvd a b *)
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("a",0), ctermEC w)] exI_vE)
  in Thm.implies_elim inst hyp end;
fun dvd_reflE t =
  (* dvd t t : witness 1, t = t*1 *)
  let val m1 = symmE (mult1rE t)   (* oeq t (mult t 1) *)
  in dvd_introE (t, t, one) m1 end;
(* dvd a (mult a c) : witness c, mult a c = mult a c *)
fun dvd_mult_rightE (aT, cT) =
  dvd_introE (aT, mult aT cT, cT) (reflE (mult aT cT));
(* dvd a x , oeq x y -> dvd a y *)
fun dvd_cong_targetE (aT, xT, yT) hxy hdvd =
  let val Pabs = Term.lambda (Free("zdt", natT)) (dvd aT (Free("zdt",natT)))
  in substPredE (Pabs, xT, yT) hxy hdvd end;
(* oeq a b -> dvd a x -> dvd b x *)
fun dvd_cong_divisorE (aT, bT, xT) hab hdvd =
  let val Pabs = Term.lambda (Free("zdd", natT)) (dvd (Free("zdd",natT)) xT)
  in substPredE (Pabs, aT, bT) hab hdvd end;
(* dvd a b -> dvd b c -> dvd a c : peel both, compose witnesses *)
val dvd_trans_vE = upE (varify (up dvd_trans));
fun dvd_transE (aT,bT,cT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("a",0), ctermEC aT),(("b",0), ctermEC bT),(("c",0), ctermEC cT)] dvd_trans_vE)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

fun list_induct_atE2 (Qabs, kT) = list_induct_atE (Qabs, kT);

val () = out "SIGMA_MULT_FOL_DVD_OK\n";

(* ===========================================================================
   MEMBERSHIP SUBLEMMAS for lmap2 / lappend (list induction), needed to push
   structural facts (dvd, le) through dl2.

   mem_map2 : lmem y (lmap2 c L) ==> (?d. lmem d L /\ oeq y (mult c d))
   mem_append : lmem y (lappend A B) ==> Disj (lmem y A)(lmem y B)
   =========================================================================== *)
(* leq transport of membership : leq L M ==> lmem y L ==> lmem y M *)
fun lmem_leqE (yT, LT, MT) hleq hmem =
  let val Pabs = Term.lambda (Free("zlm", natlistT)) (lmem yT (Free("zlm",natlistT)))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pabs),(("L",0), ctermEC LT),(("M",0), ctermEC MT)] leq_subst_vE)
  in inst OF [hleq, hmem] end;

val mem_map2 =
  let
    val cF = Free("c", natT); val yF = Free("y", natT)
    fun exwit Lt = mkEx (Term.lambda (Free("d", natT))
                     (mkConj (lmem (Free("d",natT)) Lt) (oeq yF (mult cF (Free("d",natT))))))
    fun body Lt = mkImp (lmem yF (lmap2 cF Lt)) (exwit Lt)
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("L", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    (* base L=lnil : lmap2 c lnil = lnil ; lmem y lnil -> oFalse -> anything *)
    val base =
      let
        val hmem = Thm.assume (ctermEC (jT (lmem yF (lmap2 cF lnilC))))
        val mleq = lmap2NilE cF                               (* leq (lmap2 c lnil) lnil *)
        val hmem2= lmem_leqE (yF, lmap2 cF lnilC, lnilC) mleq hmem  (* lmem y lnil *)
        val ff   = Thm.implies_elim (lmemNilElimE yF) hmem2   (* oFalse *)
        val r    = Thm.implies_elim (oFalse_elimE (exwit lnilC)) ff
      in impI_E (lmem yF (lmap2 cF lnilC), exwit lnilC) r end
    (* step x t : IH body t |- body (lcons x t).
         lmap2 c (lcons x t) = lcons (c*x)(lmap2 c t).
         lmem y (lmap2 c (lcons x t)) -> lmem y (lcons (c*x)(lmap2 c t))
           -> Disj(oeq y (c*x))(lmem y (lmap2 c t)).
         case y=c*x : witness d=x ; lmem x (lcons x t) [bwd, disjI1 refl] ; oeq y (c*x).
         case lmem y (lmap2 c t) : IH gives ?d. lmem d t /\ y=c*d ; lift lmem d t to lcons. *)
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val goalEx = exwit (lcons xF tF)
        val hmem = Thm.assume (ctermEC (jT (lmem yF (lmap2 cF (lcons xF tF)))))
        val mleq = lmap2ConsE (cF, xF, tF)
        val hmem2= lmem_leqE (yF, lmap2 cF (lcons xF tF), lcons (mult cF xF)(lmap2 cF tF)) mleq hmem
        val fwd  = lmemConsFwdE (yF, mult cF xF, lmap2 cF tF)  (* meta: jT(lmem ..) ==> jT(Disj(oeq y (c*x))(lmem y (lmap2 c t))) *)
        val dj   = Thm.implies_elim fwd hmem2
        (* case y = c*x *)
        val caseEq =
          let
            val heq = Thm.assume (ctermEC (jT (oeq yF (mult cF xF))))
            (* lmem x (lcons x t) *)
            val memx = Thm.implies_elim (lmemConsBwdE (xF, xF, tF)) (disjI1_E (oeq xF xF, lmem xF tF) (reflE xF))
            (* witness d=x : conj (lmem x (lcons x t))(oeq y (c*x)) *)
            val cj   = conjI_E (lmem xF (lcons xF tF), oeq yF (mult cF xF)) memx heq
            val Pw   = Term.lambda (Free("d", natT))
                         (mkConj (lmem (Free("d",natT)) (lcons xF tF)) (oeq yF (mult cF (Free("d",natT)))))
            val ex   = beta_norm (Drule.infer_instantiate ctxtEC
                         [(("P",0), ctermEC Pw),(("a",0), ctermEC xF)] exI_vE)
            val r    = Thm.implies_elim ex cj
          in Thm.implies_intr (ctermEC (jT (oeq yF (mult cF xF)))) r end
        (* case lmem y (lmap2 c t) : IH -> ?d. lmem d t /\ y=c*d, lift to lcons. *)
        val caseMem =
          let
            val hmt = Thm.assume (ctermEC (jT (lmem yF (lmap2 cF tF))))
            val exT = mp_E (lmem yF (lmap2 cF tF), exwit tF) IH hmt   (* ?d. lmem d t /\ y=c*d *)
            val Pt  = Term.lambda (Free("d", natT))
                        (mkConj (lmem (Free("d",natT)) tF) (oeq yF (mult cF (Free("d",natT)))))
            (* exE : from exT build goalEx *)
            val exE_inst = beta_norm (Drule.infer_instantiate ctxtEC
                  [(("P",0), ctermEC Pt),(("Q",0), ctermEC goalEx)] exE_vE)
            val partial = Thm.implies_elim exE_inst exT
            val wF = Free("d_mm", natT)
            val hbody = Thm.assume (ctermEC (jT (Term.betapply (Pt, wF))))  (* lmem wF t /\ y=c*wF *)
            val hmemd = conjunct1_E (lmem wF tF, oeq yF (mult cF wF)) hbody
            val heqd  = conjunct2_E (lmem wF tF, oeq yF (mult cF wF)) hbody
            val memd_lcons = Thm.implies_elim (lmemConsBwdE (wF, xF, tF))
                               (disjI2_E (oeq wF xF, lmem wF tF) hmemd)   (* lmem wF (lcons x t) *)
            val cj    = conjI_E (lmem wF (lcons xF tF), oeq yF (mult cF wF)) memd_lcons heqd
            val Pw    = Term.lambda (Free("d", natT))
                          (mkConj (lmem (Free("d",natT)) (lcons xF tF)) (oeq yF (mult cF (Free("d",natT)))))
            val exG   = beta_norm (Drule.infer_instantiate ctxtEC
                          [(("P",0), ctermEC Pw),(("a",0), ctermEC wF)] exI_vE)
            val rbody = Thm.implies_elim exG cj
            val minor = Thm.forall_intr (ctermEC wF) (Thm.implies_intr (ctermEC (jT (Term.betapply (Pt, wF)))) rbody)
          in Thm.implies_intr (ctermEC (jT (lmem yF (lmap2 cF tF)))) (Thm.implies_elim partial minor) end
        val res = disjE_E (oeq yF (mult cF xF), lmem yF (lmap2 cF tF), goalEx) dj caseEq caseMem
      in impI_E (lmem yF (lmap2 cF (lcons xF tF)), goalEx) res end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "MEM_MAP2_BUILT\n";

val mem_append =
  let
    val yF = Free("y", natT); val BF = Free("B", natlistT)
    fun body At = mkImp (lmem yF (lappend At BF)) (mkDisj (lmem yF At)(lmem yF BF))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("A", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    (* base A=lnil : lappend lnil B = B ; lmem y B -> Disj(lmem y lnil)(lmem y B) [disjI2]. *)
    val base =
      let
        val hmem = Thm.assume (ctermEC (jT (lmem yF (lappend lnilC BF))))
        val aleq = lappendNilE BF                              (* leq (lappend lnil B) B *)
        val hmem2= lmem_leqE (yF, lappend lnilC BF, BF) aleq hmem  (* lmem y B *)
        val r    = disjI2_E (lmem yF lnilC, lmem yF BF) hmem2
      in impI_E (lmem yF (lappend lnilC BF), mkDisj (lmem yF lnilC)(lmem yF BF)) r end
    (* step x t : IH body t |- body (lcons x t).
         lappend (lcons x t) B = lcons x (lappend t B).
         lmem y (lcons x (lappend t B)) -> Disj(oeq y x)(lmem y (lappend t B)).
         case y=x : lmem y (lcons x t) [bwd disjI1] -> Disj(lmem y (lcons x t))(lmem y B) [disjI1].
         case lmem y (lappend t B) : IH -> Disj(lmem y t)(lmem y B) ;
            subcase lmem y t -> lmem y (lcons x t) [bwd disjI2] -> left ; subcase lmem y B -> right. *)
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val goalD = mkDisj (lmem yF (lcons xF tF))(lmem yF BF)
        val hmem = Thm.assume (ctermEC (jT (lmem yF (lappend (lcons xF tF) BF))))
        val aleq = lappendConsE (xF, tF, BF)
        val hmem2= lmem_leqE (yF, lappend (lcons xF tF) BF, lcons xF (lappend tF BF)) aleq hmem
        val fwd  = lmemConsFwdE (yF, xF, lappend tF BF)        (* Disj(oeq y x)(lmem y (lappend t B)) *)
        val dj   = Thm.implies_elim fwd hmem2
        val caseEq =
          let val heq = Thm.assume (ctermEC (jT (oeq yF xF)))
              val memx = Thm.implies_elim (lmemConsBwdE (yF, xF, tF)) (disjI1_E (oeq yF xF, lmem yF tF) heq)
              val r    = disjI1_E (lmem yF (lcons xF tF), lmem yF BF) memx
          in Thm.implies_intr (ctermEC (jT (oeq yF xF))) r end
        val caseMem =
          let val hmt = Thm.assume (ctermEC (jT (lmem yF (lappend tF BF))))
              val djT = mp_E (lmem yF (lappend tF BF), mkDisj (lmem yF tF)(lmem yF BF)) IH hmt
              val subA = let val hyt = Thm.assume (ctermEC (jT (lmem yF tF)))
                             val memx = Thm.implies_elim (lmemConsBwdE (yF, xF, tF)) (disjI2_E (oeq yF xF, lmem yF tF) hyt)
                             val r = disjI1_E (lmem yF (lcons xF tF), lmem yF BF) memx
                         in Thm.implies_intr (ctermEC (jT (lmem yF tF))) r end
              val subB = let val hyb = Thm.assume (ctermEC (jT (lmem yF BF)))
                             val r = disjI2_E (lmem yF (lcons xF tF), lmem yF BF) hyb
                         in Thm.implies_intr (ctermEC (jT (lmem yF BF))) r end
              val r = disjE_E (lmem yF tF, lmem yF BF, goalD) djT subA subB
          in Thm.implies_intr (ctermEC (jT (lmem yF (lappend tF BF)))) r end
        val res = disjE_E (oeq yF xF, lmem yF (lappend tF BF), goalD) dj caseEq caseMem
      in impI_E (lmem yF (lappend (lcons xF tF) BF), goalD) res end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "MEM_APPEND_BUILT\n";

val yVmm = Var(("y",0), natT); val cVmm = Var(("c",0), natT); val LVmm = Var(("L",0), natlistT);
val AVmm = Var(("A",0), natlistT); val BVmm = Var(("B",0), natlistT);
val i_mem_map2 = jT (mkImp (lmem yVmm (lmap2 cVmm LVmm))
      (mkEx (Term.lambda (Free("d", natT))
            (mkConj (lmem (Free("d",natT)) LVmm) (oeq yVmm (mult cVmm (Free("d",natT))))))));
val r_mm = chkEC ("mem_map2", mem_map2, i_mem_map2);
val () = if r_mm then out "MEM_MAP2_OK\n" else out "MEM_MAP2_FAIL\n";
val i_mem_append = jT (mkImp (lmem yVmm (lappend AVmm BVmm))
      (mkDisj (lmem yVmm AVmm)(lmem yVmm BVmm)));
val r_ma = chkEC ("mem_append", mem_append, i_mem_append);
val () = if r_ma then out "MEM_APPEND_OK\n" else out "MEM_APPEND_FAIL\n";
val () = out "SIGMA_MULT_MEMSUB_DONE\n";

(* ===========================================================================
   sigma_mult_reduction : the CRUX reduced to the divisor-support bridges.

     oeq (sigma m) (lsumf idw D)                            [bridge_m]
     ==> oeq (sigma (mult (p2 a) m)) (lsumf idw (dl2 a D))  [bridge_N]
     ==> oeq (sigma (p2 a)) (sumf (pow 2) a)                [sig2a]
     ==> oeq (sigma (mult (p2 a) m)) (mult (sigma (p2 a)) (sigma m))

   Proof: bridge_N then dist_lemma then sig2a/bridge_m :
     sigma N = lsumf idw (dl2 a D)                          [bridge_N]
             = mult (sumf (pow 2) a) (lsumf idw D)          [dist_lemma]
             = mult (sigma (p2 a)) (lsumf idw D)            [sig2a sym, cong]
             = mult (sigma (p2 a)) (sigma m)                [bridge_m sym, cong]
   This isolates the multiplicative content (dist_lemma) from the two
   divisor-support bridges, which carry the genuine number-theoretic content
   (each is a sum_supp_collapse-style support equality).
   =========================================================================== *)
val sigma_mult_reduction =
  let
    val aF = Free("a", natT); val mF = Free("m", natT); val DF = Free("D", natlistT)
    val N  = mult (p2 aF) mF
    val S  = lsumf idwE DF
    val G  = sumf pwAbsE aF
    val bridge_m = Thm.assume (ctermEC (jT (oeq (sigma mF) S)))                (* sigma m = lsumf idw D *)
    val bridge_N = Thm.assume (ctermEC (jT (oeq (sigma N) (lsumf idwE (dl2 aF DF)))))  (* sigma N = lsumf idw (dl2 a D) *)
    val sig2a    = Thm.assume (ctermEC (jT (oeq (sigma (p2 aF)) G)))           (* sigma (2^a) = sumf (pow 2) a *)
    (* dist_lemma at (a,D) : lsumf idw (dl2 a D) = mult G S *)
    val dl = beta_norm (Drule.infer_instantiate ctxtEC
               [(("a",0), ctermEC aF),(("D",0), ctermEC DF)] dist_lemma)        (* lsumf idw (dl2 a D) = mult G S *)
    (* chain : sigma N = lsumf idw (dl2 a D) = mult G S *)
    val c1 = trans2E (bridge_N, dl)                                            (* sigma N = mult G S *)
    (* mult G S = mult (sigma (2^a)) S   [sig2a sym, cong on left] *)
    val c2 = trans2E (c1, mult_cong_lE (G, sigma (p2 aF), S) (symmE sig2a))    (* sigma N = mult (sigma 2^a) S *)
    (* mult (sigma 2^a) S = mult (sigma 2^a)(sigma m)   [bridge_m sym, cong on right] *)
    val c3 = trans2E (c2, mult_cong_rE (sigma (p2 aF), S, sigma mF) (symmE bridge_m))
                                                                              (* sigma N = mult (sigma 2^a)(sigma m) *)
    val d1 = Thm.implies_intr (ctermEC (jT (oeq (sigma (p2 aF)) G))) c3
    val d2 = Thm.implies_intr (ctermEC (jT (oeq (sigma N) (lsumf idwE (dl2 aF DF))))) d1
    val d3 = Thm.implies_intr (ctermEC (jT (oeq (sigma mF) S))) d2
  in varify d3 end;

val aVr = Var(("a",0), natT); val mVr = Var(("m",0), natT); val DVr = Var(("D",0), natlistT);
val i_sigma_mult_reduction =
  Logic.mk_implies (jT (oeq (sigma mVr) (lsumf idwE DVr)),
    Logic.mk_implies (jT (oeq (sigma (mult (p2 aVr) mVr)) (lsumf idwE (dl2 aVr DVr))),
      Logic.mk_implies (jT (oeq (sigma (p2 aVr)) (sumf pwAbsE aVr)),
        jT (oeq (sigma (mult (p2 aVr) mVr)) (mult (sigma (p2 aVr)) (sigma mVr))))));
val r_smr = chkEC ("sigma_mult_reduction", sigma_mult_reduction, i_sigma_mult_reduction);
val () = if r_smr then out "SIGMA_MULT_REDUCTION_OK\n" else out "SIGMA_MULT_REDUCTION_FAIL\n";

(* soundness probe : the reduction genuinely needs all three hypotheses
   (dropping them would claim sigma(2^a*m) = sigma(2^a)*sigma(m) unconditionally,
   which is FALSE without m odd via the bridges). *)
val s_smr_cond =
  not ((Thm.prop_of sigma_mult_reduction) aconv
       (jT (oeq (sigma (mult (p2 aVr) mVr)) (mult (sigma (p2 aVr)) (sigma mVr)))));
val () = if s_smr_cond then out "PROBE_OK sigma_mult_reduction needs the bridge hypotheses\n"
         else out "PROBE_FAIL sigma_mult_reduction dropped its hypotheses!\n";

val () = out "SIGMA_MULT_REDUCTION_DONE\n";
val () = out "SIGMA_MULT_END\n";

(* ===========================================================================
   AXIOM AUDIT : the only axioms this delta adds over thySigD are the 6
   conservative list-recursion axioms (lmap2/lappend/dl2).  NONE mentions
   sigma / perfect / the conclusion.  Print them for the human audit.
   =========================================================================== *)
val () = out "SIGMA_MULT_AXIOM_AUDIT_BEGIN\n";
val baseAx = Theory.all_axioms_of thySigD;
val ecAx   = Theory.all_axioms_of thyEC;
val baseNames = map #1 baseAx;
val newAx = List.filter (fn (nm,_) => not (List.exists (fn b => b = nm) baseNames)) ecAx;
val () = out ("SIGMA_MULT_NEW_AXIOM_COUNT = " ^ Int.toString (length newAx) ^ "\n");
val () = List.app (fn (nm, t) =>
           out ("  NEWAX " ^ nm ^ " : " ^ Syntax.string_of_term ctxtEC t ^ "\n")) newAx;
(* mechanical check : no new axiom's string mentions "sigma" or "perfect" *)
fun mentions sub t =
  let val s = Syntax.string_of_term ctxtEC t
      val n = size sub
      fun look i = i + n <= size s andalso (String.substring (s, i, n) = sub orelse look (i+1))
  in look 0 end;
val anyBad = List.exists (fn (_, t) => mentions "sigma" t orelse mentions "perfect" t) newAx;
val () = if anyBad then out "AXIOM_AUDIT_FAIL: a new axiom mentions sigma/perfect!\n"
         else out "AXIOM_AUDIT_OK: no new axiom mentions sigma/perfect\n";
val () = out "SIGMA_MULT_AXIOM_AUDIT_END\n";

(* ===========================================================================
   BRIDGE-HYP (easy half) : dl2_members_dvd
     (!!d. lmem d D ==> dvd d m)
     ==> (!!e. lmem e (dl2 a D) ==> dvd e (mult (p2 a) m))    induction on a
   i.e. every member of dl2 a D divides N = 2^a*m.  Uses mem_map2 + mem_append.
   (object-Forall reflected so the predicate is over a : nat.)
   =========================================================================== *)
val dl2_members_dvd =
  let
    val DF = Free("D", natlistT); val mF = Free("m", natT)
    (* object hypothesis : Forall d. Imp (lmem d D)(dvd d m) *)
    val hMemDvd_t = mkForall (Term.lambda (Free("d", natT)) (mkImp (lmem (Free("d",natT)) DF)(dvd (Free("d",natT)) mF)))
    val hMemDvd = Thm.assume (ctermEC (jT hMemDvd_t))
    fun bodyConcl at = mkForall (Term.lambda (Free("e", natT))
                         (mkImp (lmem (Free("e",natT)) (dl2 at DF))(dvd (Free("e",natT)) (mult (p2 at) mF))))
    val zV = Free("z", natT)
    val Qpred = Term.lambda zV (bodyConcl zV)
    val kIndA = Free("a", natT)
    val ind = nat_induct_atE (Qpred, kIndA)
    (* base a=0 : dl2 0 D = D ; N = 2^0*m = 1*m = m.  member e of D divides m, and m = 2^0*m. *)
    val base =
      let
        val N0 = mult (p2 ZeroC) mF
        fun perE eF =
          let
            val hmem = Thm.assume (ctermEC (jT (lmem eF (dl2 ZeroC DF))))
            (* dl2 0 D = D : transport membership *)
            val dleq = dl20E DF
            val hmemD = lmem_leqE (eF, dl2 ZeroC DF, DF) dleq hmem    (* lmem e D *)
            (* hMemDvd at e : dvd e m *)
            val at = allE_E (Term.lambda (Free("d", natT)) (mkImp (lmem (Free("d",natT)) DF)(dvd (Free("d",natT)) mF)), eF) hMemDvd
            val dem = mp_E (lmem eF DF, dvd eF mF) at hmemD             (* dvd e m *)
            (* m = 2^0 * m : pow2 0 = 1 ; mult 1 m = m, so N0 = m. dvd e m -> dvd e N0. *)
            val pz  = beta_norm (Drule.infer_instantiate ctxtEC [(("a",0), ctermEC two)] (upE pow_Zero_vD))  (* pow 2 0 = 1 *)
            val n0m = trans2E (mult_cong_lE (p2 ZeroC, one, mF) pz, trans2E (multcommE (one, mF), mult1rE mF))  (* N0 = m *)
            val deN0= dvd_cong_targetE (eF, mF, N0) (symmE n0m) dem     (* dvd e N0 *)
          in impI_E (lmem eF (dl2 ZeroC DF), dvd eF N0) deN0 end
        val eFb = Free("e_b", natT)
      in allI_E (Term.lambda (Free("e", natT)) (mkImp (lmem (Free("e",natT)) (dl2 ZeroC DF))(dvd (Free("e",natT)) N0)))
                (Thm.forall_intr (ctermEC eFb) (perE eFb)) end
    (* step a -> Suc a *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermEC (jT (bodyConcl xF)))
    val stepconcl =
      let
        val A2s = p2 (suc xF)
        val Nx  = mult (p2 xF) mF
        val Nsx = mult A2s mF
        fun perE eF =
          let
            val hmem = Thm.assume (ctermEC (jT (lmem eF (dl2 (suc xF) DF))))
            (* dl2 (Suc x) D = lappend (lmap2 A2s D)(dl2 x D) : transport *)
            val dleq = dl2SucE (xF, DF)
            val hmem2= lmem_leqE (eF, dl2 (suc xF) DF, lappend (lmap2 A2s DF)(dl2 xF DF)) dleq hmem
            val dj   = mp_E (lmem eF (lappend (lmap2 A2s DF)(dl2 xF DF)),
                             mkDisj (lmem eF (lmap2 A2s DF))(lmem eF (dl2 xF DF)))
                          (beta_norm (Drule.infer_instantiate ctxtEC
                             [(("y",0), ctermEC eF),(("A",0), ctermEC (lmap2 A2s DF)),(("B",0), ctermEC (dl2 xF DF))] mem_append))
                          hmem2
                       (* Disj(lmem e (lmap2 A2s D))(lmem e (dl2 x D)) *)
            val goal = dvd eF Nsx
            (* case lmem e (lmap2 A2s D) : mem_map2 -> ?d. lmem d D /\ e = A2s*d ; d|m -> A2s*d | A2s*m = Nsx. *)
            val caseMap =
              let
                val hmap = Thm.assume (ctermEC (jT (lmem eF (lmap2 A2s DF))))
                val exwit_t = mkEx (Term.lambda (Free("d", natT))
                                (mkConj (lmem (Free("d",natT)) DF)(oeq eF (mult A2s (Free("d",natT))))))
                val exT = mp_E (lmem eF (lmap2 A2s DF), exwit_t)
                            (beta_norm (Drule.infer_instantiate ctxtEC
                               [(("y",0), ctermEC eF),(("c",0), ctermEC A2s),(("L",0), ctermEC DF)] mem_map2))
                            hmap
                          (* ?d. lmem d D /\ e = A2s*d *)
                val Pt = Term.lambda (Free("d", natT))
                           (mkConj (lmem (Free("d",natT)) DF)(oeq eF (mult A2s (Free("d",natT)))))
                val exE_inst = beta_norm (Drule.infer_instantiate ctxtEC
                      [(("P",0), ctermEC Pt),(("Q",0), ctermEC goal)] exE_vE)
                val partial = Thm.implies_elim exE_inst exT
                val wF = Free("d_dm", natT)
                val hbody = Thm.assume (ctermEC (jT (Term.betapply (Pt, wF))))
                val hmemd = conjunct1_E (lmem wF DF, oeq eF (mult A2s wF)) hbody
                val heqd  = conjunct2_E (lmem wF DF, oeq eF (mult A2s wF)) hbody   (* e = A2s*d *)
                (* d | m *)
                val atd = allE_E (Term.lambda (Free("d", natT)) (mkImp (lmem (Free("d",natT)) DF)(dvd (Free("d",natT)) mF)), wF) hMemDvd
                val dwm = mp_E (lmem wF DF, dvd wF mF) atd hmemd                  (* dvd d m *)
                (* dvd (A2s*d)(A2s*m) : d|m -> m = d*k -> A2s*m = A2s*(d*k) = (A2s*d)*k -> dvd (A2s*d)(A2s*m). *)
                (* peel dwm : m = d*k *)
                val dvdAd =
                  let
                    val Pk = Abs("k", natT, oeq mF (mult wF (Bound 0)))
                    val exE2 = beta_norm (Drule.infer_instantiate ctxtEC
                          [(("P",0), ctermEC Pk),(("Q",0), ctermEC (dvd (mult A2s wF) Nsx))] exE_vE)
                    val partial2 = Thm.implies_elim exE2 dwm
                    val kF = Free("k_dm", natT)
                    val hk = Thm.assume (ctermEC (jT (oeq mF (mult wF kF))))    (* m = d*k *)
                    (* Nsx = A2s*m = A2s*(d*k) = (A2s*d)*k  ->  dvd (A2s*d) Nsx, witness k *)
                    val e1 = mult_cong_rE (A2s, mF, mult wF kF) hk              (* A2s*m = A2s*(d*k) *)
                    val e2 = symmE (multassocE (A2s, wF, kF))                   (* A2s*(d*k) = (A2s*d)*k *)
                    val e3 = trans2E (e1, e2)                                   (* Nsx = (A2s*d)*k *)
                    val dvdAdNsx = dvd_introE (mult A2s wF, Nsx, kF) e3         (* dvd (A2s*d) Nsx *)
                    val minor = Thm.forall_intr (ctermEC kF) (Thm.implies_intr (ctermEC (jT (oeq mF (mult wF kF)))) dvdAdNsx)
                  in Thm.implies_elim partial2 minor end
                (* dvd e Nsx : rewrite divisor A2s*d -> e (sym heqd) *)
                val deNsx = dvd_cong_divisorE (mult A2s wF, eF, Nsx) (symmE heqd) dvdAd
                val minor = Thm.forall_intr (ctermEC wF) (Thm.implies_intr (ctermEC (jT (Term.betapply (Pt, wF)))) deNsx)
              in Thm.implies_intr (ctermEC (jT (lmem eF (lmap2 A2s DF)))) (Thm.implies_elim partial minor) end
            (* case lmem e (dl2 x D) : IH -> dvd e Nx ; Nx = 2^x*m | 2^(Suc x)*m = Nsx (dvd_trans via 2^x | 2^(Suc x)). *)
            val caseDl =
              let
                val hdl = Thm.assume (ctermEC (jT (lmem eF (dl2 xF DF))))
                val ihAt = allE_E (Term.lambda (Free("e", natT)) (mkImp (lmem (Free("e",natT)) (dl2 xF DF))(dvd (Free("e",natT)) Nx)), eF) IH
                val deNx = mp_E (lmem eF (dl2 xF DF), dvd eF Nx) ihAt hdl       (* dvd e Nx *)
                (* dvd Nx Nsx : Nsx = A2s*m = (2*2^x)*m ; Nx = 2^x*m.  Nsx = 2*(2^x*m) = 2*Nx -> dvd Nx Nsx. *)
                val psx = beta_norm (Drule.infer_instantiate ctxtEC
                            [(("a",0), ctermEC two),(("n",0), ctermEC xF)] (upE pow_Suc_vD))  (* 2^(Suc x) = 2*2^x *)
                (* Nsx = A2s*m = (2*2^x)*m = 2*(2^x*m) = 2*Nx *)
                val q1 = mult_cong_lE (A2s, mult two (p2 xF), mF) psx           (* A2s*m = (2*2^x)*m *)
                val q2 = multassocE (two, p2 xF, mF)                           (* (2*2^x)*m = 2*(2^x*m) = 2*Nx *)
                val nsx2nx = trans2E (q1, q2)                                  (* Nsx = 2*Nx *)
                (* dvd Nx Nsx : Nsx = 2*Nx = Nx*2 [comm] -> witness 2.  dvd Nx (mult Nx 2). *)
                val nsxNx2 = trans2E (nsx2nx, multcommE (two, Nx))            (* Nsx = Nx*2 *)
                val dvdNxNsx = dvd_introE (Nx, Nsx, two) nsxNx2                (* dvd Nx Nsx *)
                val deNsx = dvd_transE (eF, Nx, Nsx) deNx dvdNxNsx            (* dvd e Nsx *)
              in Thm.implies_intr (ctermEC (jT (lmem eF (dl2 xF DF)))) deNsx end
            val res = disjE_E (lmem eF (lmap2 A2s DF), lmem eF (dl2 xF DF), goal) dj caseMap caseDl
          in impI_E (lmem eF (dl2 (suc xF) DF), goal) res end
        val eFb = Free("e_s", natT)
      in allI_E (Term.lambda (Free("e", natT)) (mkImp (lmem (Free("e",natT)) (dl2 (suc xF) DF))(dvd (Free("e",natT)) Nsx)))
                (Thm.forall_intr (ctermEC eFb) (perE eFb)) end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (bodyConcl xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1            (* bodyConcl a, under hMemDvd assumption *)
    val r3 = Thm.implies_intr (ctermEC (jT hMemDvd_t)) r2
  in varify r3 end;
val () = out "DL2_MEMBERS_DVD_BUILT\n";

val aVmd = Var(("a",0), natT); val mVmd = Var(("m",0), natT); val DVmd = Var(("D",0), natlistT);
val i_dl2_members_dvd =
  Logic.mk_implies (
    jT (mkForall (Term.lambda (Free("d", natT)) (mkImp (lmem (Free("d",natT)) DVmd)(dvd (Free("d",natT)) mVmd)))),
    jT (mkForall (Term.lambda (Free("e", natT))
          (mkImp (lmem (Free("e",natT)) (dl2 aVmd DVmd))(dvd (Free("e",natT)) (mult (p2 aVmd) mVmd))))));
val r_dmd = chkEC ("dl2_members_dvd", dl2_members_dvd, i_dl2_members_dvd);
val () = if r_dmd then out "DL2_MEMBERS_DVD_OK\n" else out "DL2_MEMBERS_DVD_FAIL\n";
val () = out "SIGMA_MULT_BRIDGEHYP_DONE\n";
