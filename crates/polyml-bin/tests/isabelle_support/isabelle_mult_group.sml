(* ============================================================================
   THE MULTIPLICATIVE GROUP MOD p (the Wilson keystones) in Isabelle/Pure on the
   polyml-rs interpreter.  (test: isabelle_mult_group.rs)
   ----------------------------------------------------------------------------
   The algebraic core of (Z/pZ)*, each a 0-hypothesis theorem by genuine LCF
   kernel inference over the two-sided congruence cong:

     inverse_unique : |- cong p (a*b) 1 ==> cong p (a*c) 1 ==> cong p b c
                      the modular inverse is unique -- a pure congruence chain
                      (b == b*1 == b*(a*c) = (a*b)*c == 1*c == c), no primality.
     mod_cancel     : |- prime p ==> ~(p dvd a) ==> cong p (a*b) (a*c) ==> cong p b c
                      cancellation by a unit: from a*b == a*c get a*(b-c) == 0,
                      then euclid_lemma + ~(p|a) give p | (b-c).
     lagrange_roots : |- prime p ==> cong p (a*a) 1 ==> (cong p a 1 \/ cong p (Suc a) 0)
                      LAGRANGE'S THEOREM ON SQUARE ROOTS OF UNITY: the only square
                      roots of 1 mod a prime are +-1 (here -1 is Suc a == 0, so no
                      truncated subtraction). Via the identity (a-1)(a+1) = a^2-1
                      and euclid_lemma.

   These are the algebraic heart of Wilson's theorem. Built on the full gcd /
   Bezout / Euclid-lemma development (isabelle_gcd.sml + ntbase) over the
   classical foundation, spliced in by common::with_gcd. Each carries a soundness
   probe. Proved by a multi-seat ultracode fleet racing all three concurrently
   (wf_3eef19b5-87f); re-verified end-to-end by hand.

   (Full Wilson additionally needs the finite-product combinator prodf merged
   onto this modular base + a product-pairing/permutation lemma -- a separate
   base-unification effort.)
   ============================================================================ *)


(* ============================================================================
   INVERSE_UNIQUE :  cong p (mult a b) 1 ==> cong p (mult a c) 1 ==> cong p b c
   (uniqueness of the modular inverse).  No primality, no induction, no euclid.
   Pure congruence chain via cong_trans / cong_mult / cong_refl / cong_sym,
   with plain equalities lifted to congruences by oeq_subst.
   All cterms routed through the FINAL context ctxtS2 / ctermS2.
   ============================================================================ *)

val () = out "INVERSE_UNIQUE_BEGIN\n";

(* ---- lift the modular congruence lemmas onto ctxtS2 (schematic) ---- *)
val cong_refl_vS  = varify cong_refl;
val cong_sym_vS   = varify cong_sym;
val cong_trans_vS = varify cong_trans;
val cong_mult_vS  = varify cong_mult;

(* cong_refl_atS (m,a) : jT (cong m a a) *)
fun cong_refl_atS (mt, at) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("a",0), ctermS2 at)] cong_refl_vS);

(* cong_sym_atS (m,a,b) h : from jT (cong m a b) build jT (cong m b a) *)
fun cong_sym_atS (mt, at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at), (("b",0), ctermS2 bt)] cong_sym_vS)
  in Thm.implies_elim inst h end;

(* cong_trans_atS (m,a,b,c) h1 h2 : from cong m a b, cong m b c build cong m a c *)
fun cong_trans_atS (mt, at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at),
         (("b",0), ctermS2 bt), (("c",0), ctermS2 ct)] cong_trans_vS)
      val s1 = Thm.implies_elim inst h1
  in Thm.implies_elim s1 h2 end;

(* cong_mult_atS (m,a,a2,b,b2) h1 h2 :
     from cong m a a2, cong m b b2 build cong m (mult a b)(mult a2 b2) *)
fun cong_mult_atS (mt, at, a2t, bt, b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at), (("a2",0), ctermS2 a2t),
         (("b",0), ctermS2 bt), (("b2",0), ctermS2 b2t)] cong_mult_vS)
      val s1 = Thm.implies_elim inst h1
  in Thm.implies_elim s1 h2 end;

(* ---- mult-congruence on the LEFT operand on ctxtS2:
        oeq p q ==> oeq (mult p k) (mult q k) ---- *)
fun mult_cong_lS (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vS);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (mult pT kT))] oeq_refl_vS);
  in inst OF [hpq, refl_pk] end;

(* ---- mult_1_left / mult_assoc / mult_comm on ctxtS2 ---- *)
val mult_1_left_vS = varify mult_1_left;     (* oeq (mult (Suc 0) n) n *)
val mult_assoc_vS  = varify mult_assoc;       (* oeq (mult (mult m n) k)(mult m (mult n k)) *)
val mult_comm_vS   = varify mult_comm;        (* oeq (mult m n)(mult n m) *)
fun mult1lS_at t       = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_1_left_vS);
fun multassocS_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt),(("k",0), ctermS2 kt)] mult_assoc_vS);
fun multcommS_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] mult_comm_vS);

(* ---- cong_of_eq : from heq : oeq X Y build jT (cong p X Y) (p fixed).
        Take cong_refl (cong p X X), then rewrite the SECOND argument X->Y by
        oeq_subst with predicate %z. cong p X z.  CAPTURE-SAFE: build the
        predicate with Term.lambda over a fresh Free, NOT Abs(...,Bound 0)
        (the SML `cong` constructor inserts its own inner existential Abs, so a
        literal Bound 0 would be captured by that inner k-binder). ---- *)
fun cong_of_eqS (pT, X, Y) heq =
  let
    val zF   = Free("z_coe", natT);
    val Pabs = Term.lambda zF (cong pT X zF);                  (* %z. cong p X z (capture-safe) *)
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 X), (("b",0), ctermS2 Y)] oeq_subst_vS);
    val crefl = cong_refl_atS (pT, X);                          (* cong p X X *)
  in inst OF [heq, crefl] end;

(* ============================================================================
   THE PROOF
   ============================================================================ *)
val inverse_unique =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val bF = Free("b", natT);
    val cF = Free("c", natT);
    val one = oneC;                                             (* Suc Zero *)

    val H1prop = jT (cong pF (mult aF bF) one);                 (* cong p (a*b) 1 *)
    val H2prop = jT (cong pF (mult aF cF) one);                 (* cong p (a*c) 1 *)
    val H1 = Thm.assume (ctermS2 H1prop);
    val H2 = Thm.assume (ctermS2 H2prop);

    (* intermediate product terms *)
    val bo  = mult bF one;            (* b * 1     *)
    val bac = mult bF (mult aF cF);   (* b * (a*c) *)
    val abc = mult (mult aF bF) cF;   (* (a*b) * c *)
    val oc  = mult one cF;            (* 1 * c     *)

    (* ---- T1 : cong p b (b*1)   [from oeq b (b*1) = sym (mult_1_right b)] ---- *)
    val eq_b_bo = oeq_sym OF [mult1rS_at bF];                   (* oeq b (mult b 1) *)
    val T1 = cong_of_eqS (pF, bF, bo) eq_b_bo;                  (* cong p b (b*1) *)

    (* ---- T2 : cong p (b*1) (b*(a*c))
            = cong_mult (cong_refl b) (cong_sym H2 : cong p 1 (a*c)) ---- *)
    val crefl_b = cong_refl_atS (pF, bF);                       (* cong p b b *)
    val H2sym   = cong_sym_atS (pF, mult aF cF, one) H2;        (* cong p 1 (a*c) *)
    val T2 = cong_mult_atS (pF, bF, bF, one, mult aF cF) crefl_b H2sym;
                                                                (* cong p (b*1)(b*(a*c)) *)

    (* ---- T3 : cong p (b*(a*c)) ((a*b)*c)  [PLAIN equality] ----
       b*(a*c) = (b*a)*c   [sym mult_assoc b a c]
       (b*a)*c = (a*b)*c   [mult_comm b a, lifted on left operand by *c] *)
    val assoc_sym = oeq_sym OF [multassocS_at (bF, aF, cF)];    (* oeq (b*(a*c)) ((b*a)*c) *)
    val comm_ba   = multcommS_at (bF, aF);                      (* oeq (b*a) (a*b) *)
    val comm_lift = mult_cong_lS (mult bF aF, mult aF bF, cF) comm_ba;
                                                                (* oeq ((b*a)*c) ((a*b)*c) *)
    val eq_bac_abc = oeq_trans OF [assoc_sym, comm_lift];       (* oeq (b*(a*c)) ((a*b)*c) *)
    val T3 = cong_of_eqS (pF, bac, abc) eq_bac_abc;

    (* ---- T4 : cong p ((a*b)*c) (1*c)
            = cong_mult (H1 : cong p (a*b) 1) (cong_refl c : cong p c c) ---- *)
    val crefl_c = cong_refl_atS (pF, cF);                       (* cong p c c *)
    val T4 = cong_mult_atS (pF, mult aF bF, one, cF, cF) H1 crefl_c;
                                                                (* cong p ((a*b)*c)(1*c) *)

    (* ---- T5 : cong p (1*c) c   [from oeq (1*c) c = mult_1_left c] ---- *)
    val eq_oc_c = mult1lS_at cF;                                (* oeq (mult 1 c) c *)
    val T5 = cong_of_eqS (pF, oc, cF) eq_oc_c;                  (* cong p (1*c) c *)

    (* ---- chain everything with cong_trans ---- *)
    val C12   = cong_trans_atS (pF, bF, bo, bac) T1 T2;         (* cong p b (b*(a*c)) *)
    val C123  = cong_trans_atS (pF, bF, bac, abc) C12 T3;       (* cong p b ((a*b)*c) *)
    val C1234 = cong_trans_atS (pF, bF, abc, oc) C123 T4;       (* cong p b (1*c) *)
    val Cfull = cong_trans_atS (pF, bF, oc, cF) C1234 T5;       (* cong p b c *)

    (* discharge the two hypotheses *)
    val d1 = Thm.implies_intr (ctermS2 H2prop) Cfull;
    val d2 = Thm.implies_intr (ctermS2 H1prop) d1;
  in varify d2 end;

val () = out "INVERSE_UNIQUE_PROVED\n";

(* ---- validation ---- *)
val pViu = Var (("p",0), natT);
val aViu = Var (("a",0), natT);
val bViu = Var (("b",0), natT);
val cViu = Var (("c",0), natT);
val inverse_unique_intended =
  Logic.mk_implies (jT (cong pViu (mult aViu bViu) oneC),
    Logic.mk_implies (jT (cong pViu (mult aViu cViu) oneC),
      jT (cong pViu bViu cViu)));
val r_iu = checkS2 ("inverse_unique", inverse_unique, inverse_unique_intended);
val () = if r_iu then out "OK inverse_unique\n" else out "FAIL inverse_unique\n";

(* ---- SOUNDNESS PROBE : dropping the SECOND hypothesis is false.
        cong p (a*b) 1 ==> cong p b c  is NOT a theorem (c is unconstrained).
        The genuine theorem must NOT aconv that dropped-hyp statement. ---- *)
val inverse_unique_BOGUS =
  Logic.mk_implies (jT (cong pViu (mult aViu bViu) oneC),
      jT (cong pViu bViu cViu));
val probe_iu = not ((Thm.prop_of inverse_unique) aconv inverse_unique_BOGUS);
val () = if probe_iu then out "PROBE_OK (dropped-hyp variant not aconv proved thm)\n"
                     else out "PROBE_UNSOUND (proved thm aconv a dropped-hyp statement!)\n";

val () = if r_iu andalso probe_iu then out "INVERSE_UNIQUE_OK\n"
                                  else out "INVERSE_UNIQUE_FAILED\n";

(* ============================================================================
   TARGET : mod_cancel
     |- prime p ==> ~(p dvd a) ==> cong p (a*b) (a*c) ==> cong p b c
   A coprime-to-p factor a can be cancelled in a congruence.
   Built on ctxtS2 (the euclid/modular base context).  Reuses euclid_lemma,
   le_total, add_left_cancel, mult monotonicity helpers, cong_introL pattern.
   ============================================================================ *)

val () = out "MOD_CANCEL_BEGIN\n";

(* euclid_lemma on ctxtS2 : jT (prime2 p) ==> jT (dvd p (a*b)) ==> jT (Disj (dvd p a)(dvd p b)) *)
val euclid_lemma_vMC = varify euclid_lemma;
fun euclid_atMC (pT, aT, bT) hPr hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("a",0), ctermS2 aT), (("b",0), ctermS2 bT)] euclid_lemma_vMC)
  in Thm.implies_elim (Thm.implies_elim inst hPr) hDvd end;

val mod_cancel =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val bF = Free("b", natT);
    val cF = Free("c", natT);

    val hPrimeP = jT (prime2 pF);          val hPrime = Thm.assume (ctermS2 hPrimeP);
    val hNdvdP  = jT (neg (dvd pF aF));     val hNdvd  = Thm.assume (ctermS2 hNdvdP);
    val hCongP  = jT (cong pF (mult aF bF) (mult aF cF));
    val hCong   = Thm.assume (ctermS2 hCongP);

    val goalC = cong pF bF cF;

    (* ---- a <> 0  (else p | 0 = a contradicts ~(p|a)) ---- *)
    val axne0 =
      let
        val ha0 = Thm.assume (ctermS2 (jT (oeq aF ZeroC)));        (* a = 0 *)
        val z_p0 = oeq_sym OF [mult0rS_at pF];                     (* 0 = p*0 *)
        val dvd_p0 = dvd_introS (pF, ZeroC, ZeroC) z_p0;           (* dvd p 0 *)
        val dvd_pa = dvd_cong_rS (pF, ZeroC, aF) (oeq_sym OF [ha0]) dvd_p0;  (* dvd p a *)
        val fls = mp_atS2 (dvd pF aF, oFalseC) hNdvd dvd_pa;       (* oFalse *)
        val metaNe = Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC))) fls;
      in impI_atS2 (oeq aF ZeroC, oFalseC) metaNe end;            (* jT (neg (oeq a 0)) *)
    val aSucEx = ne0_suc_atS aF axne0;                             (* Ex m. oeq a (Suc m) *)

    (* ---- cancel_core : le X Y  ==>  oeq (a*Y) ((a*X) + p*k)  ==>  jT (congL p X Y)
            (Ex j. Y = X + p*j).  No a>0 needed (euclid kills the a-branch). ---- *)
    fun cancel_core (X, Y, kT) hle heqYX =
      let
        val leAbs = Abs("q", natT, oeq Y (add X (Bound 0)));       (* le X Y body *)
        fun body dW (hd : thm) =                                   (* hd : oeq Y (add X dW) *)
          let
            val mcong = mult_cong_rS (aF, Y, add X dW) hd;         (* a*Y = a*(X+d) *)
            val ld    = left_distrib_atS (aF, X, dW);              (* a*(X+d) = a*X + a*d *)
            val aYeq  = oeq_trans OF [mcong, ld];                  (* a*Y = a*X + a*d *)
            val combined = oeq_trans OF [oeq_sym OF [aYeq], heqYX];(* (a*X + a*d) = (a*X + p*k) *)
            val adk   = add_left_cancel_atS (mult aF X, mult aF dW, mult pF kT) combined; (* a*d = p*k *)
            val dvd_p_ad = dvd_introS (pF, mult aF dW, kT) adk;    (* dvd p (a*d) *)
            val eDisj = euclid_atMC (pF, aF, dW) hPrime dvd_p_ad;  (* Disj (dvd p a)(dvd p d) *)
            val goalCL = congL pF X Y;                             (* Ex j. Y = X + p*j *)
            (* case dvd p a : contradiction *)
            val caseA =
              let
                val hda = Thm.assume (ctermS2 (jT (dvd pF aF)));
                val fls = mp_atS2 (dvd pF aF, oFalseC) hNdvd hda; (* oFalse *)
                val any = oFalse_elimS_at goalCL;                  (* jT oFalse ==> jT goalCL *)
              in Thm.implies_intr (ctermS2 (jT (dvd pF aF))) (Thm.implies_elim any fls) end;
            (* case dvd p d : d = p*j -> Y = X + p*j -> congL *)
            val caseD =
              let
                val hdd = Thm.assume (ctermS2 (jT (dvd pF dW)));
                val dvdAbs = Abs("k", natT, oeq dW (mult pF (Bound 0)));   (* dvd p d body *)
                fun jbody jW (hj : thm) =                          (* hj : oeq d (p*j) *)
                  let
                    val ac = add_cong_rS (X, dW, mult pF jW) hj;  (* (X+d) = (X + p*j) *)
                    val Yeq = oeq_trans OF [hd, ac];               (* Y = X + p*j *)
                    val congLabs = Abs("k", natT, oeq Y (add X (mult pF (Bound 0))));
                  in exI_atS2 congLabs jW Yeq end;                 (* jT (congL p X Y) *)
                val res = exE_elimS2 (dvdAbs, goalCL) hdd "j_mc" jbody;
              in Thm.implies_intr (ctermS2 (jT (dvd pF dW))) res end;
            val g = disjE_elimS2 (dvd pF aF, dvd pF dW, goalCL) eDisj caseA caseD;
          in g end;                                               (* jT (congL p X Y) *)
        val res = exE_elimS2 (leAbs, congL pF X Y) hle "d_mc" body;
      in res end;

    (* ---- deg_core : le X Y ==> oeq (a*X) ((a*Y) + p*k) ==> oeq X Y
            (the "wrong direction": smaller X has bigger multiple -> equality).
            Needs a = Suc a0 (passed in via aSuc on a0W). ---- *)
    fun deg_core (X, Y, kT) (a0W, aSuc) hle heqXY =
      let
        val leAbs = Abs("q", natT, oeq Y (add X (Bound 0)));
        fun body dW (hd : thm) =                                  (* hd : oeq Y (add X dW) *)
          let
            val mcong = mult_cong_rS (aF, Y, add X dW) hd;        (* a*Y = a*(X+d) *)
            val ld    = left_distrib_atS (aF, X, dW);             (* a*(X+d) = a*X + a*d *)
            val aYeq  = oeq_trans OF [mcong, ld];                 (* a*Y = a*X + a*d *)
            (* rewrite a*Y inside heqXY's RHS *)
            val rw1 = add_cong_lS (mult aF Y, add (mult aF X) (mult aF dW), mult pF kT) aYeq;
                                                                   (* (a*Y + p*k) = ((a*X+a*d) + p*k) *)
            val eq2 = oeq_trans OF [heqXY, rw1];                  (* a*X = ((a*X+a*d) + p*k) *)
            val assoc = addassocS_at (mult aF X, mult aF dW, mult pF kT);
                                                                   (* ((a*X+a*d)+p*k) = (a*X + (a*d+p*k)) *)
            val eq3 = oeq_trans OF [eq2, assoc];                  (* a*X = a*X + (a*d+p*k) *)
            val W   = add (mult aF dW) (mult pF kT);
            val lhs0 = add0rS_at (mult aF X);                     (* (a*X + 0) = a*X *)
            val eq4 = oeq_trans OF [lhs0, eq3];                   (* (a*X + 0) = (a*X + W) *)
            val zeroW = add_left_cancel_atS (mult aF X, ZeroC, W) eq4;  (* 0 = W *)
            val Weq0 = oeq_sym OF [zeroW];                        (* W = 0 ; i.e. (a*d + p*k) = 0 *)
            val aedW0 = add_eq_zero_left OF [Weq0];               (* a*d = 0 *)
            (* a = Suc a0 : (Suc a0)*d = d + a0*d ; a*d=0 -> d + a0*d = 0 -> d = 0 *)
            val c1 = mult_cong_lS (aF, suc a0W, dW) aSuc;         (* a*d = (Suc a0)*d *)
            val sucdW0 = oeq_trans OF [oeq_sym OF [c1], aedW0];   (* (Suc a0)*d = 0 *)
            val ms = mult_Suc_atS (a0W, dW);                      (* (Suc a0)*d = d + a0*d *)
            val sum0 = oeq_trans OF [oeq_sym OF [ms], sucdW0];    (* (d + a0*d) = 0 *)
            val dW0 = add_eq_zero_left OF [sum0];                 (* d = 0 *)
            (* Y = X + d, d = 0 -> Y = X *)
            val chain1 = oeq_trans OF [add_cong_rS (X, dW, ZeroC) dW0, add0rS_at X]; (* (X+d) = X *)
            val Yeqx = oeq_trans OF [hd, chain1];                 (* Y = X *)
          in oeq_sym OF [Yeqx] end;                               (* oeq X Y *)
        val res = exE_elimS2 (leAbs, oeq X Y) hle "d_dc" body;
      in res end;

    (* ---- cong_of_eq : oeq X Y ==> jT (cong p X Y)  (witness 0 on congL) ---- *)
    fun cong_of_eq (X, Y) hXY =
      let
        val m0 = mult0rS_at pF;                                   (* p*0 = 0 *)
        val acr = add_cong_rS (X, mult pF ZeroC, ZeroC) m0;       (* (X + p*0) = (X + 0) *)
        val a0r = add0rS_at X;                                    (* (X + 0) = X *)
        val xpx = oeq_trans OF [acr, a0r];                        (* (X + p*0) = X *)
        val x_xp0 = oeq_sym OF [xpx];                             (* X = (X + p*0) *)
        val Ybody = oeq_trans OF [oeq_sym OF [hXY], x_xp0];       (* Y = (X + p*0) *)
        val congLabs = Abs("k", natT, oeq Y (add X (mult pF (Bound 0))));
        val exL = exI_atS2 congLabs ZeroC Ybody;                 (* jT (congL p X Y) *)
      in disjI1S2_at (congL pF X Y, congR pF X Y) exL end;        (* jT (cong p X Y) *)

    (* ---- a = Suc a0 in scope, then case split ---- *)
    fun mainWithASuc a0W aSuc =
      let
        (* hypothesis cong p (a*b) (a*c) = Disj (congL ..)(congR ..) *)
        val dL = congL pF (mult aF bF) (mult aF cF);              (* Ex k. a*c = a*b + p*k *)
        val dR = congR pF (mult aF bF) (mult aF cF);              (* Ex k. a*b = a*c + p*k *)

        (* ===== CASE L : a*c = a*b + p*k ===== *)
        val caseL =
          let
            val hL = Thm.assume (ctermS2 (jT dL));
            val lAbs = Abs("k", natT, oeq (mult aF cF) (add (mult aF bF) (mult pF (Bound 0))));
            fun lbody kW (hk : thm) =          (* hk : a*c = a*b + p*k  (a*Y = a*X + p*k ; Y=c,X=b) *)
              let
                val lt = le_total_atS (bF, cF);                  (* Disj (le b c)(le c b) *)
                (* sub : le b c -> cancel_core(b,c) -> congL p b c -> cong via disjI1 *)
                val subBC =
                  let
                    val hbc = Thm.assume (ctermS2 (jT (le bF cF)));
                    val cl = cancel_core (bF, cF, kW) hbc hk;     (* jT (congL p b c) *)
                    val g  = disjI1S2_at (congL pF bF cF, congR pF bF cF) cl;
                  in Thm.implies_intr (ctermS2 (jT (le bF cF))) g end;
                (* sub : le c b -> deg_core(c,b) -> oeq c b -> oeq b c -> cong_of_eq *)
                val subCB =
                  let
                    val hcb = Thm.assume (ctermS2 (jT (le cF bF)));
                    val ecb = deg_core (cF, bF, kW) (a0W, aSuc) hcb hk;  (* oeq c b *)
                    val ebc = oeq_sym OF [ecb];                  (* oeq b c *)
                    val g   = cong_of_eq (bF, cF) ebc;           (* cong p b c *)
                  in Thm.implies_intr (ctermS2 (jT (le cF bF))) g end;
                val g = disjE_elimS2 (le bF cF, le cF bF, goalC) lt subBC subCB;
              in g end;
            val res = exE_elimS2 (lAbs, goalC) hL "kL_mc" lbody;
          in Thm.implies_intr (ctermS2 (jT dL)) res end;

        (* ===== CASE R : a*b = a*c + p*k ===== *)
        val caseR =
          let
            val hR = Thm.assume (ctermS2 (jT dR));
            val rAbs = Abs("k", natT, oeq (mult aF bF) (add (mult aF cF) (mult pF (Bound 0))));
            fun rbody kW (hk : thm) =          (* hk : a*b = a*c + p*k  (a*Y = a*X + p*k ; Y=b,X=c) *)
              let
                val lt = le_total_atS (cF, bF);                  (* Disj (le c b)(le b c) *)
                (* sub : le c b -> cancel_core(c,b) -> congL p c b = congR p b c -> disjI2 *)
                val subCB =
                  let
                    val hcb = Thm.assume (ctermS2 (jT (le cF bF)));
                    val cl = cancel_core (cF, bF, kW) hcb hk;     (* jT (congL p c b) = (Ex j. b = c + p*j) *)
                    val g  = disjI2S2_at (congL pF bF cF, congR pF bF cF) cl;
                  in Thm.implies_intr (ctermS2 (jT (le cF bF))) g end;
                (* sub : le b c -> deg_core(b,c) -> oeq b c -> cong_of_eq *)
                val subBC =
                  let
                    val hbc = Thm.assume (ctermS2 (jT (le bF cF)));
                    val ebc = deg_core (bF, cF, kW) (a0W, aSuc) hbc hk;  (* oeq b c *)
                    val g   = cong_of_eq (bF, cF) ebc;           (* cong p b c *)
                  in Thm.implies_intr (ctermS2 (jT (le bF cF))) g end;
                val g = disjE_elimS2 (le cF bF, le bF cF, goalC) lt subCB subBC;
              in g end;
            val res = exE_elimS2 (rAbs, goalC) hR "kR_mc" rbody;
          in Thm.implies_intr (ctermS2 (jT dR)) res end;

        val g = disjE_elimS2 (dL, dR, goalC) hCong caseL caseR;
      in g end;

    (* exE on a = Suc a0 *)
    val aSucAbs = Abs("m", natT, oeq aF (suc (Bound 0)));
    fun aSucBody a0W (haSuc : thm) = mainWithASuc a0W haSuc;
    val bodyGoal = exE_elimS2 (aSucAbs, goalC) aSucEx "a0_mc" aSucBody;

    (* discharge the three hypotheses *)
    val d1 = Thm.implies_intr (ctermS2 hCongP) bodyGoal;
    val d2 = Thm.implies_intr (ctermS2 hNdvdP) d1;
    val d3 = Thm.implies_intr (ctermS2 hPrimeP) d2;
  in varify d3 end;

val () = out "MOD_CANCEL_PROVED\n";

(* ---- validation : 0-hyp + aconv the TARGET ---- *)
val pVmc = Var (("p",0), natT);
val aVmc = Var (("a",0), natT);
val bVmc = Var (("b",0), natT);
val cVmc = Var (("c",0), natT);
val mod_cancel_intended =
  Logic.mk_implies (jT (prime2 pVmc),
    Logic.mk_implies (jT (neg (dvd pVmc aVmc)),
      Logic.mk_implies (jT (cong pVmc (mult aVmc bVmc) (mult aVmc cVmc)),
        jT (cong pVmc bVmc cVmc))));
val r_mc =
  let
    val nh = length (Thm.hyps_of mod_cancel);
    val ac = (Thm.prop_of mod_cancel) aconv mod_cancel_intended;
  in
    if nh = 0 andalso ac then (out "OK mod_cancel\n"; true)
    else (out ("FAIL mod_cancel (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtS2 (Thm.prop_of mod_cancel) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtS2 mod_cancel_intended ^ "\n");
          false)
  end;

(* ---- soundness probe : dropping ~(p|a) must NOT be provable
        (p=2, a=2 : cong 2 (2*1) (2*0) i.e. cong 2 2 0 holds, but cong 2 1 0 false). *)
val probe_mc_needs_ndvd =
  let
    val bogus = Logic.mk_implies (jT (prime2 pVmc),
                  Logic.mk_implies (jT (cong pVmc (mult aVmc bVmc) (mult aVmc cVmc)),
                    jT (cong pVmc bVmc cVmc)));   (* drops ~(p|a) *)
  in not ((Thm.prop_of mod_cancel) aconv bogus) end;
val probe_mc_nontrivial =
  not ((Thm.prop_of mod_cancel) aconv (jT (cong pVmc bVmc cVmc)));

val () =
  if r_mc andalso probe_mc_needs_ndvd andalso probe_mc_nontrivial
  then out "PROBE_OK mod_cancel is conditional on ~(p|a) / nontrivial\n"
  else out "PROBE_UNSOUND mod_cancel collapsed!\n";

val () =
  if r_mc andalso probe_mc_needs_ndvd andalso probe_mc_nontrivial
  then out "MOD_CANCEL_OK\n"
  else out "MOD_CANCEL_FAILED\n";
(* ============================================================================
   LAGRANGE'S THEOREM ON SQUARE ROOTS OF UNITY mod p
     lagrange_roots : prime2 p ==> cong p (mult a a) 1
                        ==> Disj (cong p a 1) (cong p (Suc a) 0)
   x^2 == 1 (mod p) ==> x == 1 OR x == -1   (-1 expressed as Suc a == 0).
   Strategy: num-cases on a.
     a = 0   : cong p 0 1 forces p|1, contradicting prime (1<p).
     a = Suc a0 : (a0+1)^2 = a0*(a+1) + 1 ; cong cancels +1 to p | a0*(Suc a);
                  euclid_lemma -> p|a0 (=> a == 1) or p|(Suc a) (=> Suc a == 0).
   Routed through ctxtS2 / ctermS2 (the final base context).
   ============================================================================ *)
val () = out "LAGRANGE_ROOTS_BEGIN\n";

(* ---- extra instantiators on ctxtS2 ---- *)
val Suc_inj_vS2          = varify Suc_inj_ax;            (* oeq (Suc ?a)(Suc ?b) ==> oeq ?a ?b *)
fun Suc_inj_atS (ut, vt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 ut), (("b",0), ctermS2 vt)] Suc_inj_vS2)) h;
val add_eq_zero_left_vS  = varify add_eq_zero_left;      (* oeq (add ?a ?b) Zero ==> oeq ?a Zero *)
fun add_eq_zero_left_atS (at, bt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 at), (("b",0), ctermS2 bt)] add_eq_zero_left_vS)) h;

(* mult left-zero on ctxtS2 : oeq (mult 0 n) 0 *)
val mult_0_vS2 = varify mult_0;
fun mult0lS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_vS2);

(* euclid_lemma on ctxtS2 : prime2 p -> dvd p (mult a b) -> Disj (dvd p a)(dvd p b) *)
val euclid_lemma_vS2 = varify euclid_lemma;
fun euclid_atS (pt, at, bt) hPrime hDvd =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("p",0), ctermS2 pt), (("a",0), ctermS2 at), (("b",0), ctermS2 bt)] euclid_lemma_vS2);
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hDvd end;

(* prime_not_dvd_pos_lt on ctxtS2 : dvd p r -> lt 0 r -> lt r p -> oFalse *)
val prime_not_dvd_pos_lt_vS2 = varify prime_not_dvd_pos_lt;
fun prime_not_dvd_pos_lt_atS (pt, rt) hDvd hPos hLt =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("p",0), ctermS2 pt), (("r",0), ctermS2 rt)] prime_not_dvd_pos_lt_vS2);
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hDvd) hPos) hLt end;

val () = out "LR_HELPERS_READY\n";

val lagrange_roots =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val hPrimeP = jT (prime2 pF);
    val hPrime  = Thm.assume (ctermS2 hPrimeP);
    val hCongP  = jT (cong pF (mult aF aF) oneC);
    val hCong   = Thm.assume (ctermS2 hCongP);

    (* the final goal disjunction *)
    val goalC = mkDisj (cong pF aF oneC) (cong pF (suc aF) ZeroC);

    (* num-cases on a : Disj (oeq a 0) (Ex q. oeq a (Suc q)) *)
    val dz = dzosS_at aF;

    (* ===================== CASE a = 0 ===================== *)
    val caseZero =
      let
        val ha0 = Thm.assume (ctermS2 (jT (oeq aF ZeroC)));    (* a = 0 *)
        (* From hCong : Disj (congL p (a*a) 1)(congR p (a*a) 1).  We derive oFalse,
           then oFalse_elim into goalC.  Both disjuncts of cong are contradictory.
           congL : Ex k. 1 = (a*a) + p*k  -> p|1 -> prime contra
           congR : Ex k. (a*a) = 1 + p*k  -> rewrite a*a -> 0 (since a=0); but
                   0 = 1 + p*k = Suc(p*k) -> Suc_neq_Zero contra.  *)
        val aa_0a = mult_cong_lS (aF, ZeroC, aF) ha0;          (* a*a = 0*a *)
        val z0a   = mult0lS_at aF;                             (* 0*a = 0 *)
        val aa0   = oeq_trans OF [aa_0a, z0a];                 (* a*a = 0 *)

        val LcongL = congL pF (mult aF aF) oneC;
        val LcongR = congR pF (mult aF aF) oneC;

        (* congL case : Ex k. oeq 1 (add (a*a) (mult p k)) *)
        val caseL =
          let
            val PabsL = Abs("k", natT, oeq oneC (add (mult aF aF) (mult pF (Bound 0))));
            fun bodyL kW (hk : thm) =                          (* hk : 1 = (a*a) + p*k *)
              let
                (* rewrite a*a -> 0 : (a*a) + p*k = 0 + p*k = p*k *)
                val r1 = add_cong_lS (mult aF aF, ZeroC, mult pF kW) aa0;  (* (a*a + p*k) = (0 + p*k) *)
                val r2 = add0S_at (mult pF kW);                (* (0 + p*k) = p*k *)
                val one_pk = oeq_trans OF [oeq_trans OF [hk, r1], r2];  (* 1 = p*k *)
                (* dvd p 1 : oeq 1 (mult p k) is exactly one_pk *)
                val dvdp1 = dvd_introS (pF, oneC, kW) one_pk;  (* dvd p 1 *)
                (* lt 0 1 = le (Suc 0) 1 = le 1 1 ; witness 0 : oeq 1 (add 1 0) *)
                val lt01 =
                  let val h = oeq_sym OF [add0rS_at oneC]       (* oeq 1 (add 1 0) *)
                  in le_introS (oneC, oneC, ZeroC) h end;       (* le 1 1 = lt 0 1 *)
                val lt1p  = prime2_gt1_atS pF hPrime;           (* lt 1 p *)
                val fls   = prime_not_dvd_pos_lt_atS (pF, oneC) dvdp1 lt01 lt1p;  (* oFalse *)
              in Thm.implies_elim (oFalse_elimS_at goalC) fls end;  (* goalC *)
            val resL = exE_elimS2 (PabsL, goalC) (Thm.assume (ctermS2 (jT LcongL))) "kL_lr" bodyL;
          in Thm.implies_intr (ctermS2 (jT LcongL)) resL end;

        (* congR case : Ex k. oeq (a*a) (add 1 (mult p k)) *)
        val caseR =
          let
            val PabsR = Abs("k", natT, oeq (mult aF aF) (add oneC (mult pF (Bound 0))));
            fun bodyR kW (hk : thm) =                          (* hk : (a*a) = 1 + p*k *)
              let
                (* a*a = 0 (aa0) and a*a = 1 + p*k -> 0 = 1 + p*k *)
                val z_1pk = oeq_trans OF [oeq_sym OF [aa0], hk];   (* 0 = 1 + p*k *)
                (* 1 + p*k = Suc 0 + p*k = Suc(0 + p*k) = Suc(p*k) *)
                val s1 = addSucS_at (ZeroC, mult pF kW);       (* (Suc 0 + p*k) = Suc(0 + p*k) *)
                val s2 = Suc_cong OF [add0S_at (mult pF kW)];  (* Suc(0 + p*k) = Suc(p*k) *)
                val onepk_suc = oeq_trans OF [s1, s2];         (* (1 + p*k) = Suc(p*k) *)
                val z_suc = oeq_trans OF [z_1pk, onepk_suc];   (* 0 = Suc(p*k) *)
                val suc_z = oeq_sym OF [z_suc];                (* Suc(p*k) = 0 *)
                val fls   = (Suc_neq_Zero_atS (mult pF kW)) OF [suc_z];  (* oFalse *)
              in Thm.implies_elim (oFalse_elimS_at goalC) fls end;
            val resR = exE_elimS2 (PabsR, goalC) (Thm.assume (ctermS2 (jT LcongR))) "kR_lr" bodyR;
          in Thm.implies_intr (ctermS2 (jT LcongR)) resR end;

        val res = disjE_elimS2 (LcongL, LcongR, goalC) hCong caseL caseR;
      in Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC))) res end;

    (* ===================== CASE a = Suc a0 ===================== *)
    val PabsSuc = Abs("q", natT, oeq aF (suc (Bound 0)));
    fun caseSucBody a0 (ha : thm) =                            (* ha : a = Suc a0 *)
      let
        val M  = mult a0 aF;                                   (* a0 * a *)
        val T  = add a0 M;                                     (* a0 + a0*a *)
        val xT = mult a0 (suc aF);                             (* a0 * (Suc a) = the witness x *)

        (* ---- key identity : oeq (mult a a) (add xT 1) ---- *)
        (* LHS chain : mult a a -> Suc T *)
        val L1 = mult_cong_lS (aF, suc a0, aF) ha;             (* a*a = (Suc a0)*a *)
        val L2 = mult_Suc_atS (a0, aF);                        (* (Suc a0)*a = add a (a0*a) *)
        val L3 = add_cong_lS (aF, suc a0, M) ha;               (* (a + a0*a) = (Suc a0 + a0*a) *)
        val L4 = addSucS_at (a0, M);                           (* (Suc a0 + a0*a) = Suc(a0 + a0*a) = Suc T *)
        val LHS = oeq_trans OF [oeq_trans OF [oeq_trans OF [L1, L2], L3], L4];  (* a*a = Suc T *)
        (* RHS chain : add xT 1 -> Suc T *)
        val R0 = multSrS_at (a0, aF);                          (* a0*(Suc a) = add a0 (a0*a) = T *)
        val R1 = add_cong_lS (xT, T, oneC) R0;                 (* (xT + 1) = (T + 1) *)
        val R2 = addSrS_at (T, ZeroC);                         (* (T + Suc 0) = Suc(T + 0) *)
        val R3 = Suc_cong OF [add0rS_at T];                    (* Suc(T + 0) = Suc T *)
        val RHS = oeq_trans OF [oeq_trans OF [R1, R2], R3];    (* (xT + 1) = Suc T *)
        val idEq = oeq_trans OF [LHS, oeq_sym OF [RHS]];       (* a*a = add xT 1 *)

        (* ---- derive  dvd p xT  from hCong + idEq ---- *)
        val LcongL = congL pF (mult aF aF) oneC;
        val LcongR = congR pF (mult aF aF) oneC;

        (* congL : Ex k. oeq 1 (add (a*a) (mult p k))  ->  rewrite a*a->xT+1 ->
           1 = (xT+1)+p*k = Suc(xT+p*k) -> Suc_inj -> 0 = xT+p*k -> xT=0 -> dvd p 0 -> dvd p xT *)
        val dvdL =
          let
            val PabsL = Abs("k", natT, oeq oneC (add (mult aF aF) (mult pF (Bound 0))));
            fun bodyL kW (hk : thm) =                          (* hk : 1 = (a*a) + p*k *)
              let
                (* rewrite a*a -> xT+1 in (a*a)+p*k *)
                val rw  = add_cong_lS (mult aF aF, add xT oneC, mult pF kW) idEq;  (* ((a*a)+p*k) = ((xT+1)+p*k) *)
                val one_eq = oeq_trans OF [hk, rw];            (* 1 = (xT+1)+p*k *)
                (* (xT+1)+p*k = Suc(xT) + p*k = Suc(xT + p*k) *)
                val e1 = add_cong_lS (add xT oneC, suc xT, mult pF kW)
                           (let val a1 = addSrS_at (xT, ZeroC)        (* (xT + Suc 0) = Suc(xT+0) *)
                                val a2 = Suc_cong OF [add0rS_at xT]    (* Suc(xT+0) = Suc xT *)
                            in oeq_trans OF [a1, a2] end);     (* (xT+1) = Suc xT *)
                                                               (* ((xT+1)+p*k) = (Suc xT + p*k) *)
                val e2 = addSucS_at (xT, mult pF kW);          (* (Suc xT + p*k) = Suc(xT + p*k) *)
                val one_suc = oeq_trans OF [oeq_trans OF [one_eq, e1], e2];  (* 1 = Suc(xT+p*k) *)
                (* 1 = Suc 0, so Suc 0 = Suc(xT+p*k) -> Suc_inj -> 0 = xT+p*k *)
                val suc_eq = one_suc;                          (* oeq (Suc 0) (Suc (xT+p*k)) *)
                val zero_eq = Suc_inj_atS (ZeroC, add xT (mult pF kW)) suc_eq;  (* 0 = xT+p*k *)
                val sum_zero = oeq_sym OF [zero_eq];           (* (xT+p*k) = 0 *)
                val xT_zero = add_eq_zero_left_atS (xT, mult pF kW) sum_zero;   (* xT = 0 *)
                (* dvd p 0, then rewrite 0->xT : dvd p xT.  dvd_cong_rS needs oeq 0 xT. *)
                val dvdp0 = dvd_zeroS_at pF;                   (* dvd p 0 *)
                val zero_xT = oeq_sym OF [xT_zero];            (* 0 = xT *)
                val dvdpxT = dvd_cong_rS (pF, ZeroC, xT) zero_xT dvdp0;  (* dvd p xT *)
              in dvdpxT end;
            val r = exE_elimS2 (PabsL, dvd pF xT) (Thm.assume (ctermS2 (jT LcongL))) "kL2_lr" bodyL;
          in Thm.implies_intr (ctermS2 (jT LcongL)) r end;

        (* congR : Ex k. oeq (a*a) (add 1 (mult p k)) -> rewrite a*a->xT+1 ->
           (xT+1) = 1 + p*k = Suc(p*k); also xT+1 = Suc xT -> Suc xT = Suc(p*k) -> xT = p*k -> dvd p xT *)
        val dvdR =
          let
            val PabsR = Abs("k", natT, oeq (mult aF aF) (add oneC (mult pF (Bound 0))));
            fun bodyR kW (hk : thm) =                          (* hk : (a*a) = 1 + p*k *)
              let
                val lhs_eq = oeq_trans OF [oeq_sym OF [idEq], hk];   (* (xT+1) = 1 + p*k *)
                (* xT+1 = Suc xT *)
                val xT1_suc = let val a1 = addSrS_at (xT, ZeroC)
                                  val a2 = Suc_cong OF [add0rS_at xT]
                              in oeq_trans OF [a1, a2] end;     (* (xT+1) = Suc xT *)
                (* 1 + p*k = Suc 0 + p*k = Suc(0+p*k) = Suc(p*k) *)
                val rhs_suc = let val b1 = addSucS_at (ZeroC, mult pF kW)
                                  val b2 = Suc_cong OF [add0S_at (mult pF kW)]
                              in oeq_trans OF [b1, b2] end;     (* (1 + p*k) = Suc(p*k) *)
                (* Suc xT = (xT+1) = (1+p*k) = Suc(p*k) *)
                val suc_eq = oeq_trans OF [oeq_trans OF [oeq_sym OF [xT1_suc], lhs_eq], rhs_suc];  (* Suc xT = Suc(p*k) *)
                val xT_pk = Suc_inj_atS (xT, mult pF kW) suc_eq;  (* xT = p*k *)
                val dvdpxT = dvd_introS (pF, xT, kW) xT_pk;     (* dvd p xT *)
              in dvdpxT end;
            val r = exE_elimS2 (PabsR, dvd pF xT) (Thm.assume (ctermS2 (jT LcongR))) "kR2_lr" bodyR;
          in Thm.implies_intr (ctermS2 (jT LcongR)) r end;

        val dvdpxT = disjE_elimS2 (LcongL, LcongR, dvd pF xT) hCong dvdL dvdR;  (* dvd p xT *)

        (* ---- euclid_lemma : dvd p (mult a0 (Suc a)) -> Disj (dvd p a0)(dvd p (Suc a)) ---- *)
        val euDisj = euclid_atS (pF, a0, suc aF) hPrime dvdpxT;   (* Disj (dvd p a0)(dvd p (Suc a)) *)

        (* CASE p|a0 : a0 = p*j -> a = Suc a0 = Suc(p*j) = 1 + p*j -> cong p a 1 (congR) -> disjI1 goalC *)
        val caseDA0 =
          let
            val hda0 = Thm.assume (ctermS2 (jT (dvd pF a0)));    (* dvd p a0 = Ex k. a0 = p*k *)
            val Pdvd = Abs("k", natT, oeq a0 (mult pF (Bound 0)));
            fun body jW (hj : thm) =                             (* hj : a0 = p*j *)
              let
                (* a = Suc a0 = Suc(p*j) ; 1 + p*j = Suc(p*j) ; so a = 1 + p*j *)
                val a_suc_pj = oeq_trans OF [ha, Suc_cong OF [hj]];  (* a = Suc(p*j) *)
                val onepj_suc = let val b1 = addSucS_at (ZeroC, mult pF jW)
                                    val b2 = Suc_cong OF [add0S_at (mult pF jW)]
                                in oeq_trans OF [b1, b2] end;    (* (1 + p*j) = Suc(p*j) *)
                val a_eq = oeq_trans OF [a_suc_pj, oeq_sym OF [onepj_suc]];  (* a = (1 + p*j) *)
                (* congR p a 1 : Ex k. oeq a (add 1 (mult p k)), witness j *)
                val congRabs = Abs("k", natT, oeq aF (add oneC (mult pF (Bound 0))));
                val exC = exI_atS2 congRabs jW a_eq;             (* congR p a 1 *)
                val hcong = disjI2S2_at (congL pF aF oneC, congR pF aF oneC) exC;  (* cong p a 1 *)
              in disjI1S2_at (cong pF aF oneC, cong pF (suc aF) ZeroC) hcong end;  (* goalC *)
            val r = exE_elimS2 (Pdvd, goalC) hda0 "j0_lr" body;
          in Thm.implies_intr (ctermS2 (jT (dvd pF a0))) r end;

        (* CASE p|(Suc a) : Suc a = p*j -> cong p (Suc a) 0 (congR, b:=0) -> disjI2 goalC *)
        val caseDSa =
          let
            val hdSa = Thm.assume (ctermS2 (jT (dvd pF (suc aF))));  (* dvd p (Suc a) = Ex k. Suc a = p*k *)
            val Pdvd = Abs("k", natT, oeq (suc aF) (mult pF (Bound 0)));
            fun body jW (hj : thm) =                             (* hj : Suc a = p*j *)
              let
                (* Suc a = p*j ; 0 + p*j = p*j ; so Suc a = 0 + p*j *)
                val z_pj = oeq_sym OF [add0S_at (mult pF jW)];   (* p*j = 0 + p*j *)
                val Sa_eq = oeq_trans OF [hj, z_pj];             (* Suc a = 0 + p*j *)
                (* congR p (Suc a) 0 : Ex k. oeq (Suc a) (add 0 (mult p k)), witness j *)
                val congRabs = Abs("k", natT, oeq (suc aF) (add ZeroC (mult pF (Bound 0))));
                val exC = exI_atS2 congRabs jW Sa_eq;            (* congR p (Suc a) 0 *)
                val hcong = disjI2S2_at (congL pF (suc aF) ZeroC, congR pF (suc aF) ZeroC) exC;  (* cong p (Suc a) 0 *)
              in disjI2S2_at (cong pF aF oneC, cong pF (suc aF) ZeroC) hcong end;  (* goalC *)
            val r = exE_elimS2 (Pdvd, goalC) hdSa "jS_lr" body;
          in Thm.implies_intr (ctermS2 (jT (dvd pF (suc aF)))) r end;

        val res = disjE_elimS2 (dvd pF a0, dvd pF (suc aF), goalC) euDisj caseDA0 caseDSa;
      in res end;
    val caseSuc =
      let
        val r = exE_elimS2 (PabsSuc, goalC) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "a0_lr" caseSucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) r end;

    val concl = disjE_elimS2 (oeq aF ZeroC, mkEx PabsSuc, goalC) dz caseZero caseSuc;  (* goalC *)
    val disch1 = Thm.implies_intr (ctermS2 hCongP) concl;
    val disch2 = Thm.implies_intr (ctermS2 hPrimeP) disch1;
  in varify disch2 end;

val () = out "LAGRANGE_ROOTS_PROVED\n";

(* ---- validation ---- *)
val pVlr = Var (("p",0), natT);
val aVlr = Var (("a",0), natT);
val lagrange_roots_intended =
  Logic.mk_implies (jT (prime2 pVlr),
    Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
      jT (mkDisj (cong pVlr aVlr oneC) (cong pVlr (suc aVlr) ZeroC))));
val r_lr = checkS2 ("lagrange_roots", lagrange_roots, lagrange_roots_intended);
val () = if r_lr then out "OK lagrange_roots\n" else out "FAIL lagrange_roots\n";

(* ---- soundness probes ---- *)
(* (1) dropping prime2 p must NOT be provable (kernel must still need it) *)
val probe_drop_prime =
  let val bogus = Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
                    jT (mkDisj (cong pVlr aVlr oneC) (cong pVlr (suc aVlr) ZeroC)))
  in not ((Thm.prop_of lagrange_roots) aconv bogus) end;
(* (2) dropping one disjunct (keeping only x==1) must NOT match *)
val probe_drop_disj =
  let val bogus = Logic.mk_implies (jT (prime2 pVlr),
                    Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
                      jT (cong pVlr aVlr oneC)))
  in not ((Thm.prop_of lagrange_roots) aconv bogus) end;

val () =
  if probe_drop_prime andalso probe_drop_disj
  then out "PROBE_OK lagrange_roots conditional on prime / two-sided\n"
  else out "PROBE_UNSOUND lagrange_roots collapsed!\n";

val () =
  if r_lr andalso probe_drop_prime andalso probe_drop_disj
  then out "LAGRANGE_ROOTS_OK\n"
  else out "LAGRANGE_ROOTS_FAILED\n";

