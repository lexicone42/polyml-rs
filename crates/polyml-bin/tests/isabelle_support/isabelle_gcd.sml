(* ============================================================================
   THE EUCLIDEAN ALGORITHM: gcd universal property, BEZOUT'S IDENTITY, and the
   MODULAR INVERSE, in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_gcd.rs)
   ----------------------------------------------------------------------------
   Closes the gap the rest of the tower deliberately sidestepped ("gcd/Bezout
   needs integers over N"): all four results are proved as PURE EXISTENTIALS
   over the existing theory (NO new constant, NO new axiom), by genuine LCF
   kernel inference. The key tool is the already-proved DIVISION THEOREM
   (div_mod_exists) driving a strong induction (strong_induct):

     gcd_props      : |- !a b. ?g. g dvd a /\ g dvd b /\
                                   (!d. d dvd a ==> d dvd b ==> d dvd g)
                      "every pair has a common divisor that every common
                       divisor divides" -- the gcd VALUE + its universal property.
     bezout         : |- !a b. ?g. (g the gcd, as above) /\
                                   (?x y. a*x = b*y + g \/ b*y = a*x + g)
                      Bezout's identity in the two-sided natural-number form
                      (N has no subtraction, so one of the two equations holds).
     coprime_bezout : |- (!d. d dvd a ==> d dvd b ==> d = 1) ==>
                         ?x y. a*x = b*y + 1 \/ b*y = a*x + 1
     mod_inverse    : |- prime p ==> ~(p dvd a) ==> ?b. cong p (a*b) 1

   Built on the unified number-theory base (isabelle_ntbase.sml, spliced in by
   common::with_ntbase): classical foundation + division theorem + Euclid +
   Euclid's lemma + modular arithmetic + powers. Each lemma carries a soundness
   probe (the kernel rejects the degenerate/weakened variant).

   Proved by a 3-phase ultracode fleet (wf_a420c57e-d18): gcd-props -> bezout
   -> coprime/inverse, each phase a parallel multi-seat race, the winner of each
   feeding the next. Re-verified end-to-end by hand before landing.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 : the gcd universal property (seat gcdprops0)
   ----------------------------------------------------------------------------
   Prove (object-quantified, meta-quantified over a,b):
     !!a b. jT (Ex g. Conj (dvd g a)
                         (Conj (dvd g b)
                            (Forall (%d. Imp (Conj (dvd d a) (dvd d b)) (dvd d g)))))
   "every pair (a,b) has a common divisor g that every common divisor divides."

   Strategy : strong induction on b (second arg).  Predicate
     G n := Forall (%a. body(a, n))
   with the inner first gcd-argument a OBJECT-universally quantified, so the IH
   at r < b can be re-instantiated at a' := b for the recursive call (b, r).

   Everything routes through ctxtS2 / ctermS2 (where strong_induct, div_mod_exists,
   dvd_add, dvd_mult_right, dvd_diff, dvd_cong_rS etc. all live).
   ============================================================================ *)
val () = out "GCDPROPS_BEGIN\n";

(* lift the dependency lemmas we still need onto ctxtS2 (schematic) *)
val dvd_diff_vS = varify dvd_diff;   (* jT (dvd ?p ?x) ==> jT (dvd ?p (add ?x ?y)) ==> jT (dvd ?p ?y) *)
fun dvd_diff_atS (pT, xT, yT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("x",0), ctermS2 xT), (("y",0), ctermS2 yT)] dvd_diff_vS)
  in (inst OF [h1]) OF [h2] end;

(* ---- the gcd "body" and "greatest" abstractions, capture-avoiding ----
   greatest(aT,nT,gT) = Forall (%d. Imp (Conj (dvd d aT) (dvd d nT)) (dvd d gT))
   body(aT,nT)        = Ex (%g. Conj (dvd g aT) (Conj (dvd g nT) (greatest(aT,nT,g)))) *)

fun greatestAbs (aT, nT, gT) =                       (* %d. Imp (Conj (dvd d a)(dvd d n)) (dvd d g) *)
  let val dF = Free("d_gr", natT)
  in Term.lambda dF (mkImp (mkConj (dvd dF aT) (dvd dF nT)) (dvd dF gT)) end;
fun greatest (aT, nT, gT) = mkForall (greatestAbs (aT, nT, gT));

fun gcdBodyG (aT, nT, gT) =                           (* Conj (dvd g a)(Conj (dvd g n)(greatest)) *)
  mkConj (dvd gT aT) (mkConj (dvd gT nT) (greatest (aT, nT, gT)));

fun bodyAbs (aT, nT) =                                (* %g. Conj (dvd g a)(Conj (dvd g n)(greatest a n g)) *)
  let val gF = Free("g_bd", natT)
  in Term.lambda gF (gcdBodyG (aT, nT, gF)) end;
fun bodyEx (aT, nT) = mkEx (bodyAbs (aT, nT));        (* Ex g. ... *)

(* G n = Forall (%a. bodyEx(a, n)) -- the strong_induct predicate value *)
fun GallAbs nT =                                      (* %a. bodyEx(a, n) *)
  let val aF = Free("a_G", natT)
  in Term.lambda aF (bodyEx (aF, nT)) end;
fun Gprop_of nT = mkForall (GallAbs nT);

(* The (nat=>o) predicate for strong_induct : %n. G n *)
val GpredSI =
  let val nF = Free("n_GP", natT) in Term.lambda nF (Gprop_of nF) end;

val () = out "GCD_HELPERS_READY\n";

(* ============================================================================
   SMALL helper lemmas (explicit route, as the seat hint requests)
   ----------------------------------------------------------------------------
   h_dvd_mult_q : jT (dvd d b) ==> jT (dvd d (mult b q))      [= dvd_mult_right]
   h_dvd_sum    : jT (dvd g (mult b q)) ==> jT (dvd g r)
                    ==> jT (dvd g (add (mult b q) r))          [= dvd_add]
   Both already exist as dvd_mult_right_atS / dvd_add_atS; we use them directly.
   ============================================================================ *)

(* ============================================================================
   THE STRONG INDUCTION
   ============================================================================ *)
val gcd_props =
  let
    (* ---- strong-induction step : fix nStep (the current b), assume strong IH,
            prove jT (G nStep) = jT (Forall (%a. bodyEx(a, nStep))) ---- *)
    val nStep = Free("n_gc", natT);
    val mIH   = Free("m_gc", natT);
    (* G m as a bare proposition (no Trueprop) for the Logic.all *)
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (Gprop_of mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);              (* the strong IH : !!m. lt m n ==> jT (G m) *)
    fun applyIH mt h_lt =                                (* lt m n -> jT (G m) = jT (Forall(%a. bodyEx(a,m))) *)
      let val hAt = Thm.forall_elim (ctermS2 mt) Hthm
      in Thm.implies_elim hAt h_lt end;

    (* prove jT (Forall (%a. bodyEx(a, nStep))) by allI : fix aF, prove jT (bodyEx(aF, nStep)) *)
    val aF = Free("a_gc", natT);
    val goalBody = bodyEx (aF, nStep);                   (* Ex g. ... for THIS a, THIS n *)

    (* case split on nStep = 0 vs nStep = Suc q *)
    val dz = dzosS_at nStep;                             (* Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)

    (* ----------------------------------------------------------------
       CASE n = 0 : take g := a.
         dvd a a    (dvd_refl)
         dvd a n    (dvd_zero a -> dvd a 0, then cong 0->n via oeq 0 n)
         greatest   (given Conj(dvd d a)(dvd d n), conjunct1 = dvd d a = dvd d g)
       ---------------------------------------------------------------- *)
    val caseZero =
      let
        val hZ = Thm.assume (ctermS2 (jT (oeq nStep ZeroC)));   (* oeq n 0 *)
        (* dvd a a *)
        val dvd_a_a = dvd_refl_atS2 aF;                          (* dvd a a *)
        (* dvd a n : dvd a 0 then rewrite 0 -> n *)
        val dvd_a_0 = dvd_zeroS_at aF;                          (* dvd a 0 *)
        val hZsym   = oeq_sym OF [hZ];                          (* oeq 0 n *)
        val dvd_a_n = dvd_cong_rS (aF, ZeroC, nStep) hZsym dvd_a_0;   (* dvd a n *)
        (* greatest a n a : Forall(%d. Imp(Conj(dvd d a)(dvd d n))(dvd d a)) *)
        val greatBody =
          let
            val dF   = Free("d_cz", natT);
            val hC   = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));  (* Conj(dvd d a)(dvd d n) *)
            val c1   = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hC;                     (* dvd d a = dvd d g *)
            (* META impl jT(Conj..) ==> jT(dvd d a), then OBJECT Imp via impI *)
            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) c1;
            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF aF) metaImp;  (* jT (Imp(Conj..)(dvd d a)) *)
          in (dF, objImp) end;
        val (dFz, impdz) = greatBody;
        (* allI : fix d, jT (Imp(Conj ..)(dvd d a)) -> jT (Forall (greatestAbs a n a)) *)
        val minor = Thm.forall_intr (ctermS2 dFz) impdz;        (* !!d. jT (Imp ...) *)
        val great = allI_atS2 (greatestAbs (aF, nStep, aF)) minor;  (* jT (greatest a n a) *)
        (* assemble Conj (dvd a a)(Conj (dvd a n)(greatest)) *)
        val innerConj = conjI_atS2 (dvd aF nStep, greatest (aF, nStep, aF)) dvd_a_n great;
        val fullConj  = conjI_atS2 (dvd aF aF, mkConj (dvd aF nStep) (greatest (aF, nStep, aF))) dvd_a_a innerConj;
        (* exI : witness g := a *)
        val exG = exI_atS2 (bodyAbs (aF, nStep)) aF fullConj;   (* Ex g. ... = goalBody *)
      in Thm.implies_intr (ctermS2 (jT (oeq nStep ZeroC))) exG end;

    (* ----------------------------------------------------------------
       CASE n = Suc q : descent.
       ---------------------------------------------------------------- *)
    val caseSuc =
      let
        val PabsSuc = Abs("q", natT, oeq nStep (suc (Bound 0)));   (* body of (Ex q. oeq n (Suc q)) *)
        fun sucBody qWit (hSucEq : thm) =                          (* hSucEq : oeq n (Suc q) *)
          let
            (* lt 0 n : lt 0 (Suc q) then rewrite (Suc q) -> n *)
            val lt0Sq = lt_zero_suc_atS qWit;                      (* lt 0 (Suc q) *)
            val sucEqSym = oeq_sym OF [hSucEq];                    (* oeq (Suc q) n *)
            val ltPosPabs = Term.lambda (Free("z_lp", natT)) (lt ZeroC (Free("z_lp", natT)));
            val lt0n = oeq_rewrite_atS (ltPosPabs, suc qWit, nStep) sucEqSym lt0Sq;  (* lt 0 n *)
            (* div_mod a / n : Ex q'. Ex r. Conj (oeq a (add (mult n q') r)) (lt r n) *)
            val dmEx = div_mod_atS (aF, nStep) lt0n;
            (* exE q', exE r *)
            fun qBody qDiv (hQex : thm) =                          (* hQex : Ex r. Conj (oeq a (add (mult n q') r))(lt r n) *)
              let
                fun rBody rDiv (hConj : thm) =                     (* hConj : Conj (oeq a (add (mult n q') r))(lt r n) *)
                  let
                    val eqDivP = oeq aF (add (mult nStep qDiv) rDiv);   (* a = n*q' + r *)
                    val ltRnP  = lt rDiv nStep;                        (* r < n *)
                    val hEqDiv = conjunct1_atS2 (eqDivP, ltRnP) hConj;  (* oeq a (add (mult n q') r) *)
                    val hLtRn  = conjunct2_atS2 (eqDivP, ltRnP) hConj;  (* lt r n *)

                    (* apply IH at r (legal : lt r n) : jT (Forall (%a'. bodyEx(a', r))) *)
                    val Gr     = applyIH rDiv hLtRn;                   (* jT (Forall (%a'. bodyEx(a', r))) *)
                    (* instantiate the inner object-a at a' := n (the recursive first arg) *)
                    val GrAtN  = allE_atS2 (GallAbs rDiv) nStep Gr;    (* jT (bodyEx(n, r)) = Ex g. Conj(dvd g n)(Conj(dvd g r)(greatest n r g)) *)

                    (* exE the gcd witness g of (n, r) *)
                    fun gBody gWit (hG : thm) =                       (* hG : Conj(dvd g n)(Conj(dvd g r)(greatest n r g)) *)
                      let
                        val gNd  = dvd gWit nStep;
                        val gRd  = dvd gWit rDiv;
                        val grGt = greatest (nStep, rDiv, gWit);
                        val h_g_n   = conjunct1_atS2 (gNd, mkConj gRd grGt) hG;          (* dvd g n *)
                        val h_rest  = conjunct2_atS2 (gNd, mkConj gRd grGt) hG;          (* Conj(dvd g r)(greatest n r g) *)
                        val h_g_r   = conjunct1_atS2 (gRd, grGt) h_rest;                 (* dvd g r *)
                        val h_great = conjunct2_atS2 (gRd, grGt) h_rest;                 (* greatest n r g *)

                        (* ---- (1) g divides a ----
                           dvd g n -> dvd g (n*q')   [dvd_mult_right]
                           dvd g (n*q') -> dvd g (n*q'+r)  with dvd g r  [dvd_add]
                           rewrite (n*q'+r) -> a  via oeq (n*q'+r) a   [dvd_cong_r] *)
                        val g_nq    = dvd_mult_right_atS (gWit, nStep, qDiv) h_g_n;      (* dvd g (n*q') *)
                        val g_sum   = dvd_add_atS (gWit, mult nStep qDiv, rDiv) g_nq h_g_r;  (* dvd g (n*q'+r) *)
                        val eqSym   = oeq_sym OF [hEqDiv];                               (* oeq (n*q'+r) a *)
                        val g_a     = dvd_cong_rS (gWit, add (mult nStep qDiv) rDiv, aF) eqSym g_sum;  (* dvd g a *)

                        (* ---- (2) greatest for (a, n) ----
                           given Conj(dvd d a)(dvd d n), show dvd d g :
                             dvd d n -> dvd d (n*q')        [dvd_mult_right]
                             dvd d a, a = n*q'+r => dvd d (n*q'+r)  [cong on dvd d a]
                             dvd_diff (d, n*q', r) (dvd d (n*q')) (dvd d (n*q'+r)) => dvd d r
                             great (n,r,g) at d : Imp(Conj(dvd d n)(dvd d r))(dvd d g) -> dvd d g *)
                        val greatAN =
                          let
                            val dF = Free("d_an", natT);
                            val hCd = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));  (* Conj(dvd d a)(dvd d n) *)
                            val d_a = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d a *)
                            val d_n = conjunct2_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d n *)
                            val d_nq = dvd_mult_right_atS (dF, nStep, qDiv) d_n;          (* dvd d (n*q') *)
                            (* dvd d a -> dvd d (n*q'+r) via cong a -> (n*q'+r) *)
                            val d_sum = dvd_cong_rS (dF, aF, add (mult nStep qDiv) rDiv) hEqDiv d_a;  (* dvd d (n*q'+r) *)
                            val d_r   = dvd_diff_atS (dF, mult nStep qDiv, rDiv) d_nq d_sum;          (* dvd d r *)
                            (* apply greatest(n,r,g) at d : need Conj(dvd d n)(dvd d r) -> dvd d g *)
                            val hImp  = allE_atS2 (greatestAbs (nStep, rDiv, gWit)) dF h_great;       (* Imp(Conj(dvd d n)(dvd d r))(dvd d g) *)
                            val cnj   = conjI_atS2 (dvd dF nStep, dvd dF rDiv) d_n d_r;               (* Conj(dvd d n)(dvd d r) *)
                            val d_g   = mp_atS2 (mkConj (dvd dF nStep) (dvd dF rDiv), dvd dF gWit) hImp cnj;  (* dvd d g *)
                            (* META impl jT(Conj(dvd d a)(dvd d n)) ==> jT(dvd d g), then OBJECT Imp *)
                            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) d_g;
                            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF gWit) metaImp;  (* jT (Imp(Conj..)(dvd d g)) *)
                            val minor   = Thm.forall_intr (ctermS2 dF) objImp;
                          in allI_atS2 (greatestAbs (aF, nStep, gWit)) minor end;        (* jT (greatest a n g) *)

                        (* assemble Conj (dvd g a)(Conj (dvd g n)(greatest a n g)) *)
                        val innerC = conjI_atS2 (dvd gWit nStep, greatest (aF, nStep, gWit)) h_g_n greatAN;
                        val fullC  = conjI_atS2 (dvd gWit aF, mkConj (dvd gWit nStep) (greatest (aF, nStep, gWit))) g_a innerC;
                        val exG    = exI_atS2 (bodyAbs (aF, nStep)) gWit fullC;          (* goalBody *)
                      in exG end;
                    val g = exE_elimS2 (bodyAbs (nStep, rDiv), goalBody) GrAtN "g_w" gBody;
                  in g end;
                val g = exE_elimS2 (innerDivAbsN nStep aF qDiv, goalBody) hQex "r_w" rBody;
              in g end;
            val g = exE_elimS2 (rmDivBodyN nStep aF, goalBody) dmEx "q_w" qBody;
          in g end;
        val gg = exE_elimS2 (PabsSuc, goalBody) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "q_sw" sucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) gg end;

    (* combine the two cases via dz : Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)
    val bodyProof = disjE_elimS2 (oeq nStep ZeroC, mkExSuc nStep, goalBody) dz caseZero caseSuc;
    (* turn jT (bodyEx(a, n)) into jT (Forall (%a. bodyEx(a, n))) by allI over aF *)
    val minorA = Thm.forall_intr (ctermS2 aF) bodyProof;          (* !!a. jT (bodyEx(a, n)) *)
    val GnThm  = allI_atS2 (GallAbs nStep) minorA;                (* jT (G n) = jT (Forall (%a. bodyEx(a,n))) *)

    (* the strong-induction STEP theorem *)
    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) GnThm);

    (* feed to strong_induct : P := GpredSI, k := bK *)
    val bK = Free("b", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 GpredSI), (("k",0), ctermS2 bK)] (varify strong_induct));
    val Gb = Thm.implies_elim siInst stepThm;                     (* jT (G b) = jT (Forall (%a. bodyEx(a, b))) *)
    (* extract jT (bodyEx(a, b)) at a fresh aK then re-generalise both meta *)
    val aK   = Free("a", natT);
    val bodyAB = allE_atS2 (GallAbs bK) aK Gb;                    (* jT (bodyEx(a, b)) *)
  in varify bodyAB end;

val () = out "GCD_PROPS_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal, built the SAME way.
     intended := jT (Ex g. Conj (dvd g a)
                              (Conj (dvd g b)
                                 (Forall (%d. Imp (Conj (dvd d a)(dvd d b)) (dvd d g)))))
   with a, b schematic Vars.
   ============================================================================ *)
val aVg = Var (("a",0), natT);
val bVg = Var (("b",0), natT);
val gcd_props_intended = jT (bodyEx (aVg, bVg));

val r_gcd = checkS2 ("gcd_props", gcd_props, gcd_props_intended);
val () = if r_gcd then out "OK gcd_props\n" else out "FAIL gcd_props\n";

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the "greatest" conjunct makes it trivial (g := 1 divides everything),
   so the proved theorem must NOT be aconv that weakened statement. *)
val probe_weak =
  let
    fun bodyAbsW (aT, nT) =
      let val gF = Free("g_pw", natT)
      in Term.lambda gF (mkConj (dvd gF aT) (dvd gF nT)) end;     (* drops greatest *)
    val bogus = jT (mkEx (bodyAbsW (aVg, bVg)));
  in not ((Thm.prop_of gcd_props) aconv bogus) end;

val () =
  if r_gcd andalso probe_weak
  then out "PROBE_OK\n"
  else out "PROBE_UNSOUND\n";

val () = if r_gcd andalso probe_weak then out "GCD_PROPS_OK\n" else out "GCD_PROPS_FAILED\n";
(* ============================================================================
   PHASE 2 : Bezout's identity (seat bezout0)
   ----------------------------------------------------------------------------
   Prove (object-quantified inner, meta over a,b):
     !!a b. jT (Ex g. Conj (dvd g a)
                       (Conj (dvd g b)
                         (Conj (greatest a b g)
                               (comb a b g))))
   where
     greatest a b g = Forall (%d. Imp (Conj (dvd d a)(dvd d b)) (dvd d g))
     comb     a b g = Ex x. Ex y. Disj (oeq (mult a x) (add (mult b y) g))
                                        (oeq (mult b y) (add (mult a x) g))
   "every pair (a,b) has a gcd g with Bezout coefficients (two-sided over N)."

   Strong induction on b, first arg a OBJECT-universally quantified inside the
   predicate so the IH at r<b re-instantiates at a':=b for the recursive (b,r).
   Everything routes through ctxtS2/ctermS2.
   ============================================================================ *)
val () = out "BEZOUT_BEGIN\n";

val oneC = suc ZeroC;

(* ---- term builders for the Bezout body, capture-avoiding ---- *)

(* greatest(a,n,g) -- identical shape to Phase 1 *)
fun bz_greatestAbs (aT, nT, gT) =
  let val dF = Free("d_bz", natT)
  in Term.lambda dF (mkImp (mkConj (dvd dF aT) (dvd dF nT)) (dvd dF gT)) end;
fun bz_greatest (aT, nT, gT) = mkForall (bz_greatestAbs (aT, nT, gT));

(* the inner disjunction at fixed x,y : Disj (a*x = b*y+g) (b*y = a*x+g) *)
fun bz_disj (aT, nT, gT, xT, yT) =
  mkDisj (oeq (mult aT xT) (add (mult nT yT) gT))
         (oeq (mult nT yT) (add (mult aT xT) gT));

(* comb(a,n,g) = Ex x. Ex y. Disj(...) -- capture-avoiding over fresh x,y *)
fun bz_combInnerAbs (aT, nT, gT, xT) =          (* %y. Disj (...) *)
  let val yF = Free("y_bz", natT)
  in Term.lambda yF (bz_disj (aT, nT, gT, xT, yF)) end;
fun bz_combOuterAbs (aT, nT, gT) =              (* %x. Ex y. Disj (...) *)
  let val xF = Free("x_bz", natT)
  in Term.lambda xF (mkEx (bz_combInnerAbs (aT, nT, gT, xF))) end;
fun bz_comb (aT, nT, gT) = mkEx (bz_combOuterAbs (aT, nT, gT));

(* gcd body for fixed g : Conj (dvd g a)(Conj (dvd g n)(Conj (greatest)(comb))) *)
fun bz_bodyG (aT, nT, gT) =
  mkConj (dvd gT aT)
    (mkConj (dvd gT nT)
       (mkConj (bz_greatest (aT, nT, gT)) (bz_comb (aT, nT, gT))));

fun bz_bodyAbs (aT, nT) =                        (* %g. Conj (...) *)
  let val gF = Free("g_bz", natT)
  in Term.lambda gF (bz_bodyG (aT, nT, gF)) end;
fun bz_bodyEx (aT, nT) = mkEx (bz_bodyAbs (aT, nT));   (* Ex g. ... *)

(* G n = Forall (%a. bz_bodyEx(a, n)) -- the strong_induct predicate value *)
fun bz_GallAbs nT =                              (* %a. bz_bodyEx(a, n) *)
  let val aF = Free("a_BG", natT)
  in Term.lambda aF (bz_bodyEx (aF, nT)) end;
fun bz_Gprop_of nT = mkForall (bz_GallAbs nT);

val bz_GpredSI =                                 (* %n. G n *)
  let val nF = Free("n_BP", natT) in Term.lambda nF (bz_Gprop_of nF) end;

val () = out "BEZOUT_HELPERS_READY\n";

(* small helper : build the combination existential from a chosen disjunct proof *)
(* exI x, then exI y, around a Disj proof *)
fun bz_mkComb (aT, nT, gT) (xWit, yWit) hDisj =
  let
    val exInner = exI_atS2 (bz_combInnerAbs (aT, nT, gT, xWit)) yWit hDisj;  (* Ex y. Disj(...) at x=xWit *)
    val exOuter = exI_atS2 (bz_combOuterAbs (aT, nT, gT)) xWit exInner;      (* Ex x. Ex y. Disj(...) *)
  in exOuter end;

(* ============================================================================
   THE STRONG INDUCTION
   ============================================================================ *)
val bezout =
  let
    val nStep = Free("n_bz", natT);
    val mIH   = Free("m_bz", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (bz_Gprop_of mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);              (* IH : !!m. lt m n ==> jT (G m) *)
    fun applyIH mt h_lt =
      let val hAt = Thm.forall_elim (ctermS2 mt) Hthm
      in Thm.implies_elim hAt h_lt end;

    val aF = Free("a_bz", natT);
    val goalBody = bz_bodyEx (aF, nStep);               (* Ex g. ... for THIS a, THIS n *)

    val dz = dzosS_at nStep;                            (* Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)

    (* ----------------------------------------------------------------
       CASE n = 0 : g := a, x := 1, y := 0.
         dvd a a, dvd a n (via dvd_zero + cong 0->n), greatest a n a,
         comb : LEFT disjunct  a*1 = (n*0) + a   (= a = 0+a = a).
       ---------------------------------------------------------------- *)
    val caseZero =
      let
        val hZ = Thm.assume (ctermS2 (jT (oeq nStep ZeroC)));   (* oeq n 0 *)
        val dvd_a_a = dvd_refl_atS2 aF;                          (* dvd a a *)
        val dvd_a_0 = dvd_zeroS_at aF;                          (* dvd a 0 *)
        val hZsym   = oeq_sym OF [hZ];                          (* oeq 0 n *)
        val dvd_a_n = dvd_cong_rS (aF, ZeroC, nStep) hZsym dvd_a_0;   (* dvd a n *)
        (* greatest a n a *)
        val (dFz, impdz) =
          let
            val dF   = Free("d_cz", natT);
            val hC   = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));
            val c1   = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hC;   (* dvd d a = dvd d g *)
            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) c1;
            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF aF) metaImp;
          in (dF, objImp) end;
        val minor = Thm.forall_intr (ctermS2 dFz) impdz;
        val great = allI_atS2 (bz_greatestAbs (aF, nStep, aF)) minor;  (* greatest a n a *)
        (* comb a n a : LEFT disjunct  a*1 = (n*0) + a *)
        val lhs1   = mult1rS_at aF;                            (* (a*1) = a *)
        val n0     = mult0rS_at nStep;                         (* (n*0) = 0 *)
        val n0a    = add_cong_lS (mult nStep ZeroC, ZeroC, aF) n0;  (* (n*0 + a) = (0 + a) *)
        val zer_a  = add0S_at aF;                              (* (0 + a) = a *)
        val rhs_a  = oeq_trans OF [n0a, zer_a];                (* (n*0 + a) = a *)
        val rhs_as = oeq_sym OF [rhs_a];                       (* a = (n*0 + a) *)
        val disjEq = oeq_trans OF [lhs1, rhs_as];              (* (a*1) = (n*0 + a) *)
        val dLeft  = disjI1S2_at (oeq (mult aF oneC) (add (mult nStep ZeroC) aF),
                                  oeq (mult nStep ZeroC) (add (mult aF oneC) aF)) disjEq;
        val combT  = bz_mkComb (aF, nStep, aF) (oneC, ZeroC) dLeft;   (* comb a n a *)
        (* assemble Conj (dvd a a)(Conj (dvd a n)(Conj greatest comb)) *)
        val c3 = conjI_atS2 (bz_greatest (aF, nStep, aF), bz_comb (aF, nStep, aF)) great combT;
        val c2 = conjI_atS2 (dvd aF nStep, mkConj (bz_greatest (aF, nStep, aF)) (bz_comb (aF, nStep, aF))) dvd_a_n c3;
        val c1 = conjI_atS2 (dvd aF aF, mkConj (dvd aF nStep) (mkConj (bz_greatest (aF, nStep, aF)) (bz_comb (aF, nStep, aF)))) dvd_a_a c2;
        val exG = exI_atS2 (bz_bodyAbs (aF, nStep)) aF c1;     (* Ex g. ... = goalBody *)
      in Thm.implies_intr (ctermS2 (jT (oeq nStep ZeroC))) exG end;

    (* ----------------------------------------------------------------
       CASE n = Suc q : descent.
       ---------------------------------------------------------------- *)
    val caseSuc =
      let
        val PabsSuc = Abs("q", natT, oeq nStep (suc (Bound 0)));
        fun sucBody qWit (hSucEq : thm) =                       (* hSucEq : oeq n (Suc q) *)
          let
            (* lt 0 n *)
            val lt0Sq = lt_zero_suc_atS qWit;                   (* lt 0 (Suc q) *)
            val sucEqSym = oeq_sym OF [hSucEq];                 (* oeq (Suc q) n *)
            val ltPosPabs = Term.lambda (Free("z_lp", natT)) (lt ZeroC (Free("z_lp", natT)));
            val lt0n = oeq_rewrite_atS (ltPosPabs, suc qWit, nStep) sucEqSym lt0Sq;  (* lt 0 n *)
            (* div_mod a / n *)
            val dmEx = div_mod_atS (aF, nStep) lt0n;            (* Ex q'. Ex r. Conj(oeq a (n*q'+r))(lt r n) *)
            fun qBody qDiv (hQex : thm) =
              let
                fun rBody rDiv (hConj : thm) =
                  let
                    val eqDivP = oeq aF (add (mult nStep qDiv) rDiv);   (* a = n*q' + r *)
                    val ltRnP  = lt rDiv nStep;                        (* r < n *)
                    val hEqDiv = conjunct1_atS2 (eqDivP, ltRnP) hConj;  (* oeq a (n*q' + r) *)
                    val hLtRn  = conjunct2_atS2 (eqDivP, ltRnP) hConj;  (* lt r n *)

                    (* IH at r, then instantiate inner object-a at a' := n *)
                    val Gr     = applyIH rDiv hLtRn;                   (* Forall(%a'. bz_bodyEx(a', r)) *)
                    val GrAtN  = allE_atS2 (bz_GallAbs rDiv) nStep Gr; (* bz_bodyEx(n, r) *)

                    fun gBody gWit (hG : thm) =
                      let
                        (* hG : Conj(dvd g n)(Conj(dvd g r)(Conj(greatest n r g)(comb n r g))) *)
                        val gNd   = dvd gWit nStep;
                        val gRd   = dvd gWit rDiv;
                        val grGt  = bz_greatest (nStep, rDiv, gWit);
                        val grCb  = bz_comb (nStep, rDiv, gWit);
                        val h_g_n   = conjunct1_atS2 (gNd, mkConj gRd (mkConj grGt grCb)) hG;          (* dvd g n *)
                        val h_rest1 = conjunct2_atS2 (gNd, mkConj gRd (mkConj grGt grCb)) hG;          (* Conj(dvd g r)(Conj greatest comb) *)
                        val h_g_r   = conjunct1_atS2 (gRd, mkConj grGt grCb) h_rest1;                  (* dvd g r *)
                        val h_rest2 = conjunct2_atS2 (gRd, mkConj grGt grCb) h_rest1;                  (* Conj greatest comb *)
                        val h_great = conjunct1_atS2 (grGt, grCb) h_rest2;                             (* greatest n r g *)
                        val h_comb  = conjunct2_atS2 (grGt, grCb) h_rest2;                             (* comb n r g *)

                        (* ---- (1) g divides a ---- (same as Phase 1) *)
                        val g_nq    = dvd_mult_right_atS (gWit, nStep, qDiv) h_g_n;      (* dvd g (n*q') *)
                        val g_sum   = dvd_add_atS (gWit, mult nStep qDiv, rDiv) g_nq h_g_r;  (* dvd g (n*q'+r) *)
                        val eqSym   = oeq_sym OF [hEqDiv];                               (* oeq (n*q'+r) a *)
                        val g_a     = dvd_cong_rS (gWit, add (mult nStep qDiv) rDiv, aF) eqSym g_sum;  (* dvd g a *)

                        (* ---- (2) greatest for (a, n) ---- (same as Phase 1) *)
                        val greatAN =
                          let
                            val dF = Free("d_an", natT);
                            val hCd = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));
                            val d_a = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d a *)
                            val d_n = conjunct2_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d n *)
                            val d_nq = dvd_mult_right_atS (dF, nStep, qDiv) d_n;          (* dvd d (n*q') *)
                            val d_sum = dvd_cong_rS (dF, aF, add (mult nStep qDiv) rDiv) hEqDiv d_a;  (* dvd d (n*q'+r) *)
                            val d_r   = dvd_diff_atS (dF, mult nStep qDiv, rDiv) d_nq d_sum;          (* dvd d r *)
                            val hImp  = allE_atS2 (bz_greatestAbs (nStep, rDiv, gWit)) dF h_great;    (* Imp(Conj(dvd d n)(dvd d r))(dvd d g) *)
                            val cnj   = conjI_atS2 (dvd dF nStep, dvd dF rDiv) d_n d_r;
                            val d_g   = mp_atS2 (mkConj (dvd dF nStep) (dvd dF rDiv), dvd dF gWit) hImp cnj;  (* dvd d g *)
                            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) d_g;
                            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF gWit) metaImp;
                            val minor   = Thm.forall_intr (ctermS2 dF) objImp;
                          in allI_atS2 (bz_greatestAbs (aF, nStep, gWit)) minor end;      (* greatest a n g *)

                        (* ---- (3) THE COMBINATION : from comb(n, r, g), derive comb(a, n, g) ---- *)
                        val combAN =
                          let
                            (* starEq: a*y = n*(q'*y) + r*y   for any y, from a = n*q' + r.
                               proof: a*y = (n*q'+r)*y = (n*q')*y + r*y = n*(q'*y) + r*y *)
                            fun starEq yT =                                     (* oeq (a*y) (add (n*(q'*y)) (r*y)) *)
                              let
                                val s1 = mult_cong_lS (aF, add (mult nStep qDiv) rDiv, yT) hEqDiv;  (* (a*y) = ((n*q'+r)*y) *)
                                val s2 = rdist_at_S2 (mult nStep qDiv, rDiv, yT);                   (* ((n*q'+r)*y) = ((n*q')*y + r*y) *)
                                val s3 = mult_assoc_atS (nStep, qDiv, yT);                          (* ((n*q')*y) = (n*(q'*y)) *)
                                val s3l= add_cong_lS (mult (mult nStep qDiv) yT, mult nStep (mult qDiv yT), mult rDiv yT) s3;
                                                                                                   (* ((n*q')*y + r*y) = (n*(q'*y) + r*y) *)
                                val t1 = oeq_trans OF [s1, s2];                 (* (a*y) = ((n*q')*y + r*y) *)
                                val t2 = oeq_trans OF [t1, s3l];                (* (a*y) = (n*(q'*y) + r*y) *)
                              in t2 end;

                            (* the comb(n,r,g) existential : Ex x'. Ex y'. Disj (n*x'=r*y'+g)(r*y'=n*x'+g) *)
                            fun combOuterBody xpW (hExY : thm) =
                              let
                                fun combInnerBody ypW (hDisj : thm) =
                                  let
                                    (* the two IH disjuncts *)
                                    val dL = oeq (mult nStep xpW) (add (mult rDiv ypW) gWit);   (* n*x' = r*y' + g *)
                                    val dR = oeq (mult rDiv ypW) (add (mult nStep xpW) gWit);   (* r*y' = n*x' + g *)

                                    (* targets for comb(a,n,g) *)
                                    fun aDisjL (xT, yT) = oeq (mult aF xT) (add (mult nStep yT) gWit);  (* a*X = n*Y + g  (LEFT) *)
                                    fun aDisjR (xT, yT) = oeq (mult nStep yT) (add (mult aF xT) gWit);  (* n*Y = a*X + g  (RIGHT) *)

                                    (* ===== CASE IH-LEFT : n*x' = r*y' + g  ====>  RIGHT disjunct for (a,n)
                                       X := y', Y := x' + q'*y'.
                                       Show n*(x' + q'*y') = a*y' + g.
                                         LHS = n*x' + n*(q'*y')                 [left_distrib]
                                             = (r*y'+g) + n*(q'*y')             [subst dL]
                                             = n*(q'*y') + r*y' + g             [add comm/assoc]
                                             = a*y' + g                         [starEq y' backwards]  *)
                                    val caseL =
                                      let
                                        val hL  = Thm.assume (ctermS2 (jT dL));    (* n*x' = r*y' + g *)
                                        val Yt = add xpW (mult qDiv ypW);
                                        (* LHS expand : n*(x'+q'*y') = n*x' + n*(q'*y') *)
                                        val ld  = left_distrib_atS (nStep, xpW, mult qDiv ypW);  (* n*(x'+q'y') = n*x' + n*(q'y') *)
                                        (* subst n*x' = r*y'+g *)
                                        val sb  = add_cong_lS (mult nStep xpW, add (mult rDiv ypW) gWit, mult nStep (mult qDiv ypW)) hL;
                                                  (* (n*x' + n*(q'y')) = ((r*y'+g) + n*(q'y')) *)
                                        val e1  = oeq_trans OF [ld, sb];  (* n*(x'+q'y') = ((r*y'+g) + n*(q'y')) *)
                                        (* rearrange ((r*y'+g) + n*(q'y')) = (n*(q'y') + r*y') + g
                                           step a: (r*y'+g) + n*(q'y') = n*(q'y') + (r*y'+g)   [comm]
                                           step b: n*(q'y') + (r*y'+g) = (n*(q'y') + r*y') + g  [assoc backwards] *)
                                        val cm  = addcommS_at (add (mult rDiv ypW) gWit, mult nStep (mult qDiv ypW));
                                                  (* ((r*y'+g) + n*(q'y')) = (n*(q'y') + (r*y'+g)) *)
                                        val asc = addassocS_at (mult nStep (mult qDiv ypW), mult rDiv ypW, gWit);
                                                  (* ((n*(q'y') + r*y') + g) = (n*(q'y') + (r*y' + g)) *)
                                        val ascS= oeq_sym OF [asc];  (* (n*(q'y') + (r*y'+g)) = ((n*(q'y') + r*y') + g) *)
                                        val e2  = oeq_trans OF [e1, cm];   (* n*(x'+q'y') = (n*(q'y') + (r*y'+g)) *)
                                        val e3  = oeq_trans OF [e2, ascS]; (* n*(x'+q'y') = ((n*(q'y') + r*y') + g) *)
                                        (* a*y' = n*(q'y') + r*y'  [starEq y']  =>  (n*(q'y') + r*y') = a*y'  *)
                                        val st  = starEq ypW;              (* a*y' = (n*(q'y') + r*y') *)
                                        val stS = oeq_sym OF [st];         (* (n*(q'y') + r*y') = a*y' *)
                                        val stL = add_cong_lS (add (mult nStep (mult qDiv ypW)) (mult rDiv ypW), mult aF ypW, gWit) stS;
                                                  (* ((n*(q'y') + r*y') + g) = (a*y' + g) *)
                                        val e4  = oeq_trans OF [e3, stL];  (* n*(x'+q'y') = (a*y' + g) *)
                                        (* this is aDisjR (X:=y', Y:=x'+q'y') :  oeq (n*Y) (a*X + g) *)
                                        val dR_an = disjI2S2_at (aDisjL (ypW, Yt), aDisjR (ypW, Yt)) e4;
                                        val combRes = bz_mkComb (aF, nStep, gWit) (ypW, Yt) dR_an;
                                      in Thm.implies_intr (ctermS2 (jT dL)) combRes end;

                                    (* ===== CASE IH-RIGHT : r*y' = n*x' + g  ====>  LEFT disjunct for (a,n)
                                       X := y', Y := q'*y' + x'.
                                       Show a*y' = n*(q'*y' + x') + g.
                                         a*y' = n*(q'*y') + r*y'             [starEq y']
                                              = n*(q'*y') + (n*x' + g)       [subst dR]
                                              = (n*(q'*y') + n*x') + g       [assoc]
                                              = n*(q'*y' + x') + g           [left_distrib backwards] *)
                                    val caseR =
                                      let
                                        val hR  = Thm.assume (ctermS2 (jT dR));    (* r*y' = n*x' + g *)
                                        val Yt = add (mult qDiv ypW) xpW;
                                        val st  = starEq ypW;              (* a*y' = (n*(q'y') + r*y') *)
                                        (* subst r*y' = n*x' + g *)
                                        val sb  = add_cong_rS (mult nStep (mult qDiv ypW), mult rDiv ypW, add (mult nStep xpW) gWit) hR;
                                                  (* (n*(q'y') + r*y') = (n*(q'y') + (n*x' + g)) *)
                                        val e1  = oeq_trans OF [st, sb];   (* a*y' = (n*(q'y') + (n*x' + g)) *)
                                        (* assoc : (n*(q'y') + (n*x' + g)) = ((n*(q'y') + n*x') + g) *)
                                        val asc = addassocS_at (mult nStep (mult qDiv ypW), mult nStep xpW, gWit);
                                                  (* ((n*(q'y') + n*x') + g) = (n*(q'y') + (n*x' + g)) *)
                                        val ascS= oeq_sym OF [asc];  (* (n*(q'y') + (n*x' + g)) = ((n*(q'y') + n*x') + g) *)
                                        val e2  = oeq_trans OF [e1, ascS]; (* a*y' = ((n*(q'y') + n*x') + g) *)
                                        (* left_distrib backwards : n*(q'y'+x') = n*(q'y') + n*x'  =>  reverse  *)
                                        val ld  = left_distrib_atS (nStep, mult qDiv ypW, xpW);  (* n*(q'y'+x') = (n*(q'y') + n*x') *)
                                        val ldS = oeq_sym OF [ld];  (* (n*(q'y') + n*x') = n*(q'y'+x') *)
                                        val ldL = add_cong_lS (add (mult nStep (mult qDiv ypW)) (mult nStep xpW), mult nStep Yt, gWit) ldS;
                                                  (* ((n*(q'y') + n*x') + g) = (n*(q'y'+x') + g) *)
                                        val e3  = oeq_trans OF [e2, ldL];  (* a*y' = (n*(q'y'+x') + g) = (n*Y + g) *)
                                        (* this is aDisjL (X:=y', Y:=q'y'+x') : oeq (a*X) (n*Y + g) *)
                                        val dL_an = disjI1S2_at (aDisjL (ypW, Yt), aDisjR (ypW, Yt)) e3;
                                        val combRes = bz_mkComb (aF, nStep, gWit) (ypW, Yt) dL_an;
                                      in Thm.implies_intr (ctermS2 (jT dR)) combRes end;

                                    val combRes = disjE_elimS2 (dL, dR, bz_comb (aF, nStep, gWit)) hDisj caseL caseR;
                                  in combRes end;
                                val g = exE_elimS2 (bz_combInnerAbs (nStep, rDiv, gWit, xpW), bz_comb (aF, nStep, gWit)) hExY "y_w" combInnerBody;
                              in g end;
                            val g = exE_elimS2 (bz_combOuterAbs (nStep, rDiv, gWit), bz_comb (aF, nStep, gWit)) h_comb "x_w" combOuterBody;
                          in g end;

                        (* assemble Conj (dvd g a)(Conj (dvd g n)(Conj greatest comb)) *)
                        val c3 = conjI_atS2 (bz_greatest (aF, nStep, gWit), bz_comb (aF, nStep, gWit)) greatAN combAN;
                        val c2 = conjI_atS2 (dvd gWit nStep, mkConj (bz_greatest (aF, nStep, gWit)) (bz_comb (aF, nStep, gWit))) h_g_n c3;
                        val c1 = conjI_atS2 (dvd gWit aF, mkConj (dvd gWit nStep) (mkConj (bz_greatest (aF, nStep, gWit)) (bz_comb (aF, nStep, gWit)))) g_a c2;
                        val exG = exI_atS2 (bz_bodyAbs (aF, nStep)) gWit c1;     (* goalBody *)
                      in exG end;
                    val g = exE_elimS2 (bz_bodyAbs (nStep, rDiv), goalBody) GrAtN "g_w" gBody;
                  in g end;
                val g = exE_elimS2 (innerDivAbsN nStep aF qDiv, goalBody) hQex "r_w" rBody;
              in g end;
            val g = exE_elimS2 (rmDivBodyN nStep aF, goalBody) dmEx "q_w" qBody;
          in g end;
        val gg = exE_elimS2 (PabsSuc, goalBody) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "q_sw" sucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) gg end;

    (* combine the two cases *)
    val bodyProof = disjE_elimS2 (oeq nStep ZeroC, mkExSuc nStep, goalBody) dz caseZero caseSuc;
    val minorA = Thm.forall_intr (ctermS2 aF) bodyProof;
    val GnThm  = allI_atS2 (bz_GallAbs nStep) minorA;     (* jT (G n) *)

    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) GnThm);

    val bK = Free("b", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 bz_GpredSI), (("k",0), ctermS2 bK)] (varify strong_induct));
    val Gb = Thm.implies_elim siInst stepThm;             (* jT (G b) *)
    val aK   = Free("a", natT);
    val bodyAB = allE_atS2 (bz_GallAbs bK) aK Gb;         (* jT (bz_bodyEx(a, b)) *)
  in varify bodyAB end;

val () = out "BEZOUT_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal, built the SAME way.
   ============================================================================ *)
val aVb = Var (("a",0), natT);
val bVb = Var (("b",0), natT);
val bezout_intended = jT (bz_bodyEx (aVb, bVb));

val r_bez = checkS2 ("bezout", bezout, bezout_intended);
val () = if r_bez then out "OK bezout\n" else out "FAIL bezout\n";

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the combination conjunct makes it the weaker Phase-1 statement;
   the proved theorem must NOT be aconv that weakened statement. *)
val probe_bez =
  let
    fun bodyAbsW (aT, nT) =
      let val gF = Free("g_pw", natT)
      in Term.lambda gF (mkConj (dvd gF aT)
                          (mkConj (dvd gF nT) (bz_greatest (aT, nT, gF)))) end;   (* drops comb *)
    val bogus = jT (mkEx (bodyAbsW (aVb, bVb)));
  in not ((Thm.prop_of bezout) aconv bogus) end;

val () =
  if r_bez andalso probe_bez
  then out "PROBE_OK\n"
  else out "PROBE_UNSOUND\n";

val () = if r_bez andalso probe_bez then out "BEZOUT_OK\n" else out "BEZOUT_FAILED\n";
(* ============================================================================
   PHASE 3 : coprime_bezout  (seat crt0)
   ----------------------------------------------------------------------------
   PRIMARY GOAL.  Prove (meta over a,b):
     !!a b. jT (Forall (%d. Imp (Conj (dvd d a)(dvd d b)) (oeq d 1)))
             ==> jT (Ex x. Ex y.
                       Disj (oeq (mult a x) (add (mult b y) 1))
                            (oeq (mult b y) (add (mult a x) 1)))

   COROLLARY of bezout (Phase 2): from bezout get g with
     greatest a b g  and  comb a b g = Ex x. Ex y. Disj (a*x = b*y+g)(b*y = a*x+g).
   g divides a and g divides b (the first two conjuncts), so the coprimality
   hypothesis applied to g gives g = 1; substitute g = 1 into the combination.
   ============================================================================ *)
val () = out "COPRIME_BEZOUT_BEGIN\n";

(* ---- the coprime-coefficient goal's term builders (g replaced by 1) ---- *)
(* one-sided disjunction at fixed x,y, target is 1 not g *)
fun cb_disj (aT, bT, xT, yT) =
  mkDisj (oeq (mult aT xT) (add (mult bT yT) oneC))
         (oeq (mult bT yT) (add (mult aT xT) oneC));

fun cb_innerAbs (aT, bT, xT) =                 (* %y. Disj (...) *)
  let val yF = Free("y_cb", natT)
  in Term.lambda yF (cb_disj (aT, bT, xT, yF)) end;
fun cb_outerAbs (aT, bT) =                      (* %x. Ex y. Disj (...) *)
  let val xF = Free("x_cb", natT)
  in Term.lambda xF (mkEx (cb_innerAbs (aT, bT, xF))) end;
fun cb_goal (aT, bT) = mkEx (cb_outerAbs (aT, bT));   (* Ex x. Ex y. Disj(...) *)

(* exI x, then exI y, around a Disj proof matching cb_disj *)
fun cb_mkGoal (aT, bT) (xWit, yWit) hDisj =
  let
    val exInner = exI_atS2 (cb_innerAbs (aT, bT, xWit)) yWit hDisj;
    val exOuter = exI_atS2 (cb_outerAbs (aT, bT)) xWit exInner;
  in exOuter end;

(* the coprime hypothesis predicate : %d. Imp (Conj (dvd d a)(dvd d b)) (oeq d 1) *)
fun cb_copAbs (aT, bT) =
  let val dF = Free("d_cop", natT)
  in Term.lambda dF (mkImp (mkConj (dvd dF aT) (dvd dF bT)) (oeq dF oneC)) end;
fun cb_cop (aT, bT) = mkForall (cb_copAbs (aT, bT));

val () = out "COPRIME_BEZOUT_HELPERS_READY\n";

val coprime_bezout =
  let
    val aF = Free("a", natT);
    val bF = Free("b", natT);

    (* assume the coprimality hypothesis *)
    val copP  = jT (cb_cop (aF, bF));
    val hCop  = Thm.assume (ctermS2 copP);

    (* instantiate bezout at a := aF, b := bF *)
    val bezAB = beta_norm (Drule.infer_instantiate ctxtS2
                  [(("a",0), ctermS2 aF), (("b",0), ctermS2 bF)] bezout);   (* jT (bz_bodyEx(a,b)) *)

    (* exE the gcd witness g, then build the goal *)
    val goalC = cb_goal (aF, bF);
    fun gBody gWit (hG : thm) =
      let
        (* hG : Conj (dvd g a)(Conj (dvd g b)(Conj (greatest a b g)(comb a b g))) *)
        val gAd  = dvd gWit aF;
        val gBd  = dvd gWit bF;
        val grGt = bz_greatest (aF, bF, gWit);
        val grCb = bz_comb (aF, bF, gWit);
        val h_g_a   = conjunct1_atS2 (gAd, mkConj gBd (mkConj grGt grCb)) hG;        (* dvd g a *)
        val h_rest1 = conjunct2_atS2 (gAd, mkConj gBd (mkConj grGt grCb)) hG;        (* Conj(dvd g b)(Conj greatest comb) *)
        val h_g_b   = conjunct1_atS2 (gBd, mkConj grGt grCb) h_rest1;                (* dvd g b *)
        val h_rest2 = conjunct2_atS2 (gBd, mkConj grGt grCb) h_rest1;                (* Conj greatest comb *)
        val h_comb  = conjunct2_atS2 (grGt, grCb) h_rest2;                           (* comb a b g *)

        (* coprimality at g : Imp (Conj (dvd g a)(dvd g b)) (oeq g 1) *)
        val hImp = allE_atS2 (cb_copAbs (aF, bF)) gWit hCop;                         (* Imp(Conj(dvd g a)(dvd g b))(oeq g 1) *)
        val hCnj = conjI_atS2 (dvd gWit aF, dvd gWit bF) h_g_a h_g_b;                (* Conj(dvd g a)(dvd g b) *)
        val hg1  = mp_atS2 (mkConj (dvd gWit aF) (dvd gWit bF), oeq gWit oneC) hImp hCnj;  (* oeq g 1 *)

        (* exE the combination : Ex x. Ex y. Disj (a*x = b*y+g)(b*y = a*x+g) *)
        fun combOuterBody xpW (hExY : thm) =
          let
            fun combInnerBody ypW (hDisj : thm) =
              let
                (* the two bezout disjuncts (with g) *)
                val dL = oeq (mult aF xpW) (add (mult bF ypW) gWit);   (* a*x = b*y + g *)
                val dR = oeq (mult bF ypW) (add (mult aF xpW) gWit);   (* b*y = a*x + g *)

                (* target disjuncts (with 1) *)
                val tL = oeq (mult aF xpW) (add (mult bF ypW) oneC);   (* a*x = b*y + 1 *)
                val tR = oeq (mult bF ypW) (add (mult aF xpW) oneC);   (* b*y = a*x + 1 *)

                (* CASE LEFT : a*x = b*y + g.  Rewrite g -> 1 :
                     (b*y + g) = (b*y + 1)  by add_cong_rS (b*y, g, 1) hg1
                     then a*x = (b*y + 1) by trans. *)
                val caseL =
                  let
                    val hL   = Thm.assume (ctermS2 (jT dL));            (* a*x = b*y + g *)
                    val rw   = add_cong_rS (mult bF ypW, gWit, oneC) hg1;  (* (b*y + g) = (b*y + 1) *)
                    val eqT  = oeq_trans OF [hL, rw];                   (* a*x = (b*y + 1) = tL *)
                    val dLeft= disjI1S2_at (tL, tR) eqT;
                    val res  = cb_mkGoal (aF, bF) (xpW, ypW) dLeft;
                  in Thm.implies_intr (ctermS2 (jT dL)) res end;

                (* CASE RIGHT : b*y = a*x + g.  Same rewrite on the right summand. *)
                val caseR =
                  let
                    val hR   = Thm.assume (ctermS2 (jT dR));            (* b*y = a*x + g *)
                    val rw   = add_cong_rS (mult aF xpW, gWit, oneC) hg1;  (* (a*x + g) = (a*x + 1) *)
                    val eqT  = oeq_trans OF [hR, rw];                   (* b*y = (a*x + 1) = tR *)
                    val dRight = disjI2S2_at (tL, tR) eqT;
                    val res  = cb_mkGoal (aF, bF) (xpW, ypW) dRight;
                  in Thm.implies_intr (ctermS2 (jT dR)) res end;

                val res = disjE_elimS2 (dL, dR, goalC) hDisj caseL caseR;
              in res end;
            val g = exE_elimS2 (bz_combInnerAbs (aF, bF, gWit, xpW), goalC) hExY "y_cw" combInnerBody;
          in g end;
        val g = exE_elimS2 (bz_combOuterAbs (aF, bF, gWit), goalC) h_comb "x_cw" combOuterBody;
      in g end;
    val bodyGoal = exE_elimS2 (bz_bodyAbs (aF, bF), goalC) bezAB "g_cw" gBody;
    (* discharge the coprimality hypothesis -> meta implication *)
    val disch = Thm.implies_intr (ctermS2 copP) bodyGoal;
  in varify disch end;

val () = out "COPRIME_BEZOUT_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal, built the SAME way.
     intended := jT (cop a b) ==> jT (cb_goal a b)   with a,b schematic Vars.
   ============================================================================ *)
val aVcb = Var (("a",0), natT);
val bVcb = Var (("b",0), natT);
val coprime_bezout_intended =
  Logic.mk_implies (jT (cb_cop (aVcb, bVcb)), jT (cb_goal (aVcb, bVcb)));

val r_cb = checkS2 ("coprime_bezout", coprime_bezout, coprime_bezout_intended);
val () = if r_cb then out "OK coprime_bezout\n" else out "FAIL coprime_bezout\n";

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the coprimality hypothesis would assert that EVERY a,b have x,y
   with a*x = b*y+1 OR b*y = a*x+1 (false: a=b=0).  The proved theorem must NOT
   be aconv that hypothesis-free statement. *)
val probe_cb =
  let
    val bogus = jT (cb_goal (aVcb, bVcb));   (* drops the cop hypothesis entirely *)
  in not ((Thm.prop_of coprime_bezout) aconv bogus) end;

val () =
  if r_cb andalso probe_cb
  then out "PROBE_OK\n"
  else out "PROBE_UNSOUND\n";

val () =
  if r_cb andalso probe_cb
  then out "COPRIME_BEZOUT_OK\n"
  else out "COPRIME_BEZOUT_FAILED\n";

(* ============================================================================
   STRETCH GOAL : modular inverse for a prime  (seat crt0)
   ----------------------------------------------------------------------------
     !!p a. jT (prime2 p) ==> jT (neg (dvd p a))
              ==> jT (Ex b. cong p (mult a b) 1)
   Strategy : prime p + ~(p|a) make a,p coprime; coprime_bezout(a,p) gives x,y
   with (a*x = p*y+1)  OR  (p*y = a*x+1).
     - LEFT  : a*x = p*y+1  =>  a*x = 1 + p*y  (comm)  => cong p (a*x) 1 via congR.
               witness b := x.
     - RIGHT : p*y = a*x+1  =>  a*x = -1 (mod p)  => choose b := x*(a*x), so
               a*b = (a*x)^2 = 1 + p*M (M from le y ((a*x)*y)); cong via congR.
   ============================================================================ *)
val () = out "MOD_INVERSE_BEGIN\n";

(* lift the base lemmas we need onto ctxtS2 (schematic).
   NOTE: we use the CAPTURE-AVOIDING structural prime `prime2` (base line 2810):
     prime2 p = Conj (lt 1 p) (Forall (ppAbs p)),
   whose destructors we inline via conjunct1/2 + the base `ppAbs`.  The phase-2
   `prime`/`prime_div` use a de-Bruijn-malformed predicate (the inner dvd reads
   `Ex k. p = k*k`), so we do NOT use them. *)
val ne0_suc_vS   = varify ne0_suc;          (* jT (neg (oeq d 0)) ==> jT (Ex m. oeq d (Suc m)) *)
val mult_Suc_vS  = varify mult_Suc;         (* jT (oeq (mult (Suc m) n) (add n (mult m n))) *)

fun ne0_suc_atS dt hne =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("d",0), ctermS2 dt)] ne0_suc_vS)
  in Thm.implies_elim inst hne end;
fun mult_Suc_atS (mt, nt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("n",0), ctermS2 nt)] mult_Suc_vS);

(* prime2 destructors on ctxtS2 *)
fun prime2_gt1 pt hprime = conjunct1_atS2 (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;  (* lt 1 p *)
fun prime2_div pt hprime = conjunct2_atS2 (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;  (* Forall (ppAbs p) *)

val () = out "MOD_INVERSE_HELPERS_READY\n";

(* prime predicate body abstraction = base ppAbs (capture-avoiding) *)
val primeBodyAbs = ppAbs;

(* goal-existential builder : Ex b. cong p (mult a b) 1 *)
fun mi_innerAbs (pt, at) =
  let val bF = Free("b_mi", natT)
  in Term.lambda bF (cong pt (mult at bF) oneC) end;
fun mi_goal (pt, at) = mkEx (mi_innerAbs (pt, at));
fun mi_mkGoal (pt, at) bWit hcong =
  exI_atS2 (mi_innerAbs (pt, at)) bWit hcong;

val mod_inverse =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val hPrime = Thm.assume (ctermS2 (jT (prime2 pF)));
    val hNdvdP = jT (neg (dvd pF aF));                       (* Imp (dvd p a) oFalse *)
    val hNdvd  = Thm.assume (ctermS2 hNdvdP);

    (* ---- STEP 1 : coprimality  Hcop : Forall (%d. Imp (Conj (dvd d a)(dvd d p))(oeq d 1)) ---- *)
    val Hcop =
      let
        val dF = Free("d_cp", natT);
        (* assume Conj (dvd d a)(dvd d p) *)
        val cnjP = jT (mkConj (dvd dF aF) (dvd dF pF));
        val hCnj = Thm.assume (ctermS2 cnjP);
        val dda  = conjunct1_atS2 (dvd dF aF, dvd dF pF) hCnj;     (* dvd d a *)
        val ddp  = conjunct2_atS2 (dvd dF aF, dvd dF pF) hCnj;     (* dvd d p *)
        (* prime_div : Forall (%d. Imp (dvd d p)(Disj (oeq d 1)(oeq d p))) *)
        val pdiv = prime2_div pF hPrime;
        val hImp = allE_atS2 (primeBodyAbs pF) dF pdiv;            (* Imp (dvd d p)(Disj (oeq d 1)(oeq d p)) *)
        val hDisj= mp_atS2 (dvd dF pF, mkDisj (oeq dF oneC) (oeq dF pF)) hImp ddp;  (* Disj (oeq d 1)(oeq d p) *)
        (* disjE -> oeq d 1 *)
        val caseEq1 =
          let val h = Thm.assume (ctermS2 (jT (oeq dF oneC)))
          in Thm.implies_intr (ctermS2 (jT (oeq dF oneC))) h end;
        val caseEqP =
          let
            val h   = Thm.assume (ctermS2 (jT (oeq dF pF)));       (* oeq d p *)
            (* build dvd p a from dvd d a + oeq d p : exE k, oeq a (mult d k), rewrite d->p *)
            val ddaAbs = Abs("k", natT, oeq aF (mult dF (Bound 0)));
            fun kbody kW (hk : thm) =                              (* hk : oeq a (mult d k) *)
              let
                val cong_dk = mult_cong_lS (dF, pF, kW) h;         (* oeq (mult d k)(mult p k) *)
                val a_pk    = oeq_trans OF [hk, cong_dk];          (* oeq a (mult p k) *)
                val dpa     = dvd_introS (pF, aF, kW) a_pk;        (* dvd p a *)
                val fAls    = mp_atS2 (dvd pF aF, oFalseC) hNdvd dpa;  (* oFalse *)
                val any     = oFalse_elimS_at (oeq dF oneC) ;      (* jT oFalse ==> jT (oeq d 1) *)
              in Thm.implies_elim any fAls end;
            val concl = exE_elimS2 (ddaAbs, oeq dF oneC) dda "k_cp" kbody;  (* oeq d 1 *)
          in Thm.implies_intr (ctermS2 (jT (oeq dF pF))) concl end;
        val res = disjE_elimS2 (oeq dF oneC, oeq dF pF, oeq dF oneC) hDisj caseEq1 caseEqP;
        (* discharge Conj, impI, allI *)
        val metaImp = Thm.implies_intr (ctermS2 cnjP) res;
        val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF pF), oeq dF oneC) metaImp;
        val minor   = Thm.forall_intr (ctermS2 dF) objImp;
      in allI_atS2 (cb_copAbs (aF, pF)) minor end;                (* Forall (%d. Imp (Conj (dvd d a)(dvd d p))(oeq d 1)) *)

    (* ---- STEP 2 : apply coprime_bezout at a := a, b := p ---- *)
    val cbInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("a",0), ctermS2 aF), (("b",0), ctermS2 pF)] coprime_bezout);
    val cbDisjEx = Thm.implies_elim cbInst Hcop;                  (* Ex x. Ex y. Disj (a*x = p*y+1)(p*y = a*x+1) *)

    val goalC = mi_goal (pF, aF);

    fun xbody xW (hExY : thm) =
      let
        fun ybody yW (hDisj : thm) =
          let
            val ax = mult aF xW;                                  (* a*x *)
            (* the two bezout disjuncts (b := p) *)
            val dL = oeq ax (add (mult pF yW) oneC);              (* a*x = p*y + 1 *)
            val dR = oeq (mult pF yW) (add ax oneC);              (* p*y = a*x + 1 *)

            (* ===== CASE LEFT : a*x = p*y + 1.  Witness b := x. ===== *)
            val caseL =
              let
                val hL = Thm.assume (ctermS2 (jT dL));            (* a*x = p*y + 1 *)
                (* want congR p (a*x) 1 : Ex k. oeq (a*x) (add 1 (mult p k)), witness k := y *)
                val cm = addcommS_at (mult pF yW, oneC);          (* (p*y + 1) = (1 + p*y) *)
                val axeq = oeq_trans OF [hL, cm];                 (* a*x = (1 + p*y) *)
                (* congR body at k=y is  oeq (a*x) (add 1 (mult p y)) -- matches axeq *)
                val congRabs = Abs("k", natT, oeq ax (add oneC (mult pF (Bound 0))));
                val exCongR  = exI_atS2 congRabs yW axeq;         (* congR p (a*x) 1 *)
                (* cong p (a*x) 1 = Disj (congL ..)(congR ..) ; use disjI2 *)
                val hcong    = disjI2S2_at (congL pF ax oneC, congR pF ax oneC) exCongR;
                val res      = mi_mkGoal (pF, aF) xW hcong;       (* Ex b. cong p (a*b) 1, b := x *)
              in Thm.implies_intr (ctermS2 (jT dL)) res end;

            (* ===== CASE RIGHT : p*y = a*x + 1.  Witness b := x*(a*x). ===== *)
            val caseR =
              let
                val hR = Thm.assume (ctermS2 (jT dR));            (* p*y = a*x + 1 *)
                val sq = mult ax ax;                              (* (a*x)^2 *)
                val Q  = mult ax yW;                              (* (a*x)*y *)
                val bWit = mult xW ax;                            (* x*(a*x) *)

                (* eq_ab : oeq (mult a bWit) sq    [ a*(x*ax) = (a*x)*ax = ax*ax ]
                   mult_assoc gives  sq = (a*x)*ax = a*(x*ax) = a*bWit, so SYM it. *)
                val eq_ab = oeq_sym OF [mult_assoc_atS (aF, xW, ax)];   (* a*bWit = sq *)

                (* (i) : oeq (add sq ax) (mult p Q) *)
                (* c1 : ax*(p*y) = ax*(a*x+1) *)
                val c1 = mult_cong_rS (ax, mult pF yW, add ax oneC) hR;
                (* LHS chain : ax*(p*y) -> p*Q *)
                val l1 = oeq_sym OF [mult_assoc_atS (ax, pF, yW)]; (* ax*(p*y) = (ax*p)*y *)
                val l2 = mult_cong_lS (mult ax pF, mult pF ax, yW) (mult_comm_atS (ax, pF)); (* (ax*p)*y = (p*ax)*y *)
                val l3 = mult_assoc_atS (pF, ax, yW);             (* (p*ax)*y = p*(ax*y) = p*Q *)
                val lLHS = oeq_trans OF [oeq_trans OF [l1, l2], l3];  (* ax*(p*y) = p*Q *)
                (* RHS chain : ax*(ax+1) -> sq + ax *)
                val r1 = left_distrib_atS (ax, ax, oneC);         (* ax*(ax+1) = ax*ax + ax*1 *)
                val r2 = mult1rS_at ax;                           (* ax*1 = ax *)
                val r2c= add_cong_rS (mult ax ax, mult ax oneC, ax) r2;  (* (ax*ax + ax*1) = (ax*ax + ax) = (sq+ax) *)
                val rRHS = oeq_trans OF [r1, r2c];                (* ax*(ax+1) = sq+ax *)
                (* combine : p*Q = sq+ax  =>  sq+ax = p*Q *)
                val pQ_eq = oeq_trans OF [oeq_trans OF [oeq_sym OF [lLHS], c1], rRHS];  (* p*Q = sq+ax *)
                val iEq   = oeq_sym OF [pQ_eq];                   (* (i) : sq+ax = p*Q *)

                (* ---- ax != 0 (else p*y = 1, with y>=1, p>=2 -> contra). We instead
                        prove ax = Suc k via ne0_suc on (neg (oeq ax 0)). ---- *)
                (* neg (oeq ax 0) : assume oeq ax 0, derive oFalse *)
                val axne0 =
                  let
                    val hz = Thm.assume (ctermS2 (jT (oeq ax ZeroC)));  (* ax = 0 *)
                    (* p*y = ax + 1 = 0 + 1 = 1  via hR + rewrite ax->0 *)
                    val rw = add_cong_lS (ax, ZeroC, oneC) hz;     (* (ax + 1) = (0 + 1) *)
                    val z1 = add0S_at oneC;                        (* (0 + 1) = 1 *)
                    val py1 = oeq_trans OF [oeq_trans OF [hR, rw], z1];  (* p*y = 1 = Suc 0 *)
                    (* p divides p*y = 1 ; but dvd p 1 forces p <= 1 (dvd_le),
                       contradicting prime p's 1 < p. *)
                    val dvdp_py = dvd_introS (pF, mult pF yW, yW) (oeqreflS_at (mult pF yW)); (* dvd p (p*y) *)
                    val dvdp_1  = dvd_cong_rS (pF, mult pF yW, oneC) py1 dvdp_py;  (* dvd p 1 *)
                    (* dvd p 1 and 1 != 0 -> le p 1 (dvd_le) *)
                    val one_ne0 =
                      let val h00 = Thm.assume (ctermS2 (jT (oeq oneC ZeroC)))
                      in Thm.implies_intr (ctermS2 (jT (oeq oneC ZeroC))) (Suc_neq_Zero_atS ZeroC OF [h00]) end;
                    val le_p_1  = dvd_le_atS (pF, oneC) dvdp_1 one_ne0;  (* le p 1 *)
                    (* prime p -> lt 1 p = le 2 p ; le p 1 and le 2 p -> le 2 1 (trans) -> contra *)
                    val gt1     = prime2_gt1 pF hPrime;              (* lt 1 p = le 2 p *)
                    val le2_1   = le_trans_atS (suc oneC, pF, oneC) gt1 le_p_1;  (* le (Suc 1) 1 = lt 1 1 *)
                    val contra  = lt_irrefl_atS oneC le2_1;          (* oFalse *)
                    val metaNe  = Thm.implies_intr (ctermS2 (jT (oeq ax ZeroC))) contra;  (* jT(oeq ax 0) ==> jT oFalse *)
                  in impI_atS2 (oeq ax ZeroC, oFalseC) metaNe end;   (* jT (neg (oeq ax 0)) = jT (Imp (oeq ax 0) oFalse) *)

                (* ax = Suc k0 *)
                val axSucEx = ne0_suc_atS ax axne0;               (* Ex m. oeq ax (Suc m) *)
                fun axSucBody k0 (hk0 : thm) =                    (* hk0 : oeq ax (Suc k0) *)
                  let
                    (* le y Q  where Q = ax*y = (Suc k0)*y = y + k0*y  via mult_Suc -> le_add *)
                    val ms   = mult_Suc_atS (k0, yW);             (* (Suc k0)*y = y + k0*y *)
                    (* Q = ax*y ; rewrite ax = Suc k0 : ax*y = (Suc k0)*y *)
                    val qcong= mult_cong_lS (ax, suc k0, yW) hk0; (* ax*y = (Suc k0)*y *)
                    val qEq  = oeq_trans OF [qcong, ms];          (* Q = (y + k0*y) *)
                    val leY  = le_add_atS (yW, mult k0 yW);       (* le y (y + k0*y) *)
                    (* rewrite (y + k0*y) back to Q : le y Q. *)
                    val qEqs = oeq_sym OF [qEq];                  (* (y+k0*y) = Q *)
                    val lePabs = Term.lambda (Free("z_le", natT)) (le yW (Free("z_le", natT)));
                    val leYQ = oeq_rewrite_atS (lePabs, add yW (mult k0 yW), Q) qEqs leY;  (* le y Q *)
                    (* le y Q = Ex M. oeq Q (add y M).  exE M : oeq Q (add y M) *)
                    val leAbs = Abs("p", natT, oeq Q (add yW (Bound 0)));
                    fun mbody mW (hm : thm) =                     (* hm : oeq Q (add y M) *)
                      let
                        (* star-eqn : both sides equal 1 + p*Q ; then add_left_cancel p*y -> sq = 1 + p*M *)
                        (* ---- LEFT value : add (p*y) sq = 1 + p*Q ---- *)
                        val L_a = addcommS_at (mult pF yW, sq);          (* (p*y + sq) = (sq + p*y) *)
                        val L_b = add_cong_rS (sq, mult pF yW, add ax oneC) hR;  (* (sq + p*y) = (sq + (ax+1)) *)
                        val L_c = oeq_sym OF [addassocS_at (sq, ax, oneC)];      (* (sq + (ax+1)) = ((sq+ax)+1) *)
                        val L_d = add_cong_lS (add sq ax, mult pF Q, oneC) iEq;  (* ((sq+ax)+1) = ((p*Q)+1) *)
                        val L_e = addcommS_at (mult pF Q, oneC);                 (* ((p*Q)+1) = (1 + p*Q) *)
                        val Lval = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [L_a, L_b], L_c], L_d], L_e]; (* (p*y + sq) = (1 + p*Q) *)
                        (* ---- RIGHT value : add (p*y) (add 1 (p*M)) = 1 + p*Q ---- *)
                        val R_a = addcommS_at (mult pF yW, add oneC (mult pF mW));  (* (p*y + (1 + p*M)) = ((1 + p*M) + p*y) *)
                        val R_b = addassocS_at (oneC, mult pF mW, mult pF yW);      (* ((1 + p*M) + p*y) = (1 + (p*M + p*y)) *)
                        val R_c = add_cong_rS (oneC, add (mult pF mW) (mult pF yW), add (mult pF yW) (mult pF mW))
                                    (addcommS_at (mult pF mW, mult pF yW));        (* (1 + (p*M + p*y)) = (1 + (p*y + p*M)) *)
                        val ld  = left_distrib_atS (pF, yW, mW);                   (* p*(y+M) = (p*y + p*M) *)
                        val pQeq= mult_cong_rS (pF, Q, add yW mW) hm;             (* p*Q = p*(y+M) *)
                        val pyM_pQ = oeq_sym OF [oeq_trans OF [pQeq, ld]];        (* (p*y + p*M) = p*Q *)
                        val R_d = add_cong_rS (oneC, add (mult pF yW) (mult pF mW), mult pF Q) pyM_pQ;  (* (1 + (p*y+p*M)) = (1 + p*Q) *)
                        val Rval = oeq_trans OF [oeq_trans OF [oeq_trans OF [R_a, R_b], R_c], R_d];  (* (p*y + (1+p*M)) = (1 + p*Q) *)
                        (* combine : (p*y + sq) = (p*y + (1+p*M)) *)
                        val both = oeq_trans OF [Lval, oeq_sym OF [Rval]];        (* (p*y + sq) = (p*y + (1 + p*M)) *)
                        val sqEq = add_left_cancel_atS (mult pF yW, sq, add oneC (mult pF mW)) both;  (* oeq sq (add 1 (p*M)) *)
                        (* a*bWit = sq (eq_ab) ; so oeq (a*bWit) (add 1 (p*M)) *)
                        val abEq = oeq_trans OF [eq_ab, sqEq];                    (* oeq (a*bWit) (add 1 (p*M)) *)
                        (* congR p (a*bWit) 1 : Ex k. oeq (a*bWit) (add 1 (mult p k)), witness M *)
                        val congRabs = Abs("k", natT, oeq (mult aF bWit) (add oneC (mult pF (Bound 0))));
                        val exCongR  = exI_atS2 congRabs mW abEq;                 (* congR p (a*bWit) 1 *)
                        val hcong    = disjI2S2_at (congL pF (mult aF bWit) oneC, congR pF (mult aF bWit) oneC) exCongR;
                        val res      = mi_mkGoal (pF, aF) bWit hcong;            (* Ex b. cong p (a*b) 1 *)
                      in res end;
                    val res = exE_elimS2 (leAbs, goalC) leYQ "M_mi" mbody;
                  in res end;
                val res = exE_elimS2 (Abs("m", natT, oeq ax (suc (Bound 0))), goalC) axSucEx "k0_mi" axSucBody;
              in Thm.implies_intr (ctermS2 (jT dR)) res end;

            val res = disjE_elimS2 (dL, dR, goalC) hDisj caseL caseR;
          in res end;
        val g = exE_elimS2 (cb_innerAbs (aF, pF, xW), goalC) hExY "y_mi" ybody;
      in g end;
    val bodyGoal = exE_elimS2 (cb_outerAbs (aF, pF), goalC) cbDisjEx "x_mi" xbody;
    (* discharge the two hypotheses -> meta implications *)
    val disch1 = Thm.implies_intr (ctermS2 hNdvdP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 (jT (prime2 pF))) disch1;
  in varify disch2 end;

val () = out "MOD_INVERSE_PROVED\n";

(* ---- validation ---- *)
val pVmi = Var (("p",0), natT);
val aVmi = Var (("a",0), natT);
val mod_inverse_intended =
  Logic.mk_implies (jT (prime2 pVmi),
    Logic.mk_implies (jT (neg (dvd pVmi aVmi)),
      jT (mi_goal (pVmi, aVmi))));
val r_mi = checkS2 ("mod_inverse", mod_inverse, mod_inverse_intended);
val () = if r_mi then out "OK mod_inverse\n" else out "FAIL mod_inverse\n";

val probe_mi =
  let
    (* dropping the ~(p|a) hypothesis is false (a=0 has no inverse). *)
    val bogus = Logic.mk_implies (jT (prime2 pVmi), jT (mi_goal (pVmi, aVmi)));
  in not ((Thm.prop_of mod_inverse) aconv bogus) end;
val () = if r_mi andalso probe_mi then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";
val () = if r_mi andalso probe_mi then out "MOD_INVERSE_OK\n" else out "MOD_INVERSE_FAILED\n";
