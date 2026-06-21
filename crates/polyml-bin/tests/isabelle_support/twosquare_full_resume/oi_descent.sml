(* ============================================================================
   THE DESCENT (only-if core).  Fixed p with prime2 p and Ex k. p = 4k+3.
   Prove (by strong_induct on n) :  Pred n  where
     Pred n = Imp (Conj (lt 0 n) (Ex a b. n = a*a + b*b))
                  (Ex v m. Conj (oeq n (mult (pow p v) m))
                                (Conj (neg (dvd p m)) (Ex j. oeq v (add j j))))
   ============================================================================ *)
val () = out "OI_DESCENT_BEGIN\n";

val key_onlyif_v = varify key_onlyif;   (* schematic p,a,b *)
fun key_onlyif_at (pT, aT, bT) hPrime h4k3 hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT), (("a",0), ctermSub aT), (("b",0), ctermSub bT)] key_onlyif_v)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPrime) h4k3) hDvd end;

(* fixed p *)
val pp_free = Free("p", natT);
val hPrimeP = jT (prime2 pp_free);
val hPrime  = Thm.assume (ctermSub hPrimeP);
val h4k3body = Abs("k", natT, oeq pp_free (add (add (add (add (Bound 0)(Bound 0))(Bound 0))(Bound 0)) (suc (suc (suc ZeroC)))));
val h4k3P   = jT (mkEx h4k3body);
val h4k3    = Thm.assume (ctermSub h4k3P);

(* the two-square existential body : %n. Ex a. Ex b. oeq n (add (a*a)(b*b)) *)
fun sumsqBody nT = mkEx (Abs("a", natT, mkEx (Abs("b", natT,
                     oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0)))))));
(* the conclusion body : %n. Ex v. Ex m. Conj (oeq n (pow p v * m)) (Conj (neg(dvd p m)) (Ex j. oeq v (j+j)))
   Built capture-safely with fresh Frees + Term.lambda (dvd p _ inserts its own inner Abs("k"),
   so a literal Bound 0 for m would be captured by k -- the documented gotcha). *)
val vFr0 = Free("vcb", natT);
val mFr0 = Free("mcb", natT);
fun cbInner nT (vT, mT) =
      mkConj (oeq nT (mult (pow pp_free vT) mT))
             (mkConj (neg (dvd pp_free mT))
                     (mkEx (Abs("j", natT, oeq vT (add (Bound 0)(Bound 0))))));
fun conclBody nT = mkEx (Term.lambda vFr0 (mkEx (Term.lambda mFr0 (cbInner nT (vFr0, mFr0)))));
fun predBody nT = mkImp (mkConj (lt ZeroC nT) (sumsqBody nT)) (conclBody nT);

val () = out "OI_DESCENT_TERMS_OK\n";

(* helper: dvd-extract.  from hDvd : jT (dvd p x) and a goal G, body fn (w, hw: oeq x (p*w)) -> G,
   produce G via exESub_elim on the dvd existential. *)
fun dvd_extract (pT, xT) hDvd goalC wName bodyFn =
  let val Pabs = Abs("k", natT, oeq xT (mult pT (Bound 0)))
  in exESub_elim (Pabs, goalC) hDvd wName bodyFn end;

(* mult_1_left on Sub already: mult1lSub_at t : oeq (mult (Suc 0) t) t. pow p 0 = Suc 0. *)

(* ---- the strong-induction step ---- *)
val nStep = Free("n", natT);
val GpropMeta = Logic.all (Free("m",natT))
      (Logic.mk_implies (jT (lt (Free("m",natT)) nStep), jT (predBody (Free("m",natT)))));
(* IH as an assumed meta-thm *)
val IHbox = Thm.assume (ctermSub GpropMeta);
fun applyIH mT (ltThm : thm) =          (* ltThm : jT (lt m n) -> returns jT (predBody m) *)
  let val spec = Thm.forall_elim (ctermSub mT) IHbox        (* lt m n ==> jT(predBody m) *)
  in Thm.implies_elim spec ltThm end;

(* assume the precondition Hpre = Conj (lt 0 n)(sumsqBody n) ; build conclBody n *)
val HpreT = mkConj (lt ZeroC nStep) (sumsqBody nStep);
val Hpre  = Thm.assume (ctermSub (jT HpreT));
val hPos  = conjunct1_atSub (lt ZeroC nStep, sumsqBody nStep) Hpre;   (* jT (lt 0 n) *)
val hSS   = conjunct2_atSub (lt ZeroC nStep, sumsqBody nStep) Hpre;   (* jT (sumsqBody n) *)

val () = out "OI_STEP_SETUP_OK\n";

(* ---- build_concl : capture-safe assembly of jT (conclBody nStep) from witnesses + facts.
   uses the SAME fresh Frees (vFr0,mFr0) as conclBody so the result is aconv conclBody nStep. *)
fun build_concl (vWit, mWit, hEqn, hNdvd, hEvenEx) =
  let
    val evenBody = Abs("j", natT, oeq vWit (add (Bound 0)(Bound 0)));
    val innerC   = mkConj (neg (dvd pp_free mWit)) (mkEx evenBody);
    val conj2    = conjI_atSub (neg (dvd pp_free mWit), mkEx evenBody) hNdvd hEvenEx;
    val outerA   = oeq nStep (mult (pow pp_free vWit) mWit);
    val conj1    = conjI_atSub (outerA, innerC) hEqn conj2;             (* jT (cbInner n (vWit,mWit)) *)
    val PabsM    = Term.lambda mFr0 (cbInner nStep (vWit, mFr0));       (* %m. cbInner n (vWit,m) *)
    val exM      = exISub_at PabsM mWit conj1;                          (* Ex m. cbInner n (vWit,m) *)
    val PabsV    = Term.lambda vFr0 (mkEx (Term.lambda mFr0 (cbInner nStep (vFr0, mFr0))));
    val exV      = exISub_at PabsV vWit exM;                            (* jT (conclBody n) *)
  in exV end;

(* ============ CASE B : ~(p|n) -> v=0, m=n ============ *)
val caseB_arm =
  let
    val hNdP = jT (neg (dvd pp_free nStep));
    val hNd  = Thm.assume (ctermSub hNdP);
    (* oeq n (mult (pow p 0) n) *)
    val pz   = powZeroS2_at pp_free;
    val cz   = mult_cong_lS2 (pow pp_free ZeroC, suc ZeroC, nStep) pz;
    val m1   = mult1lSub_at nStep;
    val eqn  = oeq_sym OF [oeq_trans OF [cz, m1]];          (* oeq n (mult (pow p 0) n) *)
    (* Ex j. oeq 0 (add j j) : j=0 *)
    val a00  = add0S2_at ZeroC;
    val ev0  = oeq_sym OF [a00];                            (* oeq 0 (add 0 0) *)
    val evJabs = Abs("j", natT, oeq ZeroC (add (Bound 0)(Bound 0)));
    val evEx = exISub_at evJabs ZeroC ev0;                  (* jT (Ex j. oeq 0 (add j j)) *)
    val exV  = build_concl (ZeroC, nStep, eqn, hNd, evEx);  (* jT (conclBody n) *)
    val metaImp = Thm.implies_intr (ctermSub hNdP) exV;     (* (jT (neg(dvd p n))) ==> jT (conclBody n) *)
  in impI_S2 (neg (dvd pp_free nStep), conclBody nStep) metaImp end;  (* jT (Imp (neg(dvd p n))(conclBody n)) *)

val () = out ("OI_CASEB_OK aconv-impl="^
  Bool.toString ((Thm.prop_of caseB_arm) aconv (jT (mkImp (neg (dvd pp_free nStep)) (conclBody nStep))))^"\n");
