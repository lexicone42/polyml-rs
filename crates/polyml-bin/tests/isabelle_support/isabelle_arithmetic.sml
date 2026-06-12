(* ============================================================================
   PEANO ARITHMETIC BASE LIBRARY on Isabelle/Pure (Rust PolyML interpreter)
   ============================================================================ *)

(* ---- PRELUDE: declare the object logic ---------------------------------- *)
val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global [(Binding.name "o",0,NoSyn),(Binding.name "nat",0,NoSyn)] thy0;
val oN = Sign.full_name thy1 (Binding.name "o");  val natN = Sign.full_name thy1 (Binding.name "nat");
val oT = Type (oN,[]);  val natT = Type (natN,[]);
val thy2 = Sign.add_consts
  [(Binding.name "Trueprop", oT --> propT, NoSyn),
   (Binding.name "Zero", natT, NoSyn),
   (Binding.name "Suc", natT --> natT, NoSyn),
   (Binding.name "add", natT --> natT --> natT, NoSyn),
   (Binding.name "oeq", natT --> natT --> oT, NoSyn)] thy1;
fun cnst nm T = Const (Sign.full_name thy2 (Binding.name nm), T);
val TP   = cnst "Trueprop" (oT --> propT);   fun jT t = TP $ t;
val ZeroC= cnst "Zero" natT;
val SucC = cnst "Suc" (natT --> natT);       fun suc t = SucC $ t;
val addC = cnst "add" (natT --> natT --> natT); fun add a b = addC $ a $ b;
val oeqC = cnst "oeq" (natT --> natT --> oT);   fun oeq a b = oeqC $ a $ b;
val predT = natT --> oT;
val a = Free ("a",natT); val b = Free ("b",natT); val n = Free ("n",natT); val m = Free ("m",natT);
val P = Free ("P", predT);
(* equality: refl + subst (subst gives sym/trans/congruence) *)
val ((_,oeq_refl),  t3) = Thm.add_axiom_global (Binding.name "oeq_refl",  jT (oeq a a)) thy2;
val ((_,oeq_subst), t4) = Thm.add_axiom_global (Binding.name "oeq_subst",
      Logic.mk_implies (jT (oeq a b), Logic.mk_implies (jT (P $ a), jT (P $ b)))) t3;
(* add recursion equations (recursion on the 1st arg) *)
val ((_,add_0),   t5) = Thm.add_axiom_global (Binding.name "add_0",   jT (oeq (add ZeroC n) n)) t4;
val ((_,add_Suc), t6) = Thm.add_axiom_global (Binding.name "add_Suc",
      jT (oeq (add (suc m) n) (suc (add m n)))) t5;
(* INDUCTION:  P 0 ==> (!!x. P x ==> P (Suc x)) ==> P k *)
val k = Free ("k", natT); val x = Free ("x", natT);
val induct_prop = Logic.mk_implies (jT (P $ ZeroC),
      Logic.mk_implies (Logic.all x (Logic.mk_implies (jT (P $ x), jT (P $ (suc x)))), jT (P $ k)));
val ((_,nat_induct), thy) = Thm.add_axiom_global (Binding.name "nat_induct", induct_prop) t6;
val ctxt = Proof_Context.init_global thy;
(* helpers: varify a Free-carrying axiom to schematic; beta-normalise after elim *)
fun varify th = Drule.zero_var_indexes (Drule.export_without_context th);
fun beta_norm th = Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;
(* end prelude *)

val cterm = Thm.cterm_of ctxt;
(* schematic forms of the axioms (?a ?b ?P ?n ?m ?k at index 0) *)
val oeq_refl_v  = varify oeq_refl;     (* oeq ?a ?a *)
val oeq_subst_v = varify oeq_subst;    (* oeq ?a ?b ==> P ?a ==> P ?b *)
val add_0_v     = varify add_0;        (* oeq (add Zero ?n) ?n *)
val add_Suc_v   = varify add_Suc;      (* oeq (add (Suc ?m) ?n) (Suc (add ?m ?n)) *)
val nat_induct_v= varify nat_induct;   (* P ?Zero ==> (!!x. P x ==> P (Suc x)) ==> P ?k *)

(* ----------------------------------------------------------------------------
   oeq_sym : oeq a b ==> oeq b a
   -------------------------------------------------------------------------- *)
val oeq_sym =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (Bound 0) aF);                 (* %z. oeq z a *)
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
                                              (* oeq a b ==> oeq a a ==> oeq b a *)
    val refl_aa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm aF)] oeq_refl_v);
    val step = inst OF [Thm.assume (cterm (jT (oeq aF bF))), refl_aa];
  in varify (Thm.implies_intr (cterm (jT (oeq aF bF))) step) end;
val () = out ("OK oeq_sym       : " ^ Thm.string_of_thm ctxt oeq_sym ^ "\n");

(* ----------------------------------------------------------------------------
   oeq_trans : oeq a b ==> oeq b c ==> oeq a c
   -------------------------------------------------------------------------- *)
val oeq_trans =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val cF = Free("c",natT);
    val Pabs = Abs("z", natT, oeq aF (Bound 0));                 (* %z. oeq a z *)
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm bF), (("b",0), cterm cF)] oeq_subst_v);
                                              (* oeq b c ==> oeq a b ==> oeq a c *)
    val H1 = Thm.assume (cterm (jT (oeq aF bF)));
    val H2 = Thm.assume (cterm (jT (oeq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (cterm (jT (oeq bF cF))) step;
    val t1 = Thm.implies_intr (cterm (jT (oeq aF bF))) t0;
  in varify t1 end;
val () = out ("OK oeq_trans     : " ^ Thm.string_of_thm ctxt oeq_trans ^ "\n");

(* ----------------------------------------------------------------------------
   Suc_cong : oeq a b ==> oeq (Suc a) (Suc b)
   -------------------------------------------------------------------------- *)
val Suc_cong =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (suc aF) (suc (Bound 0)));     (* %z. oeq (Suc a) (Suc z) *)
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
    val refl_SaSa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (suc aF))] oeq_refl_v);
    val H1 = Thm.assume (cterm (jT (oeq aF bF)));
    val step = inst OF [H1, refl_SaSa];
    val t0 = Thm.implies_intr (cterm (jT (oeq aF bF))) step;
  in varify t0 end;
val () = out ("OK Suc_cong      : " ^ Thm.string_of_thm ctxt Suc_cong ^ "\n");

(* convenience: instantiate the add equations at ground terms *)
fun add0_at t        = beta_norm (Drule.infer_instantiate ctxt [(("n",0), cterm t)] add_0_v);
fun addSuc_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxt
                          [(("m",0), cterm mt),(("n",0), cterm nt)] add_Suc_v);

(* ----------------------------------------------------------------------------
   add_0_right : oeq (add n Zero) n          *** BY INDUCTION on n ***
   -------------------------------------------------------------------------- *)
val add_0_right =
  let
    val Qpred = Abs("z", natT, oeq (add (Bound 0) ZeroC) (Bound 0));
    val nF = Free("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm nF)] nat_induct_v);
    val base = add0_at ZeroC;                                  (* oeq (add 0 0) 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add xF ZeroC) xF);
    val IH = Thm.assume (cterm ihprop);
    val aS = addSuc_at (xF, ZeroC);                            (* oeq (add (Suc x) 0) (Suc (add x 0)) *)
    val sc = Suc_cong OF [IH];                                 (* oeq (Suc (add x 0)) (Suc x) *)
    val stepconcl = oeq_trans OF [aS, sc];                     (* oeq (add (Suc x) 0) (Suc x) *)
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val () = out ("OK add_0_right   : " ^ Thm.string_of_thm ctxt add_0_right ^ "\n");

(* ----------------------------------------------------------------------------
   add_Suc_right : oeq (add m (Suc n)) (Suc (add m n))   *** BY INDUCTION on m ***
   -------------------------------------------------------------------------- *)
val add_Suc_right =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT, oeq (add (Bound 0) (suc nF)) (suc (add (Bound 0) nF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm mF)] nat_induct_v);
    val b1 = add0_at (suc nF);                                 (* oeq (add 0 (Suc n)) (Suc n) *)
    val b2 = add0_at nF;                                       (* oeq (add 0 n) n *)
    val b2s = Suc_cong OF [b2];                                (* oeq (Suc (add 0 n)) (Suc n) *)
    val b2ssym = oeq_sym OF [b2s];                             (* oeq (Suc n) (Suc (add 0 n)) *)
    val base = oeq_trans OF [b1, b2ssym];                      (* oeq (add 0 (Suc n)) (Suc (add 0 n)) *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add xF (suc nF)) (suc (add xF nF)));
    val IH = Thm.assume (cterm ihprop);
    val s1 = addSuc_at (xF, suc nF);                           (* oeq (add (Suc x)(Suc n)) (Suc (add x (Suc n))) *)
    val s2 = Suc_cong OF [IH];                                 (* oeq (Suc (add x (Suc n))) (Suc (Suc (add x n))) *)
    val s3 = addSuc_at (xF, nF);                               (* oeq (add (Suc x) n) (Suc (add x n)) *)
    val s3s = Suc_cong OF [s3];                                (* oeq (Suc (add (Suc x) n)) (Suc (Suc (add x n))) *)
    val s3ssym = oeq_sym OF [s3s];                             (* oeq (Suc (Suc (add x n))) (Suc (add (Suc x) n)) *)
    val c12 = oeq_trans OF [s1, s2];                           (* oeq (add (Suc x)(Suc n)) (Suc (Suc (add x n))) *)
    val stepconcl = oeq_trans OF [c12, s3ssym];                (* oeq (add (Suc x)(Suc n)) (Suc (add (Suc x) n)) *)
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val () = out ("OK add_Suc_right : " ^ Thm.string_of_thm ctxt add_Suc_right ^ "\n");

(* ---- final audit: every result must be a checked 0-hyp theorem ---- *)
fun audit (nm, th) =
  let val ph = length (Thm.hyps_of th) in
    out (nm ^ ": hyps=" ^ Int.toString ph ^ " (theorem, sound)\n")
  end;
val () = audit ("oeq_sym",       oeq_sym);
val () = audit ("oeq_trans",     oeq_trans);
val () = audit ("Suc_cong",      Suc_cong);
val () = audit ("add_0_right",   add_0_right);
val () = audit ("add_Suc_right", add_Suc_right);
val () = out ("ALL OK - Peano arithmetic base library proved (5/5)\n");

(* ============================================================================
   MY PROOF:  add_comm : oeq (add m n) (add n m)     *** BY INDUCTION on m ***
   ----------------------------------------------------------------------------
   n is held fixed (a Free parameter). Q := %z. oeq (add z n) (add n z).
   Instantiate nat_induct at P:=Q, k:=m.
     BASE : oeq (add 0 n) (add n 0)
       add_0[n]              : oeq (add 0 n) n
       add_0_right[n]        : oeq (add n 0) n   -> sym -> oeq n (add n 0)
       trans                : oeq (add 0 n) (add n 0)
     STEP : assume IH oeq (add x n) (add n x);
       add_Suc[x,n]          : oeq (add (Suc x) n) (Suc (add x n))
       Suc_cong IH           : oeq (Suc (add x n)) (Suc (add n x))
       add_Suc_right[n,x]    : oeq (add n (Suc x)) (Suc (add n x)) -> sym
                              : oeq (Suc (add n x)) (add n (Suc x))
       chain by trans        : oeq (add (Suc x) n) (add n (Suc x))
   Discharge the two induction premises with kernel implies_elim.
   ============================================================================ *)

(* convenience: instantiate the library add_0_right / add_Suc_right at terms *)
val add_0_right_v   = varify add_0_right;     (* oeq (add ?n Zero) ?n *)
val add_Suc_right_v = varify add_Suc_right;   (* oeq (add ?m (Suc ?n)) (Suc (add ?m ?n)) *)
fun add0r_at t        = beta_norm (Drule.infer_instantiate ctxt [(("n",0), cterm t)] add_0_right_v);
fun addSr_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxt
                          [(("m",0), cterm mt),(("n",0), cterm nt)] add_Suc_right_v);

val add_comm =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT, oeq (add (Bound 0) nF) (add nF (Bound 0)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm mF)] nat_induct_v);
    (* BASE : oeq (add 0 n) (add n 0) *)
    val b1 = add0_at nF;                                       (* oeq (add 0 n) n *)
    val b2 = add0r_at nF;                                      (* oeq (add n 0) n *)
    val b2sym = oeq_sym OF [b2];                               (* oeq n (add n 0) *)
    val base = oeq_trans OF [b1, b2sym];                       (* oeq (add 0 n) (add n 0) *)
    (* STEP *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add xF nF) (add nF xF));
    val IH = Thm.assume (cterm ihprop);
    val s1 = addSuc_at (xF, nF);                               (* oeq (add (Suc x) n) (Suc (add x n)) *)
    val s2 = Suc_cong OF [IH];                                 (* oeq (Suc (add x n)) (Suc (add n x)) *)
    val s3 = addSr_at (nF, xF);                                (* oeq (add n (Suc x)) (Suc (add n x)) *)
    val s3sym = oeq_sym OF [s3];                               (* oeq (Suc (add n x)) (add n (Suc x)) *)
    val c12 = oeq_trans OF [s1, s2];                           (* oeq (add (Suc x) n) (Suc (add n x)) *)
    val stepconcl = oeq_trans OF [c12, s3sym];                 (* oeq (add (Suc x) n) (add n (Suc x)) *)
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val () = out ("OK add_comm      : " ^ Thm.string_of_thm ctxt add_comm ^ "\n");
val () = audit ("add_comm", add_comm);
val () = out ("OK add_comm\n");

(* ===== add_assoc (proof-part, on the shared library above) ===== *)

(* ---- final audit ---- *)
fun audit (nm, th) =
  let val ph = length (Thm.hyps_of th) in
    out (nm ^ ": hyps=" ^ Int.toString ph ^ " (theorem, sound)\n")
  end;
val () = audit ("oeq_sym",       oeq_sym);
val () = audit ("oeq_trans",     oeq_trans);
val () = audit ("Suc_cong",      Suc_cong);
val () = audit ("add_0_right",   add_0_right);
val () = audit ("add_Suc_right", add_Suc_right);
val () = out ("ALL OK - Peano arithmetic base library proved (5/5)\n");

(* ============================================================================
   MY PROOF: add_assoc : oeq (add (add m n) k) (add m (add n k))
   *** BY INDUCTION on m *** (n and k held fixed as Free parameters)
   Q := %z. oeq (add (add z n) k) (add z (add n k)).
   ============================================================================ *)

(* add-congruence on the LEFT operand (constant second operand k):
   oeq p q ==> oeq (add p k) (add q k), via oeq_subst with P := %z. oeq (add p k) (add z k) *)
fun add_cong_l_at (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));   (* %z. oeq (add p k) (add z k) *)
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm pT), (("b",0), cterm qT)] oeq_subst_v);
                                          (* oeq p q ==> oeq (add p k) (add p k) ==> oeq (add p k) (add q k) *)
    val refl_pk = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (add pT kT))] oeq_refl_v);
  in inst OF [hpq, refl_pk] end;

val add_assoc =
  let
    val nF = Free("n", natT); val kF = Free("k", natT);
    val Qpred = Abs("z", natT,
        oeq (add (add (Bound 0) nF) kF) (add (Bound 0) (add nF kF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm mF)] nat_induct_v);
    (* BASE : oeq (add (add 0 n) k) (add 0 (add n k)) *)
    val a0n = add0_at nF;                                      (* oeq (add 0 n) n *)
    val L1  = add_cong_l_at (add ZeroC nF, nF, kF) a0n;        (* oeq (add (add 0 n) k) (add n k) *)
    val R1  = add0_at (add nF kF);                             (* oeq (add 0 (add n k)) (add n k) *)
    val R1s = oeq_sym OF [R1];                                 (* oeq (add n k) (add 0 (add n k)) *)
    val base = oeq_trans OF [L1, R1s];                         (* oeq (add (add 0 n) k) (add 0 (add n k)) *)
    (* STEP *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add (add xF nF) kF) (add xF (add nF kF)));
    val IH = Thm.assume (cterm ihprop);
    val e1  = addSuc_at (xF, nF);                              (* oeq (add (Suc x) n) (Suc (add x n)) *)
    val e1c = add_cong_l_at (add (suc xF) nF, suc (add xF nF), kF) e1;
                                                               (* oeq (add (add (Suc x) n) k) (add (Suc (add x n)) k) *)
    val e2  = addSuc_at (add xF nF, kF);                       (* oeq (add (Suc (add x n)) k) (Suc (add (add x n) k)) *)
    val e3  = Suc_cong OF [IH];                                (* oeq (Suc (add (add x n) k)) (Suc (add x (add n k))) *)
    val e4  = addSuc_at (xF, add nF kF);                       (* oeq (add (Suc x) (add n k)) (Suc (add x (add n k))) *)
    val e4s = oeq_sym OF [e4];                                 (* oeq (Suc (add x (add n k))) (add (Suc x) (add n k)) *)
    val c1  = oeq_trans OF [e1c, e2];                          (* oeq (add (add (Suc x) n) k) (Suc (add (add x n) k)) *)
    val c2  = oeq_trans OF [c1, e3];                           (* oeq (add (add (Suc x) n) k) (Suc (add x (add n k))) *)
    val stepconcl = oeq_trans OF [c2, e4s];                    (* oeq (add (add (Suc x) n) k) (add (Suc x) (add n k)) *)
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val () = out ("OK add_assoc     : " ^ Thm.string_of_thm ctxt add_assoc ^ "\n");
val () = audit ("add_assoc", add_assoc);
val () = out ("OK add_assoc\n");

(* ===== multiplication: mult_0_right (proof-part) ===== *)

(* ---- library audit ---- *)
fun audit (nm, th) =
  let val ph = length (Thm.hyps_of th) in
    out (nm ^ ": hyps=" ^ Int.toString ph ^ " (theorem, sound)\n")
  end;
val () = audit ("oeq_sym",       oeq_sym);
val () = audit ("oeq_trans",     oeq_trans);
val () = audit ("Suc_cong",      Suc_cong);
val () = audit ("add_0_right",   add_0_right);
val () = audit ("add_Suc_right", add_Suc_right);
val () = out ("ALL OK - Peano arithmetic base library proved (5/5)\n");

(* ============================================================================
   ============================  MY PROOF: mult  ==============================
   Introduce MULTIPLICATION as a second operation, recursion on the 1st arg:
     mult_0   : oeq (mult Zero n) Zero
     mult_Suc : oeq (mult (Suc m) n) (add n (mult m n))
   then prove
     mult_0_right : oeq (mult n Zero) Zero          *** BY INDUCTION on n ***
   ============================================================================ *)

(* Declare the new const `mult` on the current theory `thy`. *)
val thyM = Sign.add_consts
  [(Binding.name "mult", natT --> natT --> natT, NoSyn)] thy;
val multC = Const (Sign.full_name thyM (Binding.name "mult"), natT --> natT --> natT);
fun mult s t = multC $ s $ t;

(* mult recursion equations (recursion on the 1st arg).  Use Frees m,n. *)
val ((_,mult_0),   tM1) = Thm.add_axiom_global (Binding.name "mult_0",
      jT (oeq (mult ZeroC n) ZeroC)) thyM;
val ((_,mult_Suc), tM2) = Thm.add_axiom_global (Binding.name "mult_Suc",
      jT (oeq (mult (suc m) n) (add n (mult m n)))) tM1;

(* Re-init the proof context on the extended theory, and rebuild the helpers
   that depend on `cterm`/`ctxt` so everything is on the SAME theory. *)
val ctxtM   = Proof_Context.init_global tM2;
val ctermM  = Thm.cterm_of ctxtM;

(* schematic forms of the mult axioms (?n at index 0; ?m ?n at index 0) *)
val mult_0_v   = varify mult_0;     (* oeq (mult Zero ?n) Zero *)
val mult_Suc_v = varify mult_Suc;   (* oeq (mult (Suc ?m) ?n) (add ?n (mult ?m ?n)) *)

(* instantiate the mult equations at ground terms *)
fun mult0_at t         = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] mult_0_v);
fun multSuc_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtM
                            [(("m",0), ctermM mt),(("n",0), ctermM nt)] mult_Suc_v);
(* re-instantiate add_0 at a ground term on the extended theory *)
fun add0M_at t = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] add_0_v);

(* ----------------------------------------------------------------------------
   mult_0_right : oeq (mult n Zero) Zero          *** BY INDUCTION on n ***
   Q := %z. oeq (mult z Zero) Zero.  Instantiate nat_induct at P:=Q, k:=n.
     BASE : mult_0[?n:=0]                          gives oeq (mult 0 0) 0.
     STEP : assume IH oeq (mult x 0) 0;
            mult_Suc[x,0] : oeq (mult (Suc x) 0) (add 0 (mult x 0));
            add_0[mult x 0] : oeq (add 0 (mult x 0)) (mult x 0);
            chain twice by oeq_trans, then with IH:
              oeq (mult (Suc x) 0) (add 0 (mult x 0))   (mult_Suc)
              oeq (add 0 (mult x 0)) (mult x 0)         (add_0)
              oeq (mult x 0) 0                          (IH)
            =>  oeq (mult (Suc x) 0) 0.
   Discharge the induction premises with kernel implies_elim.
   -------------------------------------------------------------------------- *)
val mult_0_right =
  let
    val Qpred = Abs("z", natT, oeq (mult (Bound 0) ZeroC) ZeroC);
    val nF = Free("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM nF)] nat_induct_v);
    (* BASE : oeq (mult 0 0) 0 *)
    val base = mult0_at ZeroC;
    (* STEP *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult xF ZeroC) ZeroC);
    val IH = Thm.assume (ctermM ihprop);
    val mS = multSuc_at (xF, ZeroC);                  (* oeq (mult (Suc x) 0) (add 0 (mult x 0)) *)
    val a0 = add0M_at (mult xF ZeroC);                (* oeq (add 0 (mult x 0)) (mult x 0) *)
    val c1 = oeq_trans OF [mS, a0];                   (* oeq (mult (Suc x) 0) (mult x 0) *)
    val stepconcl = oeq_trans OF [c1, IH];            (* oeq (mult (Suc x) 0) 0 *)
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val () = out ("mult_0_right     : " ^ Thm.string_of_thm ctxtM mult_0_right ^ "\n");
val () = audit ("mult_0_right", mult_0_right);
val () = (if length (Thm.hyps_of mult_0_right) = 0 then out "OK mult\n" else out "FAIL mult: hyps remain\n");

val () = out "ISA_ARITH_DONE\n";
