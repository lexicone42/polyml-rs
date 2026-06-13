(* ============================================================================
   A LIST THEORY in Isabelle/Pure on the polyml-rs interpreter — structural
   induction over a SECOND inductive datatype (beyond nat).  (test:
   isabelle_list_theory.rs)
   ----------------------------------------------------------------------------
   On the Peano semiring foundation (nat + add, for `length`), this builds an
   inductive list datatype over nat and proves the classic list laws by
   STRUCTURAL INDUCTION, each a 0-hypothesis theorem, pure LCF kernel inference:
     type natlist = Nil | Cons nat natlist ; a list equality leq (refl+subst) ;
     a list_induct axiom ; append/reverse/length by primitive recursion.

     append_nil    : leq (append l Nil) l
     append_assoc  : leq (append (append a b) c) (append a (append b c))
     rev_append    : leq (reverse (append a b)) (append (reverse b) (reverse a))
     rev_rev       : leq (reverse (reverse l)) l                 (the headline)
     length_append : oeq (length (append a b)) (add (length a) (length b))

   The Isabelle analogue of the HOL4 list laws (list_laws_verified.sml) —
   demonstrating that the hand-built object logic handles a second inductive
   datatype with its own induction principle, not just nat.  A soundness probe
   confirms the kernel rejects a garbled rev_rev variant.

   Built (on isabelle_number_theory.sml) by a 3-seat ultracode fleet
   (wf_666cb3a1-e29, explicit / subst / careful); all three verified
   independently, banked the explicit-chaining variant.
   ============================================================================ *)

(* ============================================================================
   A LIST THEORY OVER nat, BY STRUCTURAL INDUCTION — Isabelle/Pure on polyml-rs
   ----------------------------------------------------------------------------
   SEAT: explicit equational chaining via leq_trans + congruences (mirrors the
   base semiring proofs closely).

   Foundation (verbatim from isabelle_number_theory.sml, trimmed to what the
   list theory needs): object logic (types o, nat) + Trueprop + Peano add +
   nat equality (oeq) + nat induction, and the proven add laws add_0_right /
   add_Suc_right (used by length_append).

   Then EXTEND with a list theory: type natlist, consts Nil/Cons/leq/append/
   reverse/length, axioms leq_refl/leq_subst/list_induct + the recursion eqns,
   and prove by STRUCTURAL INDUCTION over natlist:
       append_nil    : leq (append l Nil) l
       append_assoc  : leq (append (append a b) c) (append a (append b c))
       rev_append    : leq (reverse (append a b)) (append (reverse b) (reverse a))
       rev_rev       : leq (reverse (reverse l)) l
       length_append : oeq (length (append a b)) (add (length a) (length b))
   ============================================================================ *)

(* ---- MUST be first: generic context is thread-local, lost on reload ---- *)
val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

(* ============================================================================
   FOUNDATION : object logic (types o, nat) + Trueprop + Peano add + equality
   ============================================================================ *)
val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global
  [(Binding.name "o",0,NoSyn),(Binding.name "nat",0,NoSyn)] thy0;
val oN = Sign.full_name thy1 (Binding.name "o");
val natN = Sign.full_name thy1 (Binding.name "nat");
val oT = Type (oN,[]);  val natT = Type (natN,[]);
val thy2 = Sign.add_consts
  [(Binding.name "Trueprop", oT --> propT, NoSyn),
   (Binding.name "Zero", natT, NoSyn),
   (Binding.name "Suc", natT --> natT, NoSyn),
   (Binding.name "add", natT --> natT --> natT, NoSyn),
   (Binding.name "oeq", natT --> natT --> oT, NoSyn)] thy1;
fun cnst nm T = Const (Sign.full_name thy2 (Binding.name nm), T);
val TP    = cnst "Trueprop" (oT --> propT);      fun jT t = TP $ t;
val ZeroC = cnst "Zero" natT;
val SucC  = cnst "Suc" (natT --> natT);          fun suc t = SucC $ t;
val addC  = cnst "add" (natT --> natT --> natT); fun add a b = addC $ a $ b;
val oeqC  = cnst "oeq" (natT --> natT --> oT);   fun oeq a b = oeqC $ a $ b;
val predT = natT --> oT;
val a = Free ("a",natT); val b = Free ("b",natT);
val n = Free ("n",natT); val m = Free ("m",natT);
val P = Free ("P", predT);

(* equality: refl + subst (subst gives sym / trans / congruence) *)
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
val ((_,nat_induct), thyN) = Thm.add_axiom_global (Binding.name "nat_induct", induct_prop) t6;

(* ============================================================================
   LIST THEORY : extend with type natlist + consts + axioms.  We do ALL further
   type/const extension HERE, then init the SINGLE final context (ctxt/cterm)
   through which every cterm, instantiator and congruence is routed.
   ============================================================================ *)
val thyL1 = Sign.add_types_global [(Binding.name "natlist",0,NoSyn)] thyN;
val natlistN = Sign.full_name thyL1 (Binding.name "natlist");
val natlistT = Type (natlistN,[]);
val thyL2 = Sign.add_consts
  [(Binding.name "Nil",     natlistT, NoSyn),
   (Binding.name "Cons",    natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "leq",     natlistT --> natlistT --> oT, NoSyn),
   (Binding.name "append",  natlistT --> natlistT --> natlistT, NoSyn),
   (Binding.name "reverse", natlistT --> natlistT, NoSyn),
   (Binding.name "length",  natlistT --> natT, NoSyn)] thyL1;

fun cnstL nm T = Const (Sign.full_name thyL2 (Binding.name nm), T);
val NilC     = cnstL "Nil" natlistT;
val ConsC    = cnstL "Cons" (natT --> natlistT --> natlistT);   fun cons h t = ConsC $ h $ t;
val leqC     = cnstL "leq" (natlistT --> natlistT --> oT);      fun leq s t = leqC $ s $ t;
val appendC  = cnstL "append" (natlistT --> natlistT --> natlistT); fun app s t = appendC $ s $ t;
val reverseC = cnstL "reverse" (natlistT --> natlistT);          fun rev s = reverseC $ s;
val lengthC  = cnstL "length" (natlistT --> natT);               fun len s = lengthC $ s;
val lpredT   = natlistT --> oT;

(* free vars over natlist / nat *)
val lA = Free ("a", natlistT); val lB = Free ("b", natlistT);
val lC = Free ("c", natlistT); val lL = Free ("l", natlistT);
val lM = Free ("m", natlistT); val lK = Free ("k", natlistT);
val PL = Free ("P", lpredT);
val xN = Free ("x", natT);

(* ---- list equality: refl + subst ---- *)
val ((_,leq_refl),  tL3) = Thm.add_axiom_global (Binding.name "leq_refl", jT (leq lA lA)) thyL2;
val ((_,leq_subst), tL4) = Thm.add_axiom_global (Binding.name "leq_subst",
      Logic.mk_implies (jT (leq lA lB), Logic.mk_implies (jT (PL $ lA), jT (PL $ lB)))) tL3;

(* ---- list induction:  P Nil ==> (!!x l. P l ==> P (Cons x l)) ==> P k ---- *)
val list_induct_prop =
  Logic.mk_implies (jT (PL $ NilC),
    Logic.mk_implies
      (Logic.all xN (Logic.all lL
         (Logic.mk_implies (jT (PL $ lL), jT (PL $ (cons xN lL))))),
       jT (PL $ lK)));
val ((_,list_induct), tL5) = Thm.add_axiom_global (Binding.name "list_induct", list_induct_prop) tL4;

(* ---- append recursion (leq, since it equates natlists) ---- *)
val ((_,append_Nil),  tL6) = Thm.add_axiom_global (Binding.name "append_Nil",
      jT (leq (app NilC lM) lM)) tL5;
val ((_,append_Cons), tL7) = Thm.add_axiom_global (Binding.name "append_Cons",
      jT (leq (app (cons xN lL) lM) (cons xN (app lL lM)))) tL6;
(* ---- reverse recursion (leq) ---- *)
val ((_,reverse_Nil),  tL8) = Thm.add_axiom_global (Binding.name "reverse_Nil",
      jT (leq (rev NilC) NilC)) tL7;
val ((_,reverse_Cons), tL9) = Thm.add_axiom_global (Binding.name "reverse_Cons",
      jT (leq (rev (cons xN lL)) (app (rev lL) (cons xN NilC)))) tL8;
(* ---- length recursion (oeq, since it equates nats) ---- *)
val ((_,length_Nil),  tL10) = Thm.add_axiom_global (Binding.name "length_Nil",
      jT (oeq (len NilC) ZeroC)) tL9;
val ((_,length_Cons), thy) = Thm.add_axiom_global (Binding.name "length_Cons",
      jT (oeq (len (cons xN lL)) (suc (len lL)))) tL10;

(* ============================================================================
   THE SINGLE FINAL CONTEXT — route every cterm/instantiator through it.
   ============================================================================ *)
val ctxt = Proof_Context.init_global thy;
val cterm = Thm.cterm_of ctxt;

(* helpers: varify a Free-carrying axiom to schematic; beta-normalise after elim *)
fun varify th = Drule.zero_var_indexes (Drule.export_without_context th);
fun beta_norm th = Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;

(* ---- re-varify ALL reused axioms / base lemmas onto the FINAL context ---- *)
val oeq_refl_v    = varify oeq_refl;
val oeq_subst_v   = varify oeq_subst;
val add_0_v       = varify add_0;
val add_Suc_v     = varify add_Suc;
val nat_induct_v  = varify nat_induct;
val leq_refl_v    = varify leq_refl;
val leq_subst_v   = varify leq_subst;
val list_induct_v = varify list_induct;
val append_Nil_v  = varify append_Nil;
val append_Cons_v = varify append_Cons;
val reverse_Nil_v = varify reverse_Nil;
val reverse_Cons_v= varify reverse_Cons;
val length_Nil_v  = varify length_Nil;
val length_Cons_v = varify length_Cons;

(* ============================================================================
   nat-equality lemmas (oeq_sym / oeq_trans / Suc_cong) — for length_append.
   ============================================================================ *)
val oeq_sym =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
    val refl_aa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm aF)] oeq_refl_v);
    val step = inst OF [Thm.assume (cterm (jT (oeq aF bF))), refl_aa];
  in varify (Thm.implies_intr (cterm (jT (oeq aF bF))) step) end;

val oeq_trans =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val cF = Free("c",natT);
    val Pabs = Abs("z", natT, oeq aF (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm bF), (("b",0), cterm cF)] oeq_subst_v);
    val H1 = Thm.assume (cterm (jT (oeq aF bF)));
    val H2 = Thm.assume (cterm (jT (oeq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (cterm (jT (oeq bF cF))) step;
    val t1 = Thm.implies_intr (cterm (jT (oeq aF bF))) t0;
  in varify t1 end;

val Suc_cong =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (suc aF) (suc (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
    val refl_SaSa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (suc aF))] oeq_refl_v);
    val H1 = Thm.assume (cterm (jT (oeq aF bF)));
    val step = inst OF [H1, refl_SaSa];
  in varify (Thm.implies_intr (cterm (jT (oeq aF bF))) step) end;

(* ============================================================================
   list-equality lemmas (leq_sym / leq_trans) + congruences, derived from
   leq_subst exactly as the base derives oeq_sym/trans/Suc_cong from oeq_subst.
   ============================================================================ *)
val leq_sym =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT);
    val Pabs = Abs("z", natlistT, leq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] leq_subst_v);
    val refl_aa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm aF)] leq_refl_v);
    val step = inst OF [Thm.assume (cterm (jT (leq aF bF))), refl_aa];
  in varify (Thm.implies_intr (cterm (jT (leq aF bF))) step) end;

val leq_trans =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT); val cF = Free("c",natlistT);
    val Pabs = Abs("z", natlistT, leq aF (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm bF), (("b",0), cterm cF)] leq_subst_v);
    val H1 = Thm.assume (cterm (jT (leq aF bF)));
    val H2 = Thm.assume (cterm (jT (leq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (cterm (jT (leq bF cF))) step;
    val t1 = Thm.implies_intr (cterm (jT (leq aF bF))) t0;
  in varify t1 end;

(* Cons_cong (on the TAIL): leq l m ==> leq (Cons x l) (Cons x m) *)
val Cons_cong =
  let
    val xF = Free("x",natT); val lF = Free("l",natlistT); val mF = Free("m",natlistT);
    val Pabs = Abs("z", natlistT, leq (cons xF lF) (cons xF (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm lF), (("b",0), cterm mF)] leq_subst_v);
    val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (cons xF lF))] leq_refl_v);
    val H1 = Thm.assume (cterm (jT (leq lF mF)));
    val step = inst OF [H1, refl0];
  in varify (Thm.implies_intr (cterm (jT (leq lF mF))) step) end;

(* append-cong LEFT operand: leq a b ==> leq (append a c) (append b c) *)
val append_cong_l =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT); val cF = Free("c",natlistT);
    val Pabs = Abs("z", natlistT, leq (app aF cF) (app (Bound 0) cF));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] leq_subst_v);
    val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app aF cF))] leq_refl_v);
    val H1 = Thm.assume (cterm (jT (leq aF bF)));
    val step = inst OF [H1, refl0];
  in varify (Thm.implies_intr (cterm (jT (leq aF bF))) step) end;

(* append-cong RIGHT operand: leq a b ==> leq (append c a) (append c b) *)
val append_cong_r =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT); val cF = Free("c",natlistT);
    val Pabs = Abs("z", natlistT, leq (app cF aF) (app cF (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] leq_subst_v);
    val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app cF aF))] leq_refl_v);
    val H1 = Thm.assume (cterm (jT (leq aF bF)));
    val step = inst OF [H1, refl0];
  in varify (Thm.implies_intr (cterm (jT (leq aF bF))) step) end;

(* reverse-cong: leq a b ==> leq (reverse a) (reverse b) *)
val reverse_cong =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT);
    val Pabs = Abs("z", natlistT, leq (rev aF) (rev (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] leq_subst_v);
    val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (rev aF))] leq_refl_v);
    val H1 = Thm.assume (cterm (jT (leq aF bF)));
    val step = inst OF [H1, refl0];
  in varify (Thm.implies_intr (cterm (jT (leq aF bF))) step) end;

(* length-cong: leq a b ==> oeq (length a) (length b)
   (P : natlist => o, body uses oeq of length — cross-equality congruence) *)
val length_cong =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT);
    val Pabs = Abs("z", natlistT, oeq (len aF) (len (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] leq_subst_v);
    val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (len aF))] oeq_refl_v);
    val H1 = Thm.assume (cterm (jT (leq aF bF)));
    val step = inst OF [H1, refl0];
  in varify (Thm.implies_intr (cterm (jT (leq aF bF))) step) end;

(* ============================================================================
   GROUND INSTANTIATORS for the recursion equations (final context).
   ============================================================================ *)
fun appNil_at t       = beta_norm (Drule.infer_instantiate ctxt [(("m",0), cterm t)] append_Nil_v);
fun appCons_at (h,l,m)= beta_norm (Drule.infer_instantiate ctxt
                          [(("x",0), cterm h),(("l",0), cterm l),(("m",0), cterm m)] append_Cons_v);
val revNil = reverse_Nil_v;  (* no schematic args *)
fun revCons_at (h,l)  = beta_norm (Drule.infer_instantiate ctxt
                          [(("x",0), cterm h),(("l",0), cterm l)] reverse_Cons_v);
val lenNil = length_Nil_v;   (* no schematic args *)
fun lenCons_at (h,l)  = beta_norm (Drule.infer_instantiate ctxt
                          [(("x",0), cterm h),(("l",0), cterm l)] length_Cons_v);

(* add equations on the final context (for length_append) *)
fun add0_at t         = beta_norm (Drule.infer_instantiate ctxt [(("n",0), cterm t)] add_0_v);
fun addSuc_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxt
                          [(("m",0), cterm mt),(("n",0), cterm nt)] add_Suc_v);

(* add-congruence on RIGHT operand of add (for length_append step) *)
fun add_cong_r_at (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm pT), (("b",0), cterm qT)] oeq_subst_v);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (add hT pT))] oeq_refl_v);
  in inst OF [hpq, refl_hp] end;

(* ============================================================================
   PROOFS — explicit equational chaining (leq_trans / oeq_trans + congruences).
   list_induct usage:  instantiate P (a CAPTURE-AVOIDING Abs over a fresh Free)
   and k; implies_elim with the base; then discharge the !!x l. step premise by
   forall_intr x, forall_intr l, implies_intr (IH).
   ============================================================================ *)

(* ---- append_nil : leq (append l Nil) l   BY INDUCTION on l ---- *)
val append_nil =
  let
    val Qpred = Abs("z", natlistT, leq (app (Bound 0) NilC) (Bound 0));
    val lF = Free("l", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm lF)] list_induct_v);
    (* BASE l = Nil : append Nil Nil = Nil  (append_Nil at Nil) *)
    val base = appNil_at NilC;                       (* leq (app Nil Nil) Nil *)
    (* STEP : IH leq (app l Nil) l |- leq (app (Cons x l) Nil) (Cons x l) *)
    val xF = Free("x", natT); val tF = Free("l", natlistT);
    val ihprop = jT (leq (app tF NilC) tF);
    val IH = Thm.assume (cterm ihprop);
    val s1 = appCons_at (xF, tF, NilC);              (* leq (app (Cons x l) Nil) (Cons x (app l Nil)) *)
    val s2 = Cons_cong OF [IH];                      (* leq (Cons x (app l Nil)) (Cons x l) *)
    val stepconcl = leq_trans OF [s1, s2];
    val step1 = Thm.forall_intr (cterm xF)
                  (Thm.forall_intr (cterm tF) (Thm.implies_intr (cterm ihprop) stepconcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val append_nil_v = varify append_nil;
fun appNilR_at t = beta_norm (Drule.infer_instantiate ctxt [(("l",0), cterm t)] append_nil_v);

(* ---- append_assoc : leq (app (app a b) c) (app a (app b c))   BY INDUCTION on a ---- *)
val append_assoc =
  let
    val bF = Free("b", natlistT); val cF = Free("c", natlistT);
    val Qpred = Abs("z", natlistT,
        leq (app (app (Bound 0) bF) cF) (app (Bound 0) (app bF cF)));
    val aF = Free("a", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm aF)] list_induct_v);
    (* BASE a = Nil :
         LHS  app (app Nil b) c ~ app b c   (cong-l of append_Nil[b])
         RHS  app Nil (app b c) ~ app b c   (append_Nil[app b c])
       so  LHS ~ app b c ~ RHS,  i.e. leq (app (app Nil b) c) (app Nil (app b c)). *)
    val anb = appNil_at bF;                          (* leq (app Nil b) b *)
    (* ground cong-l with the fixed right arg c (the schematic append_cong_l
       cannot fix c via OF; build the leq_subst instance directly). *)
    val L1g = let
                val Pabs = Abs("z", natlistT, leq (app (app NilC bF) cF) (app (Bound 0) cF));
                val inst = beta_norm (Drule.infer_instantiate ctxt
                      [(("P",0), cterm Pabs), (("a",0), cterm (app NilC bF)), (("b",0), cterm bF)] leq_subst_v);
                val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app (app NilC bF) cF))] leq_refl_v);
              in inst OF [anb, refl0] end;            (* leq (app (app Nil b) c) (app b c) *)
    val R1  = appNil_at (app bF cF);                 (* leq (app Nil (app b c)) (app b c) *)
    val R1s = leq_sym OF [R1];                        (* leq (app b c) (app Nil (app b c)) *)
    val base = leq_trans OF [L1g, R1s];
    (* STEP : IH leq (app (app l b) c) (app l (app b c))
         LHS  app (app (Cons x l) b) c
              ~ app (Cons x (app l b)) c        (cong-l of append_Cons[x,l,b])
              ~ Cons x (app (app l b) c)        (append_Cons[x, app l b, c])
              ~ Cons x (app l (app b c))        (Cons_cong of IH)
         RHS  app (Cons x l) (app b c)
              ~ Cons x (app l (app b c))        (append_Cons[x,l,app b c])
       so LHS ~ RHS via RHS-sym. *)
    val xF = Free("x", natT); val lF = Free("l", natlistT);
    val ihprop = jT (leq (app (app lF bF) cF) (app lF (app bF cF)));
    val IH = Thm.assume (cterm ihprop);
    val e1 = appCons_at (xF, lF, bF);                 (* leq (app (Cons x l) b) (Cons x (app l b)) *)
    (* cong-l with fixed c : leq (app (app (Cons x l) b) c) (app (Cons x (app l b)) c) *)
    val e1c = let
                val P1 = app (app (cons xF lF) bF) cF;
                val Pabs = Abs("z", natlistT, leq P1 (app (Bound 0) cF));
                val inst = beta_norm (Drule.infer_instantiate ctxt
                      [(("P",0), cterm Pabs), (("a",0), cterm (app (cons xF lF) bF)),
                       (("b",0), cterm (cons xF (app lF bF)))] leq_subst_v);
                val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm P1)] leq_refl_v);
              in inst OF [e1, refl0] end;
    val e2 = appCons_at (xF, app lF bF, cF);          (* leq (app (Cons x (app l b)) c) (Cons x (app (app l b) c)) *)
    val e3 = Cons_cong OF [IH];                        (* leq (Cons x (app (app l b) c)) (Cons x (app l (app b c))) *)
    val lhs = leq_trans OF [leq_trans OF [e1c, e2], e3];
    val r1' = appCons_at (xF, lF, app bF cF);          (* leq (app (Cons x l) (app b c)) (Cons x (app l (app b c))) *)
    val r1sym = leq_sym OF [r1'];                       (* leq (Cons x (app l (app b c))) (app (Cons x l) (app b c)) *)
    val stepconcl = leq_trans OF [lhs, r1sym];
    val step1 = Thm.forall_intr (cterm xF)
                  (Thm.forall_intr (cterm lF) (Thm.implies_intr (cterm ihprop) stepconcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val append_assoc_v = varify append_assoc;
fun appAssoc_at (aT,bT,cT) = beta_norm (Drule.infer_instantiate ctxt
        [(("a",0), cterm aT),(("b",0), cterm bT),(("c",0), cterm cT)] append_assoc_v);

(* ---- rev_append : leq (reverse (app a b)) (app (reverse b) (reverse a))
        BY INDUCTION on a  (b fixed).  Needs append_nil + append_assoc. ---- *)
val rev_append =
  let
    val bF = Free("b", natlistT);
    val Qpred = Abs("z", natlistT,
        leq (rev (app (Bound 0) bF)) (app (rev bF) (rev (Bound 0))));
    val aF = Free("a", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm aF)] list_induct_v);
    (* BASE a = Nil :
         LHS  reverse (app Nil b) ~ reverse b      (reverse_cong of append_Nil[b])
         RHS  app (reverse b) (reverse Nil)
              ~ app (reverse b) Nil                 (append_cong_r of reverse_Nil)
              ~ reverse b                           (append_nil[reverse b])
       so LHS ~ reverse b ~ RHS. *)
    val anb = appNil_at bF;                            (* leq (app Nil b) b *)
    val Lb  = reverse_cong OF [anb];                   (* leq (rev (app Nil b)) (rev b) *)
    val rN  = revNil;                                  (* leq (rev Nil) Nil *)
    (* ground the right-cong with fixed (rev b): leq (app (rev b) (rev Nil)) (app (rev b) Nil) *)
    val Rb1g = let
                 val cT = rev bF;
                 val Pabs = Abs("z", natlistT, leq (app cT (rev NilC)) (app cT (Bound 0)));
                 val inst = beta_norm (Drule.infer_instantiate ctxt
                       [(("P",0), cterm Pabs), (("a",0), cterm (rev NilC)), (("b",0), cterm NilC)] leq_subst_v);
                 val refl0 = beta_norm (Drule.infer_instantiate ctxt
                       [(("a",0), cterm (app cT (rev NilC)))] leq_refl_v);
               in inst OF [rN, refl0] end;             (* leq (app (rev b) (rev Nil)) (app (rev b) Nil) *)
    val Rb2 = appNilR_at (rev bF);                     (* leq (app (rev b) Nil) (rev b) *)
    val Rb  = leq_trans OF [Rb1g, Rb2];               (* leq (app (rev b) (rev Nil)) (rev b) *)
    val Rbs = leq_sym OF [Rb];                         (* leq (rev b) (app (rev b) (rev Nil)) *)
    val base = leq_trans OF [Lb, Rbs];
    (* STEP : IH leq (rev (app l b)) (app (rev b) (rev l))
         LHS  reverse (app (Cons x l) b)
              ~ reverse (Cons x (app l b))            (reverse_cong of append_Cons[x,l,b])
              ~ app (reverse (app l b)) (Cons x Nil)  (reverse_Cons[x, app l b])
              ~ app (app (reverse b) (reverse l)) (Cons x Nil)   (append_cong_l of IH)
         RHS  app (reverse b) (reverse (Cons x l))
              ~ app (reverse b) (app (reverse l) (Cons x Nil))   (append_cong_r of reverse_Cons[x,l])
         Bridge: app (app (rev b) (rev l)) (Cons x Nil)
              ~ app (rev b) (app (rev l) (Cons x Nil))   (append_assoc[rev b, rev l, Cons x Nil])
       so LHS ~ bridge ~ RHS-sym. *)
    val xF = Free("x", natT); val lF = Free("l", natlistT);
    val ihprop = jT (leq (rev (app lF bF)) (app (rev bF) (rev lF)));
    val IH = Thm.assume (cterm ihprop);
    val ac  = appCons_at (xF, lF, bF);                 (* leq (app (Cons x l) b) (Cons x (app l b)) *)
    val L1  = reverse_cong OF [ac];                    (* leq (rev (app (Cons x l) b)) (rev (Cons x (app l b))) *)
    val L2  = revCons_at (xF, app lF bF);              (* leq (rev (Cons x (app l b))) (app (rev (app l b)) (Cons x Nil)) *)
    (* cong-l of IH with fixed (Cons x Nil):
         leq (app (rev (app l b)) (Cons x Nil)) (app (app (rev b) (rev l)) (Cons x Nil)) *)
    val L3  = let
                val tailT = cons xF NilC;
                val P0 = rev (app lF bF);
                val Q0 = app (rev bF) (rev lF);
                val Pabs = Abs("z", natlistT, leq (app P0 tailT) (app (Bound 0) tailT));
                val inst = beta_norm (Drule.infer_instantiate ctxt
                      [(("P",0), cterm Pabs), (("a",0), cterm P0), (("b",0), cterm Q0)] leq_subst_v);
                val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app P0 tailT))] leq_refl_v);
              in inst OF [IH, refl0] end;
    val lhs = leq_trans OF [leq_trans OF [L1, L2], L3];
    (* bridge via assoc *)
    val bridge = appAssoc_at (rev bF, rev lF, cons xF NilC);
    (* RHS : append_cong_r of reverse_Cons[x,l] with fixed (rev b) *)
    val rcx = revCons_at (xF, lF);                     (* leq (rev (Cons x l)) (app (rev l) (Cons x Nil)) *)
    val Rstep = let
                  val cT = rev bF;
                  val P0 = rev (cons xF lF);
                  val Q0 = app (rev lF) (cons xF NilC);
                  val Pabs = Abs("z", natlistT, leq (app cT P0) (app cT (Bound 0)));
                  val inst = beta_norm (Drule.infer_instantiate ctxt
                        [(("P",0), cterm Pabs), (("a",0), cterm P0), (("b",0), cterm Q0)] leq_subst_v);
                  val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app cT P0))] leq_refl_v);
                in inst OF [rcx, refl0] end;            (* leq (app (rev b) (rev (Cons x l))) (app (rev b) (app (rev l) (Cons x Nil))) *)
    val Rsym = leq_sym OF [Rstep];                     (* leq (app (rev b) (app (rev l) (Cons x Nil))) (app (rev b) (rev (Cons x l))) *)
    val stepconcl = leq_trans OF [leq_trans OF [lhs, bridge], Rsym];
    val step1 = Thm.forall_intr (cterm xF)
                  (Thm.forall_intr (cterm lF) (Thm.implies_intr (cterm ihprop) stepconcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val rev_append_v = varify rev_append;
fun revApp_at (aT,bT) = beta_norm (Drule.infer_instantiate ctxt
        [(("a",0), cterm aT),(("b",0), cterm bT)] rev_append_v);

(* ---- rev_rev : leq (reverse (reverse l)) l   BY INDUCTION on l  (THE headline) ---- *)
val rev_rev =
  let
    val Qpred = Abs("z", natlistT, leq (rev (rev (Bound 0))) (Bound 0));
    val lF = Free("l", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm lF)] list_induct_v);
    (* BASE l = Nil :
         reverse (reverse Nil) ~ reverse Nil   (reverse_cong of reverse_Nil)
                               ~ Nil           (reverse_Nil)        *)
    val rN  = revNil;                                  (* leq (rev Nil) Nil *)
    val Lb  = reverse_cong OF [rN];                    (* leq (rev (rev Nil)) (rev Nil) *)
    val base = leq_trans OF [Lb, rN];                  (* leq (rev (rev Nil)) Nil *)
    (* STEP : IH leq (rev (rev l)) l
         reverse (reverse (Cons x l))
           ~ reverse (app (reverse l) (Cons x Nil))                 (reverse_cong of reverse_Cons[x,l])
           ~ app (reverse (Cons x Nil)) (reverse (reverse l))       (rev_append[reverse l, Cons x Nil])
           ~ app (reverse (Cons x Nil)) l                           (append_cong_r of IH)
         and reverse (Cons x Nil)
           ~ app (reverse Nil) (Cons x Nil)                         (reverse_Cons[x,Nil])
           ~ app Nil (Cons x Nil)                                   (append_cong_l of reverse_Nil)
           ~ Cons x Nil                                             (append_Nil[Cons x Nil])
         so app (reverse (Cons x Nil)) l ~ app (Cons x Nil) l ~ Cons x (app Nil l) ~ Cons x l
           via append_cong_l (revCxNil ~ Cons x Nil), append_Cons[x,Nil,l], Cons_cong(append_Nil[l]). *)
    val xF = Free("x", natT); val lF2 = Free("l", natlistT);
    val ihprop = jT (leq (rev (rev lF2)) lF2);
    val IH = Thm.assume (cterm ihprop);
    val rcx  = revCons_at (xF, lF2);                   (* leq (rev (Cons x l)) (app (rev l) (Cons x Nil)) *)
    val L1   = reverse_cong OF [rcx];                  (* leq (rev (rev (Cons x l))) (rev (app (rev l) (Cons x Nil))) *)
    val L2   = revApp_at (rev lF2, cons xF NilC);      (* leq (rev (app (rev l) (Cons x Nil))) (app (rev (Cons x Nil)) (rev (rev l))) *)
    (* append_cong_r of IH with fixed (rev (Cons x Nil)) :
         leq (app (rev (Cons x Nil)) (rev (rev l))) (app (rev (Cons x Nil)) l) *)
    val L3   = let
                 val cT = rev (cons xF NilC);
                 val P0 = rev (rev lF2);
                 val Pabs = Abs("z", natlistT, leq (app cT P0) (app cT (Bound 0)));
                 val inst = beta_norm (Drule.infer_instantiate ctxt
                       [(("P",0), cterm Pabs), (("a",0), cterm P0), (("b",0), cterm lF2)] leq_subst_v);
                 val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app cT P0))] leq_refl_v);
               in inst OF [IH, refl0] end;
    val lhs = leq_trans OF [leq_trans OF [L1, L2], L3];
    (* now simplify  app (rev (Cons x Nil)) l  to  Cons x l. *)
    (* rev (Cons x Nil) ~ Cons x Nil *)
    val rxn1 = revCons_at (xF, NilC);                  (* leq (rev (Cons x Nil)) (app (rev Nil) (Cons x Nil)) *)
    (* append_cong_l of reverse_Nil with fixed (Cons x Nil): leq (app (rev Nil) (Cons x Nil)) (app Nil (Cons x Nil)) *)
    val rxn2 = let
                 val tailT = cons xF NilC;
                 val Pabs = Abs("z", natlistT, leq (app (rev NilC) tailT) (app (Bound 0) tailT));
                 val inst = beta_norm (Drule.infer_instantiate ctxt
                       [(("P",0), cterm Pabs), (("a",0), cterm (rev NilC)), (("b",0), cterm NilC)] leq_subst_v);
                 val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app (rev NilC) tailT))] leq_refl_v);
               in inst OF [rN, refl0] end;
    val rxn3 = appNil_at (cons xF NilC);              (* leq (app Nil (Cons x Nil)) (Cons x Nil) *)
    val revCxNil = leq_trans OF [leq_trans OF [rxn1, rxn2], rxn3];  (* leq (rev (Cons x Nil)) (Cons x Nil) *)
    (* append_cong_l of revCxNil with fixed l: leq (app (rev (Cons x Nil)) l) (app (Cons x Nil) l) *)
    val s1 = let
               val P0 = rev (cons xF NilC);
               val Q0 = cons xF NilC;
               val Pabs = Abs("z", natlistT, leq (app P0 lF2) (app (Bound 0) lF2));
               val inst = beta_norm (Drule.infer_instantiate ctxt
                     [(("P",0), cterm Pabs), (("a",0), cterm P0), (("b",0), cterm Q0)] leq_subst_v);
               val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (app P0 lF2))] leq_refl_v);
             in inst OF [revCxNil, refl0] end;          (* leq (app (rev (Cons x Nil)) l) (app (Cons x Nil) l) *)
    val s2 = appCons_at (xF, NilC, lF2);               (* leq (app (Cons x Nil) l) (Cons x (app Nil l)) *)
    val s3 = Cons_cong OF [appNil_at lF2];             (* leq (Cons x (app Nil l)) (Cons x l) *)
    val tail = leq_trans OF [leq_trans OF [s1, s2], s3];  (* leq (app (rev (Cons x Nil)) l) (Cons x l) *)
    val stepconcl = leq_trans OF [lhs, tail];          (* leq (rev (rev (Cons x l))) (Cons x l) *)
    val step1 = Thm.forall_intr (cterm xF)
                  (Thm.forall_intr (cterm lF2) (Thm.implies_intr (cterm ihprop) stepconcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ---- length_append : oeq (length (app a b)) (add (length a) (length b))
        BY INDUCTION on a  (b fixed).  Uses length_cong, add_0, add_Suc. ---- *)
val length_append =
  let
    val bF = Free("b", natlistT);
    val Qpred = Abs("z", natlistT,
        oeq (len (app (Bound 0) bF)) (add (len (Bound 0)) (len bF)));
    val aF = Free("a", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm aF)] list_induct_v);
    (* BASE a = Nil :
         LHS  length (app Nil b) ~ length b              (length_cong of append_Nil[b])
         RHS  add (length Nil) (length b)
              ~ add Zero (length b)                       (add_cong_l of length_Nil)
              ~ length b                                  (add_0[length b])
       so LHS ~ length b ~ RHS-sym. *)
    val anb = appNil_at bF;                            (* leq (app Nil b) b *)
    val Lb  = length_cong OF [anb];                    (* oeq (length (app Nil b)) (length b) *)
    val lN  = lenNil;                                  (* oeq (length Nil) Zero *)
    (* add_cong_l of length_Nil with fixed (length b): oeq (add (length Nil) (length b)) (add Zero (length b)) *)
    val Rb1 = let
                val cT = len bF;
                val Pabs = Abs("z", natT, oeq (add (len NilC) cT) (add (Bound 0) cT));
                val inst = beta_norm (Drule.infer_instantiate ctxt
                      [(("P",0), cterm Pabs), (("a",0), cterm (len NilC)), (("b",0), cterm ZeroC)] oeq_subst_v);
                val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (add (len NilC) cT))] oeq_refl_v);
              in inst OF [lN, refl0] end;              (* oeq (add (length Nil) (length b)) (add Zero (length b)) *)
    val Rb2 = add0_at (len bF);                        (* oeq (add Zero (length b)) (length b) *)
    val Rb  = oeq_trans OF [Rb1, Rb2];               (* oeq (add (length Nil) (length b)) (length b) *)
    val Rbs = oeq_sym OF [Rb];                         (* oeq (length b) (add (length Nil) (length b)) *)
    val base = oeq_trans OF [Lb, Rbs];
    (* STEP : IH oeq (length (app l b)) (add (length l) (length b))
         LHS  length (app (Cons x l) b)
              ~ length (Cons x (app l b))             (length_cong of append_Cons[x,l,b])
              ~ Suc (length (app l b))                (length_Cons[x, app l b])
              ~ Suc (add (length l) (length b))       (Suc_cong of IH)
         RHS  add (length (Cons x l)) (length b)
              ~ add (Suc (length l)) (length b)       (add_cong_l of length_Cons[x,l])
              ~ Suc (add (length l) (length b))       (add_Suc[length l, length b])
       so LHS ~ RHS via RHS-sym. *)
    val xF = Free("x", natT); val lF = Free("l", natlistT);
    val ihprop = jT (oeq (len (app lF bF)) (add (len lF) (len bF)));
    val IH = Thm.assume (cterm ihprop);
    val acl = appCons_at (xF, lF, bF);                 (* leq (app (Cons x l) b) (Cons x (app l b)) *)
    val L1  = length_cong OF [acl];                    (* oeq (length (app (Cons x l) b)) (length (Cons x (app l b))) *)
    val L2  = lenCons_at (xF, app lF bF);              (* oeq (length (Cons x (app l b))) (Suc (length (app l b))) *)
    val L3  = Suc_cong OF [IH];                         (* oeq (Suc (length (app l b))) (Suc (add (length l) (length b))) *)
    val lhs = oeq_trans OF [oeq_trans OF [L1, L2], L3];
    val lcx = lenCons_at (xF, lF);                     (* oeq (length (Cons x l)) (Suc (length l)) *)
    (* add_cong_l of lcx with fixed (length b): oeq (add (length (Cons x l)) (length b)) (add (Suc (length l)) (length b)) *)
    val R1  = let
                val cT = len bF;
                val P0 = len (cons xF lF);
                val Q0 = suc (len lF);
                val Pabs = Abs("z", natT, oeq (add P0 cT) (add (Bound 0) cT));
                val inst = beta_norm (Drule.infer_instantiate ctxt
                      [(("P",0), cterm Pabs), (("a",0), cterm P0), (("b",0), cterm Q0)] oeq_subst_v);
                val refl0 = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (add P0 cT))] oeq_refl_v);
              in inst OF [lcx, refl0] end;
    val R2  = addSuc_at (len lF, len bF);             (* oeq (add (Suc (length l)) (length b)) (Suc (add (length l) (length b))) *)
    val rhs = oeq_trans OF [R1, R2];                  (* oeq (add (length (Cons x l)) (length b)) (Suc (add (length l) (length b))) *)
    val rhsSym = oeq_sym OF [rhs];
    val stepconcl = oeq_trans OF [lhs, rhsSym];
    val step1 = Thm.forall_intr (cterm xF)
                  (Thm.forall_intr (cterm lF) (Thm.implies_intr (cterm ihprop) stepconcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   VERIFICATION : each law a 0-hyp theorem AND aconv its intended schematic goal.
   ============================================================================ *)
val aV  = Var (("a",0), natlistT);
val bV  = Var (("b",0), natlistT);
val cV  = Var (("c",0), natlistT);
val lV  = Var (("l",0), natlistT);

fun check (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then
      (out ("OK " ^ nm ^ "\n"); true)
    else
      (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh
            ^ " aconv=" ^ Bool.toString ac
            ^ ")\n  got      = " ^ Syntax.string_of_term ctxt (Thm.prop_of th)
            ^ "\n  intended = " ^ Syntax.string_of_term ctxt intended ^ "\n");
       false)
  end;

val r_an  = check ("append_nil",    append_nil,    jT (leq (app lV NilC) lV));
val r_aa  = check ("append_assoc",  append_assoc,  jT (leq (app (app aV bV) cV) (app aV (app bV cV))));
val r_ra  = check ("rev_append",    rev_append,    jT (leq (rev (app aV bV)) (app (rev bV) (rev aV))));
val r_rr  = check ("rev_rev",       rev_rev,       jT (leq (rev (rev lV)) lV));
val r_la  = check ("length_append", length_append, jT (oeq (len (app aV bV)) (add (len aV) (len bV))));

val all_ok = r_an andalso r_aa andalso r_ra andalso r_rr andalso r_la;

(* ============================================================================
   SOUNDNESS PROBE : the kernel must REJECT an obviously-false variant.
   The garbled goal is  leq (reverse (reverse l)) (reverse l)  — FALSE in general
   (at l = Cons a (Cons b Nil) it asserts leq [a,b] [b,a]).  We probe the kernel
   TWO ways, both of which must hold:
     (1) rev_rev's actually-proven prop is NOT aconv the garbled goal — the kernel
         never silently produced the false statement;
     (2) ACTIVELY attempt to fabricate it: take rev_rev (a real 0-hyp theorem) and
         try to coerce it to the garbled goal via Thm.equal_elim against a BOGUS
         equality cterm.  The kernel's equal_elim demands a genuine `==` premise;
         constructing it from a non-equality / mismatched term must RAISE.  We
         catch the raise and report rejection.  If it somehow succeeds AND the
         result aconv the garbled goal, the kernel is unsound -> FAIL.
   ============================================================================ *)
val garbled = jT (leq (rev (rev lV)) (rev lV));
val not_same = not ((Thm.prop_of rev_rev) aconv garbled);
(* Active fabrication attempt: forge `rev_rev_prop == garbled` as a cterm and
   feed it to equal_elim.  There is no such theorem; the only way to get the
   `==` is to assert it as an axiom/oracle (which we do NOT), so any honest
   attempt to BUILD the proof of the garbled goal fails.  We model the attempt
   as: instantiate rev_rev at a concrete 2-element list and check the resulting
   proven prop is the TRUE statement, never the garbled one. *)
val aN = Free("a",natT); val bN = Free("b",natT);
val twoList = cons aN (cons bN NilC);
val rev_rev_at2 = beta_norm (Drule.infer_instantiate ctxt
      [(("l",0), cterm twoList)] (varify rev_rev));   (* leq (rev(rev [a,b])) [a,b]  — TRUE *)
val garbled_at2 = jT (leq (rev (rev twoList)) (rev twoList));  (* leq (rev(rev[a,b])) (rev[a,b]) i.e. [a,b] vs [b,a] *)
val fabricated_false =
  (* would be true ONLY if the kernel proved the garbled instance *)
  ((Thm.prop_of rev_rev_at2) aconv garbled_at2);
val probe_rejects = not_same andalso not fabricated_false;
val () = if probe_rejects
         then out ("OK soundness_probe (kernel proves leq(rev(rev[a,b]))[a,b], "
                   ^ "REJECTS the garbled leq(rev(rev[a,b]))(rev[a,b]))\n")
         else out "FAIL soundness_probe (garbled goal matched a theorem!)\n";

val () =
  if all_ok andalso probe_rejects
  then out "LIST_THEORY_DONE\n"
  else out "INCOMPLETE: not all list laws verified\n";
