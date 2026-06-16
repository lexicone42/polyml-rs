(* ============================================================================
   THE INVOLUTION-PAIRING LEMMA (the historic wall toward Wilson's theorem),
   with its list-product library, in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_wilson_pairing.rs)
   ----------------------------------------------------------------------------
   The classical proof of Wilson's theorem ((p-1)! = -1 mod p) pairs each element
   of {1,...,p-1} with its multiplicative inverse; only 1 and p-1 are self-paired
   (lagrange_roots), so the rest multiply to 1. Formalizing that pairing -- a
   PRODUCT INVARIANT UNDER AN INVOLUTION, with no finite-set library -- has been
   the wall. Here it is proved by genuine LCF kernel inference, in two parts:

   (1) THE LIST-PRODUCT LIBRARY (a natlist datatype defined on the modular base):
       lprod (list product), lmem, lremove (remove first occurrence, conditional),
       llen, lnodup, and the lemmas the pairing needs -- the KEY one being
         extract : lmem x L ==> lprod L = x * lprod (lremove x L)
       plus mem_remove (membership/removal interaction), llen_remove (removal
       strictly shortens), nodup_remove. Each 0-hyp by list induction. (LIST_LIB_OK)

   (2) THE PAIRING LEMMA: for a modulus p, a list L, and a function inv,
         pairing_lemma : lnodup L
            ==> (!x. lmem x L ==> lmem (inv x) L)              [closed under inv]
            ==> (!x. lmem x L ==> cong p (x * inv x) 1)        [inv x is x's inverse]
            ==> (!x. lmem x L ==> ~(inv x = x))                [fixed-point free]
            ==> (!x. lmem x L ==> inv (inv x) = x)             [inv is an involution]
            ==> cong p (lprod L) 1
       By STRONG INDUCTION on llen L: extract the head a and its partner inv a from
       the tail (inv a in L, inv a <> a, so inv a is in the tail), remove both
       (R = L minus {a, inv a}); lprod L = (a * inv a) * lprod R = 1 * lprod R; R
       still satisfies the hypotheses (inv is injective on L from the involution),
       so lprod R = 1 by the IH (llen R < llen L). The pure combinatorial CORE of
       Wilson's theorem, abstracted from the residue range. (PAIRING_OK)

   Soundness probes confirm the pairing genuinely uses the inverse hypothesis (H3)
   and is conditional. Built on the modular/keystone base (isabelle_mult_group.sml
   + gcd + Euclid's lemma + lagrange_roots) via common::with_mult_group. Proved by
   a 2-phase ultracode fleet (wf_1ef6ffe6-859); re-verified end-to-end by hand.

   NEXT toward full Wilson: construct the list [2..p-2] (or [1..p-1]) and prove it
   is closed under the modular inverse (no element maps outside, none self-pairs
   except the excluded 1, p-1), then assemble (p-1)! = 1 * (prod[2..p-2]) * (p-1)
   = -1. Euler's theorem reuses pairing_lemma directly. This lemma is the hard part.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 (seat ll0) — THE LIST-PRODUCT LIBRARY for Wilson's theorem.
   On the final pow/classical/modular theory thyP (context ctxtP), extend with a
   natlist datatype + lprod/lmem/lremove/llen/lnodup and prove the pairing-
   argument lemmas, each by list_induct.  ONE new final context ctxtLL/ctermLL.
   Mirrors isabelle_list_theory.sml (list_induct) and isabelle_fta_unique.sml
   (in_list intro/elim, all_prime Nil/fwd/bwd, remove1 conditional axioms).
   ============================================================================ *)
val () = out "LIST_LIB_BEGIN\n";

(* ---- type natlist + constructors + operations on top of thyP ---- *)
val thyLLt = Sign.add_types_global [(Binding.name "natlist",0,NoSyn)] thyP;
val natlistN = Sign.full_name thyLLt (Binding.name "natlist");
val natlistT = Type (natlistN,[]);
val llpredT  = natlistT --> oT;

val thyLLc = Sign.add_consts
  [(Binding.name "lnil",    natlistT, NoSyn),
   (Binding.name "lcons",   natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "leq",     natlistT --> natlistT --> oT, NoSyn),
   (Binding.name "lprod",   natlistT --> natT, NoSyn),
   (Binding.name "lmem",    natT --> natlistT --> oT, NoSyn),
   (Binding.name "lremove", natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "llen",    natlistT --> natT, NoSyn),
   (Binding.name "lnodup",  natlistT --> oT, NoSyn)] thyLLt;

fun cnstLL nm T = Const (Sign.full_name thyLLc (Binding.name nm), T);
val lnilC    = cnstLL "lnil" natlistT;
val lconsC   = cnstLL "lcons" (natT --> natlistT --> natlistT); fun lcons h t = lconsC $ h $ t;
val leqC     = cnstLL "leq" (natlistT --> natlistT --> oT);     fun leq s t = leqC $ s $ t;
val lprodC   = cnstLL "lprod" (natlistT --> natT);              fun lprod l = lprodC $ l;
val lmemC    = cnstLL "lmem" (natT --> natlistT --> oT);        fun lmem x l = lmemC $ x $ l;
val lremoveC = cnstLL "lremove" (natT --> natlistT --> natlistT); fun lremove x l = lremoveC $ x $ l;
val llenC    = cnstLL "llen" (natlistT --> natT);              fun llen l = llenC $ l;
val lnodupC  = cnstLL "lnodup" (natlistT --> oT);              fun lnodup l = lnodupC $ l;

(* free vars *)
val aLL = Free ("a", natlistT); val bLL = Free ("b", natlistT);
val lLL = Free ("l", natlistT); val tLL = Free ("t", natlistT);
val xLL = Free ("x", natT);     val yLL = Free ("y", natT);     val hLL = Free ("h", natT);
val PLL = Free ("P", llpredT);

(* ---- list equality: refl + subst ---- *)
val ((_,leq_refl_ax),  tLL1) = Thm.add_axiom_global (Binding.name "leq_refl_ll",
      jT (leq aLL aLL)) thyLLc;
val ((_,leq_subst_ax), tLL2) = Thm.add_axiom_global (Binding.name "leq_subst_ll",
      Logic.mk_implies (jT (leq aLL bLL), Logic.mk_implies (jT (PLL $ aLL), jT (PLL $ bLL)))) tLL1;

(* ---- list induction:  P lnil ==> (!!x l. P l ==> P (lcons x l)) ==> P k ---- *)
val list_induct_prop =
  Logic.mk_implies (jT (PLL $ lnilC),
    Logic.mk_implies
      (Logic.all xLL (Logic.all lLL
         (Logic.mk_implies (jT (PLL $ lLL), jT (PLL $ (lcons xLL lLL))))),
       jT (PLL $ aLL)));
val ((_,list_induct_ax), tLL3) = Thm.add_axiom_global (Binding.name "list_induct_ll", list_induct_prop) tLL2;

(* ---- lprod recursion (oeq) :  lprod lnil = Suc Zero ; lprod (lcons x xs) = mult x (lprod xs) ---- *)
val ((_,lprod_nil_ax),  tLL4) = Thm.add_axiom_global (Binding.name "lprod_nil",
      jT (oeq (lprod lnilC) (suc ZeroC))) tLL3;
val ((_,lprod_cons_ax), tLL5) = Thm.add_axiom_global (Binding.name "lprod_cons",
      jT (oeq (lprod (lcons xLL tLL)) (mult xLL (lprod tLL)))) tLL4;

(* ---- lmem (membership) intro/elim ----
     lmem_nil_elim : jT (lmem x lnil) ==> jT oFalse
     lmem_cons_fwd : jT (lmem x (lcons y ys)) ==> jT (Disj (oeq x y) (lmem x ys))
     lmem_cons_bwd : jT (Disj (oeq x y) (lmem x ys)) ==> jT (lmem x (lcons y ys)) *)
val ((_,lmem_nil_elim_ax), tLL6) = Thm.add_axiom_global (Binding.name "lmem_nil_elim",
      Logic.mk_implies (jT (lmem xLL lnilC), jT oFalseC)) tLL5;
val ((_,lmem_cons_fwd_ax), tLL7) = Thm.add_axiom_global (Binding.name "lmem_cons_fwd",
      Logic.mk_implies (jT (lmem xLL (lcons yLL tLL)),
                        jT (mkDisj (oeq xLL yLL) (lmem xLL tLL)))) tLL6;
val ((_,lmem_cons_bwd_ax), tLL8) = Thm.add_axiom_global (Binding.name "lmem_cons_bwd",
      Logic.mk_implies (jT (mkDisj (oeq xLL yLL) (lmem xLL tLL)),
                        jT (lmem xLL (lcons yLL tLL)))) tLL7;

(* ---- lremove (remove FIRST occurrence) : conditional axioms ----
     lremove_nil      : leq (lremove x lnil) lnil
     lremove_cons_eq  : jT (oeq x y) ==> leq (lremove x (lcons y ys)) ys
     lremove_cons_neq : jT (neg (oeq x y)) ==> leq (lremove x (lcons y ys)) (lcons y (lremove x ys)) *)
val ((_,lremove_nil_ax), tLL9) = Thm.add_axiom_global (Binding.name "lremove_nil",
      jT (leq (lremove xLL lnilC) lnilC)) tLL8;
val ((_,lremove_cons_eq_ax), tLL10) = Thm.add_axiom_global (Binding.name "lremove_cons_eq",
      Logic.mk_implies (jT (oeq xLL yLL),
        jT (leq (lremove xLL (lcons yLL tLL)) tLL))) tLL9;
val ((_,lremove_cons_neq_ax), tLL11) = Thm.add_axiom_global (Binding.name "lremove_cons_neq",
      Logic.mk_implies (jT (neg (oeq xLL yLL)),
        jT (leq (lremove xLL (lcons yLL tLL)) (lcons yLL (lremove xLL tLL))))) tLL10;

(* ---- llen recursion (oeq) :  llen lnil = Zero ; llen (lcons x xs) = Suc (llen xs) ---- *)
val ((_,llen_nil_ax),  tLL12) = Thm.add_axiom_global (Binding.name "llen_nil",
      jT (oeq (llen lnilC) ZeroC)) tLL11;
val ((_,llen_cons_ax), tLL13) = Thm.add_axiom_global (Binding.name "llen_cons",
      jT (oeq (llen (lcons xLL tLL)) (suc (llen tLL)))) tLL12;

(* ---- lnodup intro/elim ----
     lnodup_nil       : jT (lnodup lnil)                               (always true)
     lnodup_cons_fwd  : jT (lnodup (lcons x xs)) ==> jT (Conj (neg (lmem x xs)) (lnodup xs))
     lnodup_cons_bwd  : jT (Conj (neg (lmem x xs)) (lnodup xs)) ==> jT (lnodup (lcons x xs)) *)
val ((_,lnodup_nil_ax), tLL14) = Thm.add_axiom_global (Binding.name "lnodup_nil",
      jT (lnodup lnilC)) tLL13;
val ((_,lnodup_cons_fwd_ax), tLL15) = Thm.add_axiom_global (Binding.name "lnodup_cons_fwd",
      Logic.mk_implies (jT (lnodup (lcons xLL tLL)),
                        jT (mkConj (neg (lmem xLL tLL)) (lnodup tLL)))) tLL14;
val ((_,lnodup_cons_bwd_ax), thyLL) = Thm.add_axiom_global (Binding.name "lnodup_cons_bwd",
      Logic.mk_implies (jT (mkConj (neg (lmem xLL tLL)) (lnodup tLL)),
                        jT (lnodup (lcons xLL tLL)))) tLL15;

(* ---- THE ONE FINAL CONTEXT ---- *)
val ctxtLL  = Proof_Context.init_global thyLL;
val ctermLL = Thm.cterm_of ctxtLL;

val () = out "LIST_LIB_CONSTS_READY\n";

(* ============================================================================
   re-varify EVERY reused base axiom/lemma onto ctxtLL (schematic, valid in thyLL)
   ============================================================================ *)
val oeq_refl_vL    = varify oeq_refl;
val oeq_subst_vL   = varify oeq_subst;
val oeq_sym_vL     = varify oeq_sym;
val oeq_trans_vL   = varify oeq_trans;
val Suc_cong_vL    = varify Suc_cong;
val exI_vL         = varify exI_ax;
val exE_vL         = varify exE_ax;
val oFalse_elim_vL = varify oFalse_elim_ax;
val Suc_neq_Zero_vL= varify Suc_neq_Zero_ax;
val Suc_inj_vL     = varify Suc_inj_ax;
val conjI_vL       = varify conjI_ax;
val conjunct1_vL   = varify conjunct1_ax;
val conjunct2_vL   = varify conjunct2_ax;
val disjI1_vL      = varify disjI1_ax;
val disjI2_vL      = varify disjI2_ax;
val disjE_vL       = varify disjE_ax;
val mp_vL          = varify mp_ax;
val impI_vL        = varify impI_ax;
val ex_middle_vL   = varify ex_middle_ax;
val add_0_vL       = varify add_0;
val add_Suc_vL     = varify add_Suc;
val add_0_right_vL = varify add_0_right;
val mult_0_right_vL= varify mult_0_right;
(* list machinery *)
val leq_refl_vL    = varify leq_refl_ax;
val leq_subst_vL   = varify leq_subst_ax;
val list_induct_vL = varify list_induct_ax;
val lprod_nil_vL   = varify lprod_nil_ax;
val lprod_cons_vL  = varify lprod_cons_ax;
val lmem_nil_elim_vL = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vL = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vL = varify lmem_cons_bwd_ax;
val lremove_nil_vL   = varify lremove_nil_ax;
val lremove_cons_eq_vL  = varify lremove_cons_eq_ax;
val lremove_cons_neq_vL = varify lremove_cons_neq_ax;
val llen_nil_vL    = varify llen_nil_ax;
val llen_cons_vL   = varify llen_cons_ax;
val lnodup_nil_vL  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vL = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vL = varify lnodup_cons_bwd_ax;

(* ============================================================================
   GROUND INSTANTIATORS (final context).
   ============================================================================ *)
fun lprodNil_at ()       = lprod_nil_vL;
fun lprodCons_at (h,t)   = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL h),(("t",0), ctermLL t)] lprod_cons_vL);
fun llenNil_at ()        = llen_nil_vL;
fun llenCons_at (h,t)    = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL h),(("t",0), ctermLL t)] llen_cons_vL);
fun add0_at t            = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL t)] add_0_vL);
fun addSuc_at (mt,nt)    = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("m",0), ctermLL mt),(("n",0), ctermLL nt)] add_Suc_vL);

(* lmem intro/elim *)
fun lmemNilElim_at x     = beta_norm (Drule.infer_instantiate ctxtLL [(("x",0), ctermLL x)] lmem_nil_elim_vL);
fun lmemConsFwd_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lmem_cons_fwd_vL);
fun lmemConsBwd_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lmem_cons_bwd_vL);
(* lremove conditional *)
val lremoveNil = lremove_nil_vL;
fun lremoveNil_at x      = beta_norm (Drule.infer_instantiate ctxtLL [(("x",0), ctermLL x)] lremove_nil_vL);
fun lremoveConsEq_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lremove_cons_eq_vL);
fun lremoveConsNeq_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lremove_cons_neq_vL);
(* lnodup intro/elim *)
fun lnodupConsFwd_at (x,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("t",0), ctermLL t)] lnodup_cons_fwd_vL);
fun lnodupConsBwd_at (x,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("t",0), ctermLL t)] lnodup_cons_bwd_vL);

(* ex_middle / disj / conj helpers on ctxtLL *)
fun ex_middle_at At = beta_norm (Drule.infer_instantiate ctxtLL [(("A",0), ctermLL At)] ex_middle_vL);
fun disjE_elim (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At), (("B",0), ctermLL Bt), (("C",0), ctermLL Ct)] disjE_vL)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] disjI1_vL)) h;
fun disjI2_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] disjI2_vL)) h;
fun conjI_at (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] conjI_vL)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_at (At,Bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] conjunct1_vL)) h;
fun conjunct2_at (At,Bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] conjunct2_vL)) h;
fun oFalse_elim_at rT = beta_norm (Drule.infer_instantiate ctxtLL [(("R",0), ctermLL rT)] oFalse_elim_vL);
fun mp_at (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] mp_vL)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_at (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] impI_vL)
  in Thm.implies_elim inst hImpThm end;

(* ---- list-equality lemmas leq_sym / leq_trans (from leq_subst) ---- *)
val leq_sym =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT);
    val Pabs = Abs("z", natlistT, leq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs), (("a",0), ctermLL aF), (("b",0), ctermLL bF)] leq_subst_vL);
    val refl_aa = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL aF)] leq_refl_vL);
    val step = inst OF [Thm.assume (ctermLL (jT (leq aF bF))), refl_aa];
  in varify (Thm.implies_intr (ctermLL (jT (leq aF bF))) step) end;

val leq_trans =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT); val cF = Free("c",natlistT);
    val Pabs = Abs("z", natlistT, leq aF (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs), (("a",0), ctermLL bF), (("b",0), ctermLL cF)] leq_subst_vL);
    val H1 = Thm.assume (ctermLL (jT (leq aF bF)));
    val H2 = Thm.assume (ctermLL (jT (leq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (ctermLL (jT (leq bF cF))) step;
    val t1 = Thm.implies_intr (ctermLL (jT (leq aF bF))) t0;
  in varify t1 end;

val () = out "LIST_LIB_HELPERS_READY\n";

(* ============================================================================
   SANITY: recursion equations instantiate cleanly (0-hyp, aconv intended).
   ============================================================================ *)
val xV = Var (("x",0), natT);
val tV = Var (("t",0), natlistT);
val yV = Var (("y",0), natT);
fun chk0 (nm, th, intended) =
  let val nh = length (Thm.hyps_of th); val ac = (Thm.prop_of th) aconv intended;
  in if nh=0 andalso ac then (out ("OK "^nm^"\n"); true)
     else (out ("FAIL "^nm^" (hyps="^Int.toString nh^" aconv="^Bool.toString ac^")\n"
                ^"  got      = "^Syntax.string_of_term ctxtLL (Thm.prop_of th)^"\n"
                ^"  intended = "^Syntax.string_of_term ctxtLL intended^"\n"); false) end;

val r_lprod_nil  = chk0 ("lprod_nil",  lprod_nil_vL,  jT (oeq (lprod lnilC) (suc ZeroC)));
val r_lprod_cons = chk0 ("lprod_cons", lprod_cons_vL, jT (oeq (lprod (lcons xV tV)) (mult xV (lprod tV))));
val r_llen_nil   = chk0 ("llen_nil",   llen_nil_vL,   jT (oeq (llen lnilC) ZeroC));
val r_llen_cons  = chk0 ("llen_cons",  llen_cons_vL,  jT (oeq (llen (lcons xV tV)) (suc (llen tV))));
val () = out "LIST_LIB_SANITY_DONE\n";

(* ============================================================================
   mult helpers on ctxtLL (for extract).
   ============================================================================ *)
val mult_comm_vL  = varify mult_comm;
val mult_assoc_vL = varify mult_assoc;
fun multcomm_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt),(("n",0), ctermLL nt)] mult_comm_vL);
fun multassoc_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt),(("n",0), ctermLL nt),(("k",0), ctermLL kt)] mult_assoc_vL);
(* mult-cong on LEFT operand: oeq p q ==> oeq (mult p k) (mult q k) *)
fun mult_cong_l (pT,qT,kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL pT), (("b",0), ctermLL qT)] oeq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (mult pT kT))] oeq_refl_vL);
  in inst OF [hpq, refl0] end;
(* mult-cong on RIGHT operand: oeq p q ==> oeq (mult h p) (mult h q) *)
fun mult_cong_r (hT,pT,qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL pT), (("b",0), ctermLL qT)] oeq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (mult hT pT))] oeq_refl_vL);
  in inst OF [hpq, refl0] end;
(* lprod-cong (via leq_subst): leq a b ==> oeq (lprod a) (lprod b) *)
fun lprod_cong (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (lprod aT))] oeq_refl_vL);
  in inst OF [hab, refl0] end;
(* llen-cong (via leq_subst): leq a b ==> oeq (llen a) (llen b) *)
fun llen_cong (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (llen aT) (llen (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (llen aT))] oeq_refl_vL);
  in inst OF [hab, refl0] end;

val () = out "LIST_LIB_MULT_HELPERS_READY\n";

(* ============================================================================
   (1) extract : lmem x L ==> oeq (lprod L) (mult x (lprod (lremove x L)))
       BY list_induct on L.  THE key lemma.
   ============================================================================ *)
val extract =
  let
    val xF = Free("x", natT);
    fun concBody zt = oeq (lprod zt) (mult xF (lprod (lremove xF zt)));
    fun predBody zt = mkImp (lmem xF zt) (concBody zt);
    val Qpred = Abs("z", natlistT, predBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF lnilC)));
        val ff   = Thm.implies_elim (lmemNilElim_at xF) hmem;
        val conc = Thm.implies_elim (oFalse_elim_at (concBody lnilC)) ff;
        val dis  = Thm.implies_intr (ctermLL (jT (lmem xF lnilC))) conc;
      in impI_at (lmem xF lnilC, concBody lnilC) dis end;
    val yF = Free("y", natT); val tF = Free("t", natlistT);
    val ihprop = jT (predBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF (lcons yF tF))));
        val disjmem = Thm.implies_elim (lmemConsFwd_at (xF, yF, tF)) hmem;
        val lpc = lprodCons_at (yF, tF);
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF yF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, yF, tF)) heq;
            val lp_lrm = lprod_cong (lremove xF (lcons yF tF), tF) lrm;
            val rhs_eq = mult_cong_r (xF, lprod (lremove xF (lcons yF tF)), lprod tF) lp_lrm;
            val yx = oeq_sym OF [heq];
            val my_mx = mult_cong_l (yF, xF, lprod tF) yx;
            val rhs_eq_sym = oeq_sym OF [rhs_eq];
            val conc = oeq_trans OF [oeq_trans OF [lpc, my_mx], rhs_eq_sym];
          in Thm.implies_intr (ctermLL (jT (oeq xF yF))) conc end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF yF))));
            val memT =
              let
                val cA = let val hxy = Thm.assume (ctermLL (jT (oeq xF yF)))
                             val ff  = mp_at (oeq xF yF, oFalseC) hneq hxy
                             val r   = Thm.implies_elim (oFalse_elim_at (lmem xF tF)) ff
                         in Thm.implies_intr (ctermLL (jT (oeq xF yF))) r end;
                val cB = let val hm = Thm.assume (ctermLL (jT (lmem xF tF)))
                         in Thm.implies_intr (ctermLL (jT (lmem xF tF))) hm end;
              in disjE_elim (oeq xF yF, lmem xF tF, lmem xF tF) disjmem cA cB end;
            val ihconc = mp_at (lmem xF tF, concBody tF) IH memT;
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, yF, tF)) hneq;
            val rmtl = lremove xF tF;
            val lp_lrm = lprod_cong (lremove xF (lcons yF tF), lcons yF rmtl) lrm;
            val lp_cons = lprodCons_at (yF, rmtl);
            val lp_lrm2 = oeq_trans OF [lp_lrm, lp_cons];
            val rhs1 = mult_cong_r (xF, lprod (lremove xF (lcons yF tF)), mult yF (lprod rmtl)) lp_lrm2;
            val q = lprod rmtl;
            val mut = mult_cong_r (yF, lprod tF, mult xF q) ihconc;
            val lhs1 = oeq_trans OF [lpc, mut];
            val assoc1 = multassoc_at (yF, xF, q);
            val assoc1s = oeq_sym OF [assoc1];
            val comm = multcomm_at (yF, xF);
            val commc = mult_cong_l (mult yF xF, mult xF yF, q) comm;
            val assoc2 = multassoc_at (xF, yF, q);
            val bridge = oeq_trans OF [oeq_trans OF [assoc1s, commc], assoc2];
            val rhs1s = oeq_sym OF [rhs1];
            val conc = oeq_trans OF [oeq_trans OF [lhs1, bridge], rhs1s];
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF yF)))) conc end;
        val em = ex_middle_at (oeq xF yF);
        val conc = disjE_elim (oeq xF yF, neg (oeq xF yF), concBody (lcons yF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lmem xF (lcons yF tF)))) conc;
      in impI_at (lmem xF (lcons yF tF), concBody (lcons yF tF)) dis end;
    val step1 = Thm.forall_intr (ctermLL yF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hmemL = Thm.assume (ctermLL (jT (lmem xF LF)));
    val concL = mp_at (lmem xF LF, concBody LF) r2 hmemL;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem xF LF))) concL;
  in varify d1 end;

val extract_v = varify extract;
val xVe = Var (("x",0), natT);  val LVe = Var (("L",0), natlistT);
val i_extract = Logic.mk_implies (jT (lmem xVe LVe),
      jT (oeq (lprod LVe) (mult xVe (lprod (lremove xVe LVe)))));
val r_extract = chk0 ("extract", extract, i_extract);
val () = out "LIST_LIB_EXTRACT_DONE\n";

(* ============================================================================
   transfer helpers : move an o-predicate across a leq list-equality.
   ============================================================================ *)
fun lmem_transfer (yT, aT, bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
  in inst OF [hleq, hmem] end;
fun lnodup_transfer (aT, bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
  in inst OF [hleq, hnd] end;

(* ============================================================================
   (2a) mem_remove_fwd : lmem y (lremove x L) ==> lmem y L   (BY list_induct on L)
   ============================================================================ *)
val mem_remove_fwd =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun concBody zt = mkImp (lmem yF (lremove xF zt)) (lmem yF zt);
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hassm = Thm.assume (ctermLL (jT (lmem yF (lremove xF lnilC))));
        val lrm = lremoveNil_at xF;
        val mem_lnil = lmem_transfer (yF, lremove xF lnilC, lnilC) lrm hassm;
        val ff  = Thm.implies_elim (lmemNilElim_at yF) mem_lnil;
        val conc = Thm.implies_elim (oFalse_elim_at (lmem yF lnilC)) ff;
        val dis  = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF lnilC)))) conc;
      in impI_at (lmem yF (lremove xF lnilC), lmem yF lnilC) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hassm = Thm.assume (ctermLL (jT (lmem yF (lremove xF (lcons hF tF)))));
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val mem_t = lmem_transfer (yF, lremove xF (lcons hF tF), tF) lrm hassm;
            val dj  = disjI2_at (oeq yF hF, lmem yF tF) mem_t;
            val res = Thm.implies_elim (lmemConsBwd_at (yF, hF, tF)) dj;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) res end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;
            val mem_cons = lmem_transfer (yF, lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm hassm;
            val dj = Thm.implies_elim (lmemConsFwd_at (yF, hF, lremove xF tF)) mem_cons;
            val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))
                         val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, tF))
                                   (disjI1_at (oeq yF hF, lmem yF tF) hyh)
                     in Thm.implies_intr (ctermLL (jT (oeq yF hF))) r end;
            val cB = let val hmr = Thm.assume (ctermLL (jT (lmem yF (lremove xF tF))))
                         val mt  = mp_at (lmem yF (lremove xF tF), lmem yF tF) IH hmr
                         val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, tF))
                                   (disjI2_at (oeq yF hF, lmem yF tF) mt)
                     in Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF tF)))) r end;
            val res = disjE_elim (oeq yF hF, lmem yF (lremove xF tF), lmem yF (lcons hF tF)) dj cA cB;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), lmem yF (lcons hF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF (lcons hF tF))))) conc;
      in impI_at (lmem yF (lremove xF (lcons hF tF)), lmem yF (lcons hF tF)) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hassmL = Thm.assume (ctermLL (jT (lmem yF (lremove xF LF))));
    val concL = mp_at (lmem yF (lremove xF LF), lmem yF LF) r2 hassmL;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF LF)))) concL;
  in varify d1 end;

val mem_remove_fwd_v = varify mem_remove_fwd;
val yVm = Var (("y",0), natT); val xVm = Var (("x",0), natT); val LVm = Var (("L",0), natlistT);
val i_mem_remove_fwd = Logic.mk_implies (jT (lmem yVm (lremove xVm LVm)), jT (lmem yVm LVm));
val r_mem_remove_fwd = chk0 ("mem_remove_fwd", mem_remove_fwd, i_mem_remove_fwd);
val () = out "LIST_LIB_MEM_REMOVE_FWD_DONE\n";

(* exI / add_0_right helpers on ctxtLL *)
fun exI_at Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL at)] exI_vL)
  in Thm.implies_elim inst hbody end;
fun add0r_at t = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL t)] add_0_right_vL);
fun oeq_subst_at (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] oeq_subst_vL)
  in inst OF [hab, hPa] end;

(* ============================================================================
   (2b) mem_remove_bwd : (Conj (lmem y L) (neg (oeq y x))) ==> lmem y (lremove x L)
        BY list_induct on L.  (the direction Phase 2 needs)
   ============================================================================ *)
val mem_remove_bwd =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun hypBody zt = mkConj (lmem yF zt) (neg (oeq yF xF));
    fun concBody zt = mkImp (hypBody zt) (lmem yF (lremove xF zt));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hh = Thm.assume (ctermLL (jT (hypBody lnilC)));
        val mem = conjunct1_at (lmem yF lnilC, neg (oeq yF xF)) hh;
        val ff  = Thm.implies_elim (lmemNilElim_at yF) mem;
        val conc = Thm.implies_elim (oFalse_elim_at (lmem yF (lremove xF lnilC))) ff;
        val dis = Thm.implies_intr (ctermLL (jT (hypBody lnilC))) conc;
      in impI_at (hypBody lnilC, lmem yF (lremove xF lnilC)) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hh = Thm.assume (ctermLL (jT (hypBody (lcons hF tF))));
        val mem = conjunct1_at (lmem yF (lcons hF tF), neg (oeq yF xF)) hh;
        val hneqYX = conjunct2_at (lmem yF (lcons hF tF), neg (oeq yF xF)) hh;
        val djmem = Thm.implies_elim (lmemConsFwd_at (yF, hF, tF)) mem;
        val caseEqXH =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val mem_t =
              let
                val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))
                             val hx = oeq_sym OF [heq]
                             val yx = oeq_trans OF [hyh, hx]
                             val ff = mp_at (oeq yF xF, oFalseC) hneqYX yx
                             val r  = Thm.implies_elim (oFalse_elim_at (lmem yF tF)) ff
                         in Thm.implies_intr (ctermLL (jT (oeq yF hF))) r end;
                val cB = let val hm = Thm.assume (ctermLL (jT (lmem yF tF)))
                         in Thm.implies_intr (ctermLL (jT (lmem yF tF))) hm end;
              in disjE_elim (oeq yF hF, lmem yF tF, lmem yF tF) djmem cA cB end;
            val lrm_s = leq_sym OF [lrm];
            val res = lmem_transfer (yF, tF, lremove xF (lcons hF tF)) lrm_s mem_t;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) res end;
        val caseNeqXH =
          let
            val hneqXH = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneqXH;
            val target = lcons hF (lremove xF tF);
            val mem_target =
              let
                val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))
                             val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, lremove xF tF))
                                       (disjI1_at (oeq yF hF, lmem yF (lremove xF tF)) hyh)
                         in Thm.implies_intr (ctermLL (jT (oeq yF hF))) r end;
                val cB = let val hmt = Thm.assume (ctermLL (jT (lmem yF tF)))
                             val cj  = conjI_at (lmem yF tF, neg (oeq yF xF)) hmt hneqYX
                             val mr  = mp_at (hypBody tF, lmem yF (lremove xF tF)) IH cj
                             val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, lremove xF tF))
                                       (disjI2_at (oeq yF hF, lmem yF (lremove xF tF)) mr)
                         in Thm.implies_intr (ctermLL (jT (lmem yF tF))) r end;
              in disjE_elim (oeq yF hF, lmem yF tF, lmem yF target) djmem cA cB end;
            val lrm_s = leq_sym OF [lrm];
            val res = lmem_transfer (yF, target, lremove xF (lcons hF tF)) lrm_s mem_target;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), lmem yF (lremove xF (lcons hF tF))) em caseEqXH caseNeqXH;
        val dis = Thm.implies_intr (ctermLL (jT (hypBody (lcons hF tF)))) conc;
      in impI_at (hypBody (lcons hF tF), lmem yF (lremove xF (lcons hF tF))) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hhL = Thm.assume (ctermLL (jT (hypBody LF)));
    val concL = mp_at (hypBody LF, lmem yF (lremove xF LF)) r2 hhL;
    val d1 = Thm.implies_intr (ctermLL (jT (hypBody LF))) concL;
  in varify d1 end;

val i_mem_remove_bwd = Logic.mk_implies (jT (mkConj (lmem yVm LVm) (neg (oeq yVm xVm))),
      jT (lmem yVm (lremove xVm LVm)));
val r_mem_remove_bwd = chk0 ("mem_remove_bwd", mem_remove_bwd, i_mem_remove_bwd);
val () = out "LIST_LIB_MEM_REMOVE_BWD_DONE\n";

(* ============================================================================
   (3) llen_remove : lmem x L ==> lt (llen (lremove x L)) (llen L)
       via stronger oeq (llen L)(suc (llen (lremove x L))) + exI witness Zero.
   ============================================================================ *)
val llen_remove_eq =
  let
    val xF = Free("x", natT);
    fun concBody zt = oeq (llen zt) (suc (llen (lremove xF zt)));
    fun predBody zt = mkImp (lmem xF zt) (concBody zt);
    val Qpred = Abs("z", natlistT, predBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF lnilC)));
        val ff   = Thm.implies_elim (lmemNilElim_at xF) hmem;
        val conc = Thm.implies_elim (oFalse_elim_at (concBody lnilC)) ff;
        val dis  = Thm.implies_intr (ctermLL (jT (lmem xF lnilC))) conc;
      in impI_at (lmem xF lnilC, concBody lnilC) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (predBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF (lcons hF tF))));
        val djmem = Thm.implies_elim (lmemConsFwd_at (xF, hF, tF)) hmem;
        val llc = llenCons_at (hF, tF);
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val lc  = llen_cong (lremove xF (lcons hF tF), tF) lrm;
            val sc  = Suc_cong OF [lc];
            val scs = oeq_sym OF [sc];
            val conc = oeq_trans OF [llc, scs];
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) conc end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val memT =
              let
                val cA = let val hxh = Thm.assume (ctermLL (jT (oeq xF hF)))
                             val ff  = mp_at (oeq xF hF, oFalseC) hneq hxh
                             val r   = Thm.implies_elim (oFalse_elim_at (lmem xF tF)) ff
                         in Thm.implies_intr (ctermLL (jT (oeq xF hF))) r end;
                val cB = let val hm = Thm.assume (ctermLL (jT (lmem xF tF)))
                         in Thm.implies_intr (ctermLL (jT (lmem xF tF))) hm end;
              in disjE_elim (oeq xF hF, lmem xF tF, lmem xF tF) djmem cA cB end;
            val ihconc = mp_at (lmem xF tF, concBody tF) IH memT;
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;
            val lc  = llen_cong (lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm;
            val lcc = llenCons_at (hF, lremove xF tF);
            val rhs_in = oeq_trans OF [lc, lcc];
            val rhs = Suc_cong OF [rhs_in];
            val lhs_in = Suc_cong OF [ihconc];
            val lhs = oeq_trans OF [llc, lhs_in];
            val rhs_s = oeq_sym OF [rhs];
            val conc = oeq_trans OF [lhs, rhs_s];
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) conc end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), concBody (lcons hF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lmem xF (lcons hF tF)))) conc;
      in impI_at (lmem xF (lcons hF tF), concBody (lcons hF tF)) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hmemL = Thm.assume (ctermLL (jT (lmem xF LF)));
    val concL = mp_at (lmem xF LF, concBody LF) r2 hmemL;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem xF LF))) concL;
  in varify d1 end;

val llen_remove =
  let
    val xF = Free("x", natT); val LF = Free("L", natlistT);
    val heq = Thm.assume (ctermLL (jT (lmem xF LF)));
    val eqv = varify llen_remove_eq;
    val streq = beta_norm (Drule.infer_instantiate ctxtLL
          [(("x",0), ctermLL xF), (("L",0), ctermLL LF)] eqv);
    val oeqLL = Thm.implies_elim streq heq;
    val aT = llen (lremove xF LF); val bT = llen LF;
    val a0r = add0r_at (suc aT);
    val a0rs = oeq_sym OF [a0r];
    val body = oeq_trans OF [oeqLL, a0rs];
    val Pabs = Abs("p", natT, oeq bT (add (suc aT) (Bound 0)));
    val ltThm = exI_at Pabs ZeroC body;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem xF LF))) ltThm;
  in varify d1 end;

val i_llen_remove = Logic.mk_implies (jT (lmem xVm LVm), jT (lt (llen (lremove xVm LVm)) (llen LVm)));
val r_llen_remove = chk0 ("llen_remove", llen_remove, i_llen_remove);
val () = out "LIST_LIB_LLEN_REMOVE_DONE\n";

(* ============================================================================
   (4) nodup_remove : lnodup L ==> lnodup (lremove x L)   (BY list_induct on L)
   ============================================================================ *)
val nodup_remove =
  let
    val xF = Free("x", natT);
    fun concBody zt = mkImp (lnodup zt) (lnodup (lremove xF zt));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hnd = Thm.assume (ctermLL (jT (lnodup lnilC)));
        val lrm = lremoveNil_at xF;
        val lrm_s = leq_sym OF [lrm];
        val res = lnodup_transfer (lnilC, lremove xF lnilC) lrm_s hnd;
        val dis = Thm.implies_intr (ctermLL (jT (lnodup lnilC))) res;
      in impI_at (lnodup lnilC, lnodup (lremove xF lnilC)) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hnd = Thm.assume (ctermLL (jT (lnodup (lcons hF tF))));
        val cj  = Thm.implies_elim (lnodupConsFwd_at (hF, tF)) hnd;
        val nmem = conjunct1_at (neg (lmem hF tF), lnodup tF) cj;
        val ndt  = conjunct2_at (neg (lmem hF tF), lnodup tF) cj;
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val lrm_s = leq_sym OF [lrm];
            val res = lnodup_transfer (tF, lremove xF (lcons hF tF)) lrm_s ndt;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) res end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;
            val ndrt = mp_at (lnodup tF, lnodup (lremove xF tF)) IH ndt;
            val mrf = beta_norm (Drule.infer_instantiate ctxtLL
                  [(("y",0), ctermLL hF), (("x",0), ctermLL xF), (("L",0), ctermLL tF)] mem_remove_fwd_v);
            val nmem_rt =
              let val hassm = Thm.assume (ctermLL (jT (lmem hF (lremove xF tF))))
                  val inT   = Thm.implies_elim mrf hassm
                  val ff    = mp_at (lmem hF tF, oFalseC) nmem inT
                  val dis   = Thm.implies_intr (ctermLL (jT (lmem hF (lremove xF tF)))) ff
              in impI_at (lmem hF (lremove xF tF), oFalseC) dis end;
            val cj2 = conjI_at (neg (lmem hF (lremove xF tF)), lnodup (lremove xF tF)) nmem_rt ndrt;
            val nd_target = Thm.implies_elim (lnodupConsBwd_at (hF, lremove xF tF)) cj2;
            val lrm_s = leq_sym OF [lrm];
            val res = lnodup_transfer (lcons hF (lremove xF tF), lremove xF (lcons hF tF)) lrm_s nd_target;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), lnodup (lremove xF (lcons hF tF))) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lnodup (lcons hF tF)))) conc;
      in impI_at (lnodup (lcons hF tF), lnodup (lremove xF (lcons hF tF))) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hndL = Thm.assume (ctermLL (jT (lnodup LF)));
    val concL = mp_at (lnodup LF, lnodup (lremove xF LF)) r2 hndL;
    val d1 = Thm.implies_intr (ctermLL (jT (lnodup LF))) concL;
  in varify d1 end;

val i_nodup_remove = Logic.mk_implies (jT (lnodup LVm), jT (lnodup (lremove xVm LVm)));
val r_nodup_remove = chk0 ("nodup_remove", nodup_remove, i_nodup_remove);
val () = out "LIST_LIB_NODUP_REMOVE_DONE\n";

(* ============================================================================
   PROBES / sanity computations.
   ============================================================================ *)
val probe_lprod2 =
  let
    val aP = Free("a", natT); val bP = Free("b", natT);
    val twolist = lcons aP (lcons bP lnilC);
    val c1 = lprodCons_at (aP, lcons bP lnilC);
    val c2 = lprodCons_at (bP, lnilC);
    val cn = lprodNil_at ();
    val c2' = oeq_trans OF [c2, mult_cong_r (bP, lprod lnilC, suc ZeroC) cn];
    val full = oeq_trans OF [c1, mult_cong_r (aP, lprod (lcons bP lnilC), mult bP (suc ZeroC)) c2'];
    val intended = jT (oeq (lprod twolist) (mult aP (mult bP (suc ZeroC))));
  in (length (Thm.hyps_of full) = 0) andalso ((Thm.prop_of full) aconv intended) end;
val () = if probe_lprod2 then out "PROBE_OK lprod [a,b] = a*(b*1)\n"
         else out "PROBE_FAIL lprod2\n";

val probe_extract_cond =
  let val bogus = jT (oeq (lprod LVe) (mult xVe (lprod (lremove xVe LVe))))
  in not ((Thm.prop_of extract) aconv bogus) end;
val probe_extract_nontrivial =
  let val bogus = Logic.mk_implies (jT (lmem xVe LVe), jT (oeq (lprod LVe) (lprod LVe)))
  in not ((Thm.prop_of extract) aconv bogus) end;
val () = if probe_extract_cond andalso probe_extract_nontrivial
         then out "PROBE_OK extract conditional + nontrivial\n"
         else out "PROBE_FAIL extract collapsed\n";

val probe_mrb_cond =
  let val bogus = Logic.mk_implies (jT (lmem yVm LVm), jT (lmem yVm (lremove xVm LVm)))
  in not ((Thm.prop_of mem_remove_bwd) aconv bogus) end;
val () = if probe_mrb_cond then out "PROBE_OK mem_remove_bwd conditional on y<>x\n"
         else out "PROBE_FAIL mem_remove_bwd\n";

(* ============================================================================
   FINAL VERDICT
   ============================================================================ *)
val () =
  if r_lprod_nil andalso r_lprod_cons andalso r_llen_nil andalso r_llen_cons
     andalso r_extract andalso r_mem_remove_fwd andalso r_mem_remove_bwd
     andalso r_llen_remove andalso r_nodup_remove
     andalso probe_lprod2 andalso probe_extract_cond andalso probe_extract_nontrivial
     andalso probe_mrb_cond
  then out "LIST_LIB_OK\n"
  else out "LIST_LIB_FAILED\n";

(* ============================================================================
   PHASE 2 (seat pr0) — THE INVOLUTION-PAIRING LEMMA toward Wilson's theorem.
   On ctxtLL (the Phase-1 list-library context), prove pairing_lemma by list
   strong induction on llen L (derived from meta_nat_induct).
   ============================================================================ *)
val () = out "PAIRING_BEGIN\n";

(* ---- re-varify base nat-order + cong lemmas onto ctxtLL ---- *)
val meta_nat_induct_vLL = varify meta_nat_induct_ax2;
val lt_suc_vLL        = varify lt_suc;
val lt_suc_cases_vLL  = varify lt_suc_cases;
val Suc_neq_Zero_vLL  = varify Suc_neq_Zero_ax;
val cong_refl_vLL     = varify cong_refl;
val cong_mult_vLL     = varify cong_mult;
val cong_trans_vLL    = varify cong_trans;
val cong_sym_vLL      = varify cong_sym;
val mult_1_left_vLL   = varify mult_1_left;
val oeq_subst_vLL     = oeq_subst_vL;   (* alias *)

(* ---- ground instantiators on ctxtLL ---- *)
fun lt_suc_at nt = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL nt)] lt_suc_vLL);
fun lt_suc_cases_at (mt,nt) hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt),(("n",0), ctermLL nt)] lt_suc_cases_vLL)
  in Thm.implies_elim inst hlt end;
fun Suc_neq_Zero_at nt heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL nt)] Suc_neq_Zero_vLL)
  in Thm.implies_elim inst heq end;
fun mult1l_at t = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL t)] mult_1_left_vLL);

(* cong instantiators on ctxtLL *)
fun cong_refl_at (mt, at) = beta_norm (Drule.infer_instantiate ctxtLL
      [(("m",0), ctermLL mt), (("a",0), ctermLL at)] cong_refl_vLL);
fun cong_mult_at (mt, at, a2t, bt, b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt), (("a",0), ctermLL at), (("a2",0), ctermLL a2t),
         (("b",0), ctermLL bt), (("b2",0), ctermLL b2t)] cong_mult_vLL)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_trans_at (mt, at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt), (("a",0), ctermLL at), (("b",0), ctermLL bt),
         (("c",0), ctermLL ct)] cong_trans_vLL)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_sym_at (mt, at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt), (("a",0), ctermLL at), (("b",0), ctermLL bt)] cong_sym_vLL)
  in Thm.implies_elim inst h end;

(* cong_cong on ctxtLL : oeq a a2 -> oeq b b2 -> cong m a b -> cong m a2 b2. *)
fun cong_cong_at (mF, aF, a2F, bF, b2F) (haa2 : thm) (hbb2 : thm) (hcong : thm) =
  let
    val zF1 = Free("zz1", natT);
    val Pabs1 = Term.lambda zF1 (cong mF zF1 bF);
    val inst1 = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs1), (("a",0), ctermLL aF), (("b",0), ctermLL a2F)] oeq_subst_vLL);
    val cong1 = inst1 OF [haa2, hcong];
    val zF2 = Free("zz2", natT);
    val Pabs2 = Term.lambda zF2 (cong mF a2F zF2);
    val inst2 = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs2), (("a",0), ctermLL bF), (("b",0), ctermLL b2F)] oeq_subst_vLL);
    val cong2 = inst2 OF [hbb2, cong1];
  in cong2 end;

(* exE_elim on ctxtLL *)
fun exE_elim (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermLL hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermLL wF) (Thm.implies_intr (ctermLL hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtLL
                    [(("P",0), ctermLL Pabs), (("Q",0), ctermLL goalC)] exE_vL);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* oeq_subst as a one-shot on ctxtLL : oeq a b -> Tp(P a) -> Tp(P b) *)
fun oeq_rewrite (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] oeq_subst_vLL)
  in inst OF [hab, hPa] end;

val () = out "PAIRING_HELPERS_READY\n";

(* ============================================================================
   lt_zero_elim : jT (lt m Zero) ==> jT (anyGoal)
   ============================================================================ *)
fun lt_zero_elim mT goalC hlt =
  let
    val Pabs = Abs("p", natT, oeq ZeroC (add (suc mT) (Bound 0)));
    fun body w (hw : thm) =                  (* hw : oeq Zero (add (Suc m) w) *)
      let
        val aS    = addSuc_at (mT, w);        (* (Suc m + w) = Suc(m + w) *)
        val z_S   = oeq_trans OF [hw, aS];    (* 0 = Suc(m + w) *)
        val S_z   = oeq_sym OF [z_S];         (* Suc(m+w) = 0 *)
        val fls   = Suc_neq_Zero_at (add mT w) S_z;   (* oFalse *)
      in Thm.implies_elim (oFalse_elim_at goalC) fls end;
  in exE_elim (Pabs, goalC) hlt "w_lz" body end;

val () = out "PAIRING_LT_ZERO_READY\n";

(* ============================================================================
   LIST STRONG INDUCTION (meta), parameterised by an ML body PhiBody : term -> term.
     list_strong_induct PhiBody stepFn  : returns  (LF, Tp(Phi LF))  with LF a Free
       stepFn : (LF : term) -> (applyIH : term -> thm -> thm) -> thm(Tp(Phi LF))
         applyIH L2 (h_lt : Tp(lt (llen L2) (llen LF))) : thm(Tp(Phi L2))
   Meta AUX : !!n. !!L. lt (llen L) n ==> Tp(Phi L)  by meta_nat_induct on n.
   ============================================================================ *)
fun list_strong_induct PhiBody stepFn =
  let
    (* meta predicate  Phi_meta n := !!L. lt (llen L) n ==> Tp(PhiBody L) *)
    val nMeta = Free("n_lsi", natT);
    val LMeta = Free("L_lsi", natlistT);
    fun auxBody nt =
      Logic.all LMeta (Logic.mk_implies (jT (lt (llen LMeta) nt), jT (PhiBody LMeta)));
    val PhiMetaAbs = Term.lambda nMeta (auxBody nMeta);

    (* BASE : !!L. lt (llen L) Zero ==> Tp(PhiBody L) *)
    val base =
      let
        val LB = Free("L_b", natlistT);
        val hlt = Thm.assume (ctermLL (jT (lt (llen LB) ZeroC)));
        val res = lt_zero_elim (llen LB) (PhiBody LB) hlt;
        val disch = Thm.implies_intr (ctermLL (jT (lt (llen LB) ZeroC))) res;
      in Thm.forall_intr (ctermLL LB) disch end;

    (* STEP : !!x. (AUX x) ==> (AUX (Suc x)) *)
    val step =
      let
        val xS = Free("x_lsi", natT);
        val auxX = auxBody xS;               (* !!L. lt (llen L) x ==> Tp(Phi L) *)
        val IHmeta = Thm.assume (ctermLL auxX);
        (* applyAUXx L2 (h : lt (llen L2) x) : Tp(Phi L2) *)
        fun applyAUXx L2 hlt =
          let val a1 = Thm.forall_elim (ctermLL L2) IHmeta
          in Thm.implies_elim a1 hlt end;
        (* prove !!L. lt (llen L)(Suc x) ==> Tp(Phi L) *)
        val LS = Free("L_s", natlistT);
        val hltS = Thm.assume (ctermLL (jT (lt (llen LS) (suc xS))));
        val dThm = lt_suc_cases_at (llen LS, xS) hltS;   (* Disj (lt (llen L) x)(oeq (llen L) x) *)
        val goalC = PhiBody LS;
        val caseA =
          let
            val hA = Thm.assume (ctermLL (jT (lt (llen LS) xS)));
            val r  = applyAUXx LS hA;
          in Thm.implies_intr (ctermLL (jT (lt (llen LS) xS))) r end;
        val caseB =
          let
            val hB = Thm.assume (ctermLL (jT (oeq (llen LS) xS)));  (* oeq (llen LS) x *)
            (* build IH for LS : applyIH L2 (h : lt (llen L2)(llen LS)) : Tp(Phi L2)
               from applyAUXx, rewriting lt (llen L2)(llen LS) to lt (llen L2) x via hB *)
            fun applyIH L2 (h_lt : thm) =     (* h_lt : Tp(lt (llen L2)(llen LS)) *)
              let
                val zpr = Free("z_pr", natT);
                val Pr = Term.lambda zpr (lt (llen L2) zpr);
                val h_lt_x = oeq_rewrite (Pr, llen LS, xS) hB h_lt;  (* lt (llen L2) x *)
              in applyAUXx L2 h_lt_x end;
            val r = stepFn LS applyIH;
          in Thm.implies_intr (ctermLL (jT (oeq (llen LS) xS))) r end;
        val disjE_inst = beta_norm (Drule.infer_instantiate ctxtLL
              [(("A",0), ctermLL (lt (llen LS) xS)), (("B",0), ctermLL (oeq (llen LS) xS)),
               (("C",0), ctermLL goalC)] disjE_vL);
        val d1 = Thm.implies_elim disjE_inst dThm;
        val d2 = Thm.implies_elim d1 caseA;
        val pm = Thm.implies_elim d2 caseB;     (* Tp(Phi LS) *)
        val dischLt = Thm.implies_intr (ctermLL (jT (lt (llen LS) (suc xS)))) pm;
        val auxSucx = Thm.forall_intr (ctermLL LS) dischLt;
        val stepInner = Thm.implies_intr (ctermLL auxX) auxSucx;
      in Thm.forall_intr (ctermLL xS) stepInner end;

    (* the final list LF; instantiate AUX at K := Suc (llen LF), then apply at LF *)
    val LF = Free("L_fin", natlistT);
    val kFin = suc (llen LF);
    val indK = beta_norm (Drule.infer_instantiate ctxtLL
                 [(("Phi",0), ctermLL PhiMetaAbs), (("k",0), ctermLL kFin)] meta_nat_induct_vLL);
    val r1 = Thm.implies_elim indK base;
    val auxK = Thm.implies_elim r1 step;        (* !!L. lt (llen L)(Suc(llen LF)) ==> Tp(Phi L) *)
    val auxKL = Thm.forall_elim (ctermLL LF) auxK;   (* lt (llen LF)(Suc(llen LF)) ==> Tp(Phi LF) *)
    val selfLt = lt_suc_at (llen LF);                (* lt (llen LF)(Suc(llen LF)) *)
    val resLF = Thm.implies_elim auxKL selfLt;       (* Tp(Phi LF) *)
  in (LF, resLF) end;

val () = out "PAIRING_LSI_READY\n";

(* ---- SMOKE TEST of list_strong_induct: prove !!L. oeq (lprod L)(lprod L) ----
   (trivial; just exercises the principle's plumbing end-to-end) ---- *)
val lsi_smoke =
  let
    fun PhiBody L = oeq (lprod L) (lprod L);
    fun stepFn LF applyIH =
      beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (lprod LF))] oeq_refl_vL);
    val (LF, res) = list_strong_induct PhiBody stepFn;
  in varify (Thm.forall_intr (ctermLL LF) res) end;
val r_lsi_smoke = (length (Thm.hyps_of lsi_smoke) = 0);
val () = if r_lsi_smoke then out "OK lsi_smoke (list strong induction plumbing)\n"
         else out "FAIL lsi_smoke\n";

val () = out "PAIRING_SMOKE_DONE\n";

(* ============================================================================
   Object Forall helpers on ctxtLL + inv congruence + injectivity.
   ============================================================================ *)
val allI_vLL = varify allI_ax;
val allE_vLL = varify allE_ax;
fun allI_at Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL [(("P",0), ctermLL Pabs)] allI_vLL)
  in Thm.implies_elim inst hAllThm end;
fun allE_at Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL at)] allE_vLL)
  in Thm.implies_elim inst hForall end;

(* inv : nat => nat  (a Free function variable) ; p : nat (the modulus) *)
val invF = Free("inv", natT --> natT);
fun inv t = invF $ t;
val pF = Free("p", natT);
val oneN = suc ZeroC;

(* inv_cong : oeq a b ==> oeq (inv a)(inv b)   (via oeq_subst, %z. oeq (inv a)(inv z)) *)
fun inv_cong (aT, bT) hab =
  let val Pabs = Abs("z", natT, oeq (inv aT) (inv (Bound 0)));
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (inv aT))] oeq_refl_vL);
  in oeq_rewrite (Pabs, aT, bT) hab refl0 end;

val () = out "PAIRING_FORALL_HELPERS_READY\n";

(* ---- TEST inv_cong : prove oeq a b ==> oeq (inv a)(inv b) as a closed thm ---- *)
val r_inv_cong =
  let
    val aF = Free("a_t", natT); val bF = Free("b_t", natT);
    val hab = Thm.assume (ctermLL (jT (oeq aF bF)));
    val res = inv_cong (aF, bF) hab;
    val th  = Thm.implies_intr (ctermLL (jT (oeq aF bF))) res;
    val intended = Logic.mk_implies (jT (oeq aF bF), jT (oeq (inv aF) (inv bF)));
  in (length (Thm.hyps_of th) = 0) andalso ((Thm.prop_of th) aconv intended) end;
val () = if r_inv_cong then out "OK inv_cong\n" else out "FAIL inv_cong\n";

(* ============================================================================
   inv_inj_on : given H5 as an ML function  h5 : x -> Tp(lmem x L) -> Tp(oeq (inv(inv x)) x),
   if  lmem x L, lmem y L, oeq (inv x)(inv y)  then  oeq x y.
     x = inv(inv x)        [h5 x sym]
       = inv(inv y)        [inv_cong of oeq(inv x)(inv y)]
       = y                 [h5 y]
   ============================================================================ *)
fun inv_inj_on h5 (xT, yT) hMemX hMemY hInvEq =
  let
    val hx = h5 xT hMemX;                       (* oeq (inv(inv x)) x *)
    val hy = h5 yT hMemY;                       (* oeq (inv(inv y)) y *)
    val hx_s = oeq_sym OF [hx];                 (* oeq x (inv(inv x)) *)
    val hii = inv_cong (inv xT, inv yT) hInvEq; (* oeq (inv(inv x))(inv(inv y)) *)
    val c1 = oeq_trans OF [hx_s, hii];          (* oeq x (inv(inv y)) *)
    val c2 = oeq_trans OF [c1, hy];             (* oeq x y *)
  in c2 end;

(* ---- TEST inv_inj_on with a generic L and an assumed H5 ---- *)
val r_inv_inj =
  let
    val LF = Free("L_t", natlistT);
    val xF = Free("x_t", natT); val yF = Free("y_t", natT);
    (* h5 as: assume Tp(oeq (inv(inv z)) z) for any z directly (stand-in) *)
    fun h5 z hMem = Thm.assume (ctermLL (jT (oeq (inv (inv z)) z)));
    val hMemX = Thm.assume (ctermLL (jT (lmem xF LF)));
    val hMemY = Thm.assume (ctermLL (jT (lmem yF LF)));
    val hInvEq= Thm.assume (ctermLL (jT (oeq (inv xF)(inv yF))));
    val res = inv_inj_on h5 (xF, yF) hMemX hMemY hInvEq;
  in (Thm.prop_of res) aconv (jT (oeq xF yF)) end;
val () = if r_inv_inj then out "OK inv_inj_on\n" else out "FAIL inv_inj_on\n";

val () = out "PAIRING_INJ_DONE\n";

(* ============================================================================
   mem_remove_neq : lnodup L ==> lmem y (lremove x L) ==> neg (oeq y x)
     BY list_induct on L (on ctxtLL).
   ============================================================================ *)
val mem_remove_neq =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun concBody zt = mkImp (lnodup zt) (mkImp (lmem yF (lremove xF zt)) (neg (oeq yF xF)));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hmem0 = Thm.assume (ctermLL (jT (lmem yF (lremove xF lnilC))));
        val lrm = lremoveNil_at xF;
        val mem_lnil = lmem_transfer (yF, lremove xF lnilC, lnilC) lrm hmem0;
        val ff  = Thm.implies_elim (lmemNilElim_at yF) mem_lnil;
        val conc = Thm.implies_elim (oFalse_elim_at (neg (oeq yF xF))) ff;
        val d2 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF lnilC)))) conc;
        val d1 = impI_at (lmem yF (lremove xF lnilC), neg (oeq yF xF)) d2;
        val d0 = Thm.implies_intr (ctermLL (jT (lnodup lnilC))) d1;
      in impI_at (lnodup lnilC, mkImp (lmem yF (lremove xF lnilC)) (neg (oeq yF xF))) d0 end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    (* helper: build an object  neg(oeq y x)  from a meta  Tp(oeq y x) ==> Tp oFalse  *)
    fun mkNegYX metaImpl = impI_at (oeq yF xF, oFalseC) metaImpl;
    val stepConcl =
      let
        val hnd = Thm.assume (ctermLL (jT (lnodup (lcons hF tF))));
        val cj  = Thm.implies_elim (lnodupConsFwd_at (hF, tF)) hnd;
        val nmemH = conjunct1_at (neg (lmem hF tF), lnodup tF) cj;   (* neg (lmem h t) *)
        val ndt   = conjunct2_at (neg (lmem hF tF), lnodup tF) cj;   (* lnodup t *)
        val hmem = Thm.assume (ctermLL (jT (lmem yF (lremove xF (lcons hF tF)))));
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));         (* x = h *)
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;  (* leq (lremove x (lcons h t)) t *)
            val mem_t = lmem_transfer (yF, lremove xF (lcons hF tF), tF) lrm hmem;  (* lmem y t *)
            val negYX =
              let val hyx = Thm.assume (ctermLL (jT (oeq yF xF)))     (* y = x *)
                  val yh  = oeq_trans OF [hyx, heq]                   (* y = h *)
                  val Pr  = Abs("z", natT, lmem (Bound 0) tF)
                  val memH= oeq_rewrite (Pr, yF, hF) yh mem_t          (* lmem h t *)
                  val ff  = mp_at (lmem hF tF, oFalseC) nmemH memH
              in mkNegYX (Thm.implies_intr (ctermLL (jT (oeq yF xF))) ff) end;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) negYX end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));   (* x != h *)
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;  (* leq (lremove x (lcons h t)) (lcons h (lremove x t)) *)
            val mem_cons = lmem_transfer (yF, lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm hmem; (* lmem y (lcons h (lremove x t)) *)
            val dj = Thm.implies_elim (lmemConsFwd_at (yF, hF, lremove xF tF)) mem_cons;  (* Disj (oeq y h)(lmem y (lremove x t)) *)
            val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))   (* y = h *)
                         val negYX =
                           let val hyx = Thm.assume (ctermLL (jT (oeq yF xF)))   (* y = x *)
                               val hy_s= oeq_sym OF [hyh]                         (* h = y *)
                               val hx  = oeq_trans OF [hy_s, hyx]                 (* h = x *)
                               val hxh = oeq_sym OF [hx]                          (* x = h *)
                               val ff  = mp_at (oeq xF hF, oFalseC) hneq hxh
                           in mkNegYX (Thm.implies_intr (ctermLL (jT (oeq yF xF))) ff) end;
                     in Thm.implies_intr (ctermLL (jT (oeq yF hF))) negYX end;
            val cB = let val hmt = Thm.assume (ctermLL (jT (lmem yF (lremove xF tF))))
                         val ihA = mp_at (lnodup tF, mkImp (lmem yF (lremove xF tF)) (neg (oeq yF xF))) IH ndt
                         val res = mp_at (lmem yF (lremove xF tF), neg (oeq yF xF)) ihA hmt
                     in Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF tF)))) res end;
            val res = disjE_elim (oeq yF hF, lmem yF (lremove xF tF), neg (oeq yF xF)) dj cA cB;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val negThm = disjE_elim (oeq xF hF, neg (oeq xF hF), neg (oeq yF xF)) em caseEq caseNeq;
        val d2 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF (lcons hF tF))))) negThm;
        val d1 = impI_at (lmem yF (lremove xF (lcons hF tF)), neg (oeq yF xF)) d2;
        val d0 = Thm.implies_intr (ctermLL (jT (lnodup (lcons hF tF)))) d1;
      in impI_at (lnodup (lcons hF tF), mkImp (lmem yF (lremove xF (lcons hF tF))) (neg (oeq yF xF))) d0 end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hndL = Thm.assume (ctermLL (jT (lnodup LF)));
    val hmemL = Thm.assume (ctermLL (jT (lmem yF (lremove xF LF))));
    val resA = mp_at (lnodup LF, mkImp (lmem yF (lremove xF LF)) (neg (oeq yF xF))) r2 hndL;
    val resB = mp_at (lmem yF (lremove xF LF), neg (oeq yF xF)) resA hmemL;
    val d2 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF LF)))) resB;
    val d1 = Thm.implies_intr (ctermLL (jT (lnodup LF))) d2;
  in varify d1 end;

val mem_remove_neq_v = varify mem_remove_neq;
fun mem_remove_neq_at (yt, xt, Lt) hnd hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("y",0), ctermLL yt), (("x",0), ctermLL xt), (("L",0), ctermLL Lt)] mem_remove_neq_v)
  in mp_at (lmem yt (lremove xt Lt), neg (oeq yt xt)) (mp_at (lnodup Lt, mkImp (lmem yt (lremove xt Lt)) (neg (oeq yt xt))) inst hnd) hmem end;

val r_mem_remove_neq =
  let
    val yV = Var(("y",0),natT); val xV = Var(("x",0),natT); val LV = Var(("L",0),natlistT);
    val intended = Logic.mk_implies (jT (lnodup LV),
        Logic.mk_implies (jT (lmem yV (lremove xV LV)), jT (neg (oeq yV xV))));
  in (length (Thm.hyps_of mem_remove_neq) = 0) andalso ((Thm.prop_of mem_remove_neq) aconv intended) end;
val () = if r_mem_remove_neq then out "OK mem_remove_neq\n" else out "FAIL mem_remove_neq\n";

val () = out "PAIRING_MRN_DONE\n";

(* ============================================================================
   META LIST-CASES.  Add lhd/ltl consts (one new final context ctxtL2), then
   prove by list_induct the object  Disj (leq L lnil) (leq L (lcons (lhd L)(ltl L))).
   ============================================================================ *)
val thyL2c = Sign.add_consts
  [(Binding.name "lhd", natlistT --> natT, NoSyn),
   (Binding.name "ltl", natlistT --> natlistT, NoSyn)] thyLL;
fun cnstL2 nm T = Const (Sign.full_name thyL2c (Binding.name nm), T);
val lhdC = cnstL2 "lhd" (natlistT --> natT);  fun lhd l = lhdC $ l;
val ltlC = cnstL2 "ltl" (natlistT --> natlistT); fun ltl l = ltlC $ l;
val xL2 = Free("x", natT); val tL2 = Free("t", natlistT);
val ((_,lhd_cons_ax), tL2a) = Thm.add_axiom_global (Binding.name "lhd_cons",
      jT (oeq (lhd (lcons xL2 tL2)) xL2)) thyL2c;
val ((_,ltl_cons_ax), thyL2) = Thm.add_axiom_global (Binding.name "ltl_cons",
      jT (leq (ltl (lcons xL2 tL2)) tL2)) tL2a;

val ctxtL2  = Proof_Context.init_global thyL2;
val ctermL2 = Thm.cterm_of ctxtL2;

val list_induct_vL2 = varify list_induct_ax;
val leq_refl_vL2    = varify leq_refl_ax;
val disjI1_vL2 = varify disjI1_ax;
val disjI2_vL2 = varify disjI2_ax;
val disjE_vL2  = varify disjE_ax;
fun lhdCons_at (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] (varify lhd_cons_ax));
fun ltlCons_at (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] (varify ltl_cons_ax));
fun leqRefl_at l = beta_norm (Drule.infer_instantiate ctxtL2 [(("a",0), ctermL2 l)] leq_refl_vL2);
fun disjI1_L2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI1_vL2)) h;
fun disjI2_L2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI2_vL2)) h;
fun disjE_L2 (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt),(("C",0), ctermL2 Ct)] disjE_vL2)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
(* leq_subst rewrite on ctxtL2 (for list-eq) *)
val leq_subst_vL2 = varify leq_subst_ax;
fun leq_rewrite (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs), (("a",0), ctermL2 aT), (("b",0), ctermL2 bT)] leq_subst_vL2)
  in inst OF [hab, hPa] end;
(* oeq_subst rewrite on ctxtL2 (terms may mention lhd/ltl) *)
val oeq_subst_vL2 = varify oeq_subst;
fun oeq_rewrite_L2 (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs), (("a",0), ctermL2 aT), (("b",0), ctermL2 bT)] oeq_subst_vL2)
  in inst OF [hab, hPa] end;

(* cases predicate :  %L. Disj (leq L lnil) (leq L (lcons (lhd L)(ltl L))) *)
fun casesBody L = mkDisj (leq L lnilC) (leq L (lcons (lhd L) (ltl L)));

val list_cases_thm =   (* !!L. Tp(casesBody L) *)
  let
    val Qpred = Abs("z", natlistT, casesBody (Bound 0));
    val LF = Free("L_c", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtL2
          [(("P",0), ctermL2 Qpred), (("a",0), ctermL2 LF)] list_induct_vL2);
    val base =
      let
        val nilRefl = leqRefl_at lnilC;        (* leq lnil lnil *)
      in disjI1_L2 (leq lnilC lnilC, leq lnilC (lcons (lhd lnilC)(ltl lnilC))) nilRefl end;
    val hF = Free("h_c", natT); val tF = Free("t_c", natlistT);
    val ihprop = jT (casesBody tF);
    val stepConcl =
      let
        val consL = lcons hF tF;
        val refl0 = leqRefl_at consL;                          (* leq (lcons h t)(lcons h t) *)
        val hLhd = lhdCons_at (hF, tF);                        (* oeq (lhd (lcons h t)) h *)
        val hLhd_s = oeq_sym OF [hLhd];                        (* oeq h (lhd (lcons h t)) *)
        val hLtl = ltlCons_at (hF, tF);                        (* leq (ltl (lcons h t)) t *)
        val hLtl_s = leq_sym OF [hLtl];                        (* leq t (ltl (lcons h t)) *)
        val P1 = Abs("z", natT, leq consL (lcons (Bound 0) tF));
        val r1 = oeq_rewrite_L2 (P1, hF, lhd consL) hLhd_s refl0;  (* leq (lcons h t)(lcons (lhd ..) t) *)
        val P2 = Abs("z", natlistT, leq consL (lcons (lhd consL) (Bound 0)));
        val r2 = leq_rewrite (P2, tF, ltl consL) hLtl_s r1;    (* leq (lcons h t)(lcons (lhd ..)(ltl ..)) *)
      in disjI2_L2 (leq consL lnilC, leq consL (lcons (lhd consL)(ltl consL))) r2 end;
    val step1 = Thm.forall_intr (ctermL2 hF)
                  (Thm.forall_intr (ctermL2 tF) (Thm.implies_intr (ctermL2 ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;            (* Tp(casesBody LF) *)
  in (LF, r2) end;

val () = out "PAIRING_CASES_THM_READY\n";

(* meta cases : given L, produce R from caseNil(Tp(leq L lnil)) and
   caseCons(a, rest, Tp(leq L (lcons a rest))).  a := lhd L, rest := ltl L. *)
fun list_cases (LT, goalC) caseNilFn caseConsFn =
  let
    val (LFc, casesL) = list_cases_thm;
    val casesAtL = beta_norm (Drule.infer_instantiate ctxtL2
          [(("L_c",0), ctermL2 LT)] (varify (Thm.forall_intr (ctermL2 LFc) casesL)));
    val nilP  = leq LT lnilC;
    val consP = leq LT (lcons (lhd LT)(ltl LT));
    val cA = let val h = Thm.assume (ctermL2 (jT nilP))
             in Thm.implies_intr (ctermL2 (jT nilP)) (caseNilFn h) end;
    val cB = let val h = Thm.assume (ctermL2 (jT consP))
             in Thm.implies_intr (ctermL2 (jT consP)) (caseConsFn (lhd LT, ltl LT) h) end;
  in disjE_L2 (nilP, consP, goalC) casesAtL cA cB end;

(* ---- TEST list_cases : prove !!L. Tp(Disj (leq L lnil)(leq L (lcons (lhd L)(ltl L)))) trivially ---- *)
val r_list_cases =
  let
    val (LFc, casesL) = list_cases_thm;
    val th = varify (Thm.forall_intr (ctermL2 LFc) casesL);
  in (length (Thm.hyps_of th) = 0) end;
val () = if r_list_cases then out "OK list_cases_thm\n" else out "FAIL list_cases_thm\n";

val () = out "PAIRING_CASES_DONE\n";

(* ============================================================================
   ctxtL2 helper layer : ALL operations used inside caseCons must build cterms
   over thyL2 (since head = lhd LS / rest = ltl LS mention lhd/ltl).  We
   re-instantiate the SAME varified (theory-agnostic) lemmas via ctxtL2/ctermL2.
   Suffix _2 throughout.
   ============================================================================ *)
val oeq_refl_v2  = varify oeq_refl;
val oeq_subst_v2 = varify oeq_subst;
val mp_v2        = varify mp_ax;
val impI_v2      = varify impI_ax;
val conjI_v2     = varify conjI_ax;
val conjunct1_v2 = varify conjunct1_ax;
val conjunct2_v2 = varify conjunct2_ax;
val oFalse_elim_v2 = varify oFalse_elim_ax;
val allI_v2      = varify allI_ax;
val allE_v2      = varify allE_ax;
val leq_subst_v2 = varify leq_subst_ax;
val lprod_cons_v2= varify lprod_cons_ax;
val llen_cons_v2 = varify llen_cons_ax;
val lmem_cons_fwd_v2 = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_v2 = varify lmem_cons_bwd_ax;
val lnodup_cons_fwd_v2 = varify lnodup_cons_fwd_ax;
val mult_comm_v2 = varify mult_comm;
val mult_assoc_v2= varify mult_assoc;
val mult_1_left_v2 = varify mult_1_left;
val cong_refl_v2 = varify cong_refl;
val cong_mult_v2 = varify cong_mult;
val cong_trans_v2= varify cong_trans;
val lt_suc_v2    = varify lt_suc;

fun oeqRefl_2 t = beta_norm (Drule.infer_instantiate ctxtL2 [(("a",0), ctermL2 t)] oeq_refl_v2);
fun oeq_rw_2 (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] oeq_subst_v2)
  in inst OF [hab, hPa] end;
fun mp_2 (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] mp_v2)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_2 (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] impI_v2)
  in Thm.implies_elim inst hImpThm end;
fun conjI_2 (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] conjI_v2)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] conjunct1_v2)) h;
fun conjunct2_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] conjunct2_v2)) h;
fun oFalse_elim_2 rT = beta_norm (Drule.infer_instantiate ctxtL2 [(("R",0), ctermL2 rT)] oFalse_elim_v2);
fun disjE_2 (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt),(("C",0), ctermL2 Ct)] disjE_vL2)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI1_vL2)) h;
fun disjI2_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI2_vL2)) h;
fun allI_2 Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("P",0), ctermL2 Pabs)] allI_v2)) hAll;
fun allE_2 Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 at)] allE_v2)) hF;
fun leq_rw_2 (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
  in inst OF [hab, hPa] end;
fun lprodCons_2 (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] lprod_cons_v2);
fun llenCons_2 (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] llen_cons_v2);
fun lmemConsFwd_2 (x,y,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("y",0), ctermL2 y),(("t",0), ctermL2 t)] lmem_cons_fwd_v2);
fun lmemConsBwd_2 (x,y,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("y",0), ctermL2 y),(("t",0), ctermL2 t)] lmem_cons_bwd_v2);
fun lnodupConsFwd_2 (x,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("t",0), ctermL2 t)] lnodup_cons_fwd_v2);
fun multcomm_2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] mult_comm_v2);
fun multassoc_2 (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt),(("k",0), ctermL2 kt)] mult_assoc_v2);
fun mult1l_2 t = beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 t)] mult_1_left_v2);
fun mult_cong_r_2 (hT,pT,qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 pT),(("b",0), ctermL2 qT)] oeq_subst_v2)
      val refl0 = oeqRefl_2 (mult hT pT)
  in inst OF [hpq, refl0] end;
fun lprod_cong_2 (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
      val refl0 = oeqRefl_2 (lprod aT)
  in inst OF [hab, refl0] end;
fun llen_cong_2 (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (llen aT) (llen (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
      val refl0 = oeqRefl_2 (llen aT)
  in inst OF [hab, refl0] end;
fun lmem_transfer_2 (yT,aT,bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
  in inst OF [hleq, hmem] end;
fun lnodup_transfer_2 (aT,bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
  in inst OF [hleq, hnd] end;
fun cong_refl_2 (mt,at) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("a",0), ctermL2 at)] cong_refl_v2);
fun cong_mult_2 (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("m",0), ctermL2 mt),(("a",0), ctermL2 at),(("a2",0), ctermL2 a2t),
         (("b",0), ctermL2 bt),(("b2",0), ctermL2 b2t)] cong_mult_v2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_trans_2 (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("m",0), ctermL2 mt),(("a",0), ctermL2 at),(("b",0), ctermL2 bt),(("c",0), ctermL2 ct)] cong_trans_v2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_cong_2 (mF,aF,a2F,bF,b2F) haa2 hbb2 hcong =
  let val zF1 = Free("zz1",natT)
      val Pabs1 = Term.lambda zF1 (cong mF zF1 bF)
      val inst1 = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs1),(("a",0), ctermL2 aF),(("b",0), ctermL2 a2F)] oeq_subst_v2)
      val cong1 = inst1 OF [haa2, hcong]
      val zF2 = Free("zz2",natT)
      val Pabs2 = Term.lambda zF2 (cong mF a2F zF2)
      val inst2 = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs2),(("a",0), ctermL2 bF),(("b",0), ctermL2 b2F)] oeq_subst_v2)
  in inst2 OF [hbb2, cong1] end;
fun lt_suc_2 nt = beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 nt)] lt_suc_v2);
fun inv_cong_2 (aT,bT) hab =
  let val Pabs = Abs("z", natT, oeq (inv aT) (inv (Bound 0)))
      val refl0 = oeqRefl_2 (inv aT)
  in oeq_rw_2 (Pabs, aT, bT) hab refl0 end;
fun inv_inj_2 h5 (xT,yT) hMemX hMemY hInvEq =
  let val hx = h5 xT hMemX
      val hy = h5 yT hMemY
      val hx_s = oeq_sym OF [hx]
      val hii = inv_cong_2 (inv xT, inv yT) hInvEq
      val c1 = oeq_trans OF [hx_s, hii]
  in oeq_trans OF [c1, hy] end;

(* L2 versions of the pieces list_strong_induct needs *)
val meta_nat_induct_v2 = varify meta_nat_induct_ax2;
val lt_suc_cases_v2    = varify lt_suc_cases;
val Suc_neq_Zero_v2    = varify Suc_neq_Zero_ax;
val add_Suc_v2         = varify add_Suc;
val exE_v2             = varify exE_ax;
fun addSuc_2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] add_Suc_v2);
fun Suc_neq_Zero_2 nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 nt)] Suc_neq_Zero_v2)) heq;
fun lt_suc_cases_2 (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] lt_suc_cases_v2)) hlt;
fun exE_elim_2 (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermL2 hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermL2 wF) (Thm.implies_intr (ctermL2 hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtL2
                      [(("P",0), ctermL2 Pabs),(("Q",0), ctermL2 goalC)] exE_v2)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
fun lt_zero_elim_2 mT goalC hlt =
  let val Pabs = Abs("p", natT, oeq ZeroC (add (suc mT) (Bound 0)))
      fun body w (hw:thm) =
        let val aS = addSuc_2 (mT, w)
            val z_S = oeq_trans OF [hw, aS]
            val S_z = oeq_sym OF [z_S]
            val fls = Suc_neq_Zero_2 (add mT w) S_z
        in Thm.implies_elim (oFalse_elim_2 goalC) fls end
  in exE_elim_2 (Pabs, goalC) hlt "w_lz" body end;

(* L2 list strong induction (on llen), identical to the LL version but on ctxtL2 *)
fun list_strong_induct_2 PhiBody stepFn =
  let
    val LMeta = Free("L_lsi", natlistT)
    fun auxBody nt = Logic.all LMeta (Logic.mk_implies (jT (lt (llen LMeta) nt), jT (PhiBody LMeta)))
    val nMeta = Free("n_lsi", natT)
    val PhiMetaAbs = Term.lambda nMeta (auxBody nMeta)
    val base =
      let val LB = Free("L_b", natlistT)
          val hlt = Thm.assume (ctermL2 (jT (lt (llen LB) ZeroC)))
          val res = lt_zero_elim_2 (llen LB) (PhiBody LB) hlt
      in Thm.forall_intr (ctermL2 LB) (Thm.implies_intr (ctermL2 (jT (lt (llen LB) ZeroC))) res) end
    val step =
      let
        val xS = Free("x_lsi", natT)
        val auxX = auxBody xS
        val IHmeta = Thm.assume (ctermL2 auxX)
        fun applyAUXx L2 hlt = Thm.implies_elim (Thm.forall_elim (ctermL2 L2) IHmeta) hlt
        val LS = Free("L_s", natlistT)
        val hltS = Thm.assume (ctermL2 (jT (lt (llen LS) (suc xS))))
        val dThm = lt_suc_cases_2 (llen LS, xS) hltS
        val goalC = PhiBody LS
        val caseA = let val hA = Thm.assume (ctermL2 (jT (lt (llen LS) xS)))
                    in Thm.implies_intr (ctermL2 (jT (lt (llen LS) xS))) (applyAUXx LS hA) end
        val caseB =
          let val hB = Thm.assume (ctermL2 (jT (oeq (llen LS) xS)))
              fun applyIH L2 (h_lt:thm) =
                let val zpr = Free("z_pr", natT)
                    val Pr = Term.lambda zpr (lt (llen L2) zpr)
                    val h_lt_x = oeq_rw_2 (Pr, llen LS, xS) hB h_lt
                in applyAUXx L2 h_lt_x end
              val r = stepFn LS applyIH
          in Thm.implies_intr (ctermL2 (jT (oeq (llen LS) xS))) r end
        val inst = beta_norm (Drule.infer_instantiate ctxtL2
              [(("A",0), ctermL2 (lt (llen LS) xS)),(("B",0), ctermL2 (oeq (llen LS) xS)),
               (("C",0), ctermL2 goalC)] disjE_vL2)
        val pm = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB
        val dischLt = Thm.implies_intr (ctermL2 (jT (lt (llen LS) (suc xS)))) pm
        val auxSucx = Thm.forall_intr (ctermL2 LS) dischLt
      in Thm.forall_intr (ctermL2 xS) (Thm.implies_intr (ctermL2 auxX) auxSucx) end
    val LF = Free("L_fin", natlistT)
    val kFin = suc (llen LF)
    val indK = beta_norm (Drule.infer_instantiate ctxtL2
                 [(("Phi",0), ctermL2 PhiMetaAbs),(("k",0), ctermL2 kFin)] meta_nat_induct_v2)
    val auxK = Thm.implies_elim (Thm.implies_elim indK base) step
    val auxKL = Thm.forall_elim (ctermL2 LF) auxK
    val resLF = Thm.implies_elim auxKL (lt_suc_2 (llen LF))
  in (LF, resLF) end;

val () = out "PAIRING_L2_HELPERS_READY\n";

(* ============================================================================
   THE PAIRING LEMMA — hypotheses bundled into one object predicate Phi,
   proved by list strong induction.
   ============================================================================ *)
fun H2body L = let val xf = Free("xh2",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (lmem (inv xf) L))) end;
fun H3body L = let val xf = Free("xh3",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (cong pF (mult xf (inv xf)) oneN))) end;
fun H4body L = let val xf = Free("xh4",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (neg (oeq (inv xf) xf)))) end;
fun H5body L = let val xf = Free("xh5",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (oeq (inv (inv xf)) xf))) end;
fun PhiBody L =
  mkImp (lnodup L)
   (mkImp (H2body L)
     (mkImp (H3body L)
       (mkImp (H4body L)
         (mkImp (H5body L)
           (cong pF (lprod L) oneN)))));

val () = out "PAIRING_PHI_READY\n";

fun useH2 L hF2 z (hm : thm) =
  let val xf = Free("xh2",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (lmem (inv xf) L))
      val inst = allE_at Pabs z hF2
  in mp_at (lmem z L, lmem (inv z) L) inst hm end;
fun useH3 L hF3 z (hm : thm) =
  let val xf = Free("xh3",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (cong pF (mult xf (inv xf)) oneN))
      val inst = allE_at Pabs z hF3
  in mp_at (lmem z L, cong pF (mult z (inv z)) oneN) inst hm end;
fun useH4 L hF4 z (hm : thm) =
  let val xf = Free("xh4",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (neg (oeq (inv xf) xf)))
      val inst = allE_at Pabs z hF4
  in mp_at (lmem z L, neg (oeq (inv z) z)) inst hm end;
fun useH5 L hF5 z (hm : thm) =
  let val xf = Free("xh5",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (oeq (inv (inv xf)) xf))
      val inst = allE_at Pabs z hF5
  in mp_at (lmem z L, oeq (inv (inv z)) z) inst hm end;

fun useH2_2 L hF2 z (hm : thm) =
  let val xf = Free("xh2",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (lmem (inv xf) L))
      val inst = allE_2 Pabs z hF2
  in mp_2 (lmem z L, lmem (inv z) L) inst hm end;
fun useH3_2 L hF3 z (hm : thm) =
  let val xf = Free("xh3",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (cong pF (mult xf (inv xf)) oneN))
      val inst = allE_2 Pabs z hF3
  in mp_2 (lmem z L, cong pF (mult z (inv z)) oneN) inst hm end;
fun useH4_2 L hF4 z (hm : thm) =
  let val xf = Free("xh4",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (neg (oeq (inv xf) xf)))
      val inst = allE_2 Pabs z hF4
  in mp_2 (lmem z L, neg (oeq (inv z) z)) inst hm end;
fun useH5_2 L hF5 z (hm : thm) =
  let val xf = Free("xh5",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (oeq (inv (inv xf)) xf))
      val inst = allE_2 Pabs z hF5
  in mp_2 (lmem z L, oeq (inv (inv z)) z) inst hm end;

val extract_vv      = varify extract;
val llen_remove_vv  = varify llen_remove;
val lt_trans_vv     = varify lt_trans;
val nodup_remove_vv = varify nodup_remove;
val mem_remove_fwd_vv = varify mem_remove_fwd;
val mem_remove_bwd_vv = varify mem_remove_bwd;
val mem_remove_neq_vv = varify mem_remove_neq;
fun extract_2 (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] extract_vv)) hmem;
fun llen_remove_2 (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] llen_remove_vv)) hmem;
fun lt_trans_2 (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("a",0), ctermL2 at),(("b",0), ctermL2 bt),(("c",0), ctermL2 ct)] lt_trans_vv)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun nodup_remove_2 (xt, Lt) hnd =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] nodup_remove_vv)) hnd;
fun mem_remove_fwd_2 (yt, xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("y",0), ctermL2 yt),(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] mem_remove_fwd_vv)) hmem;
fun mem_remove_bwd_2 (yt, xt, Lt) hconj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("y",0), ctermL2 yt),(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] mem_remove_bwd_vv)) hconj;
fun mem_remove_neq_2 (yt, xt, Lt) hnd hmem =  (* mem_remove_neq is a META impl *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("y",0), ctermL2 yt),(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] mem_remove_neq_vv)
  in Thm.implies_elim (Thm.implies_elim inst hnd) hmem end;

val () = out "PAIRING_USEH_READY\n";

(* ---- the pairing lemma proper (ALL on ctxtL2) ---- *)
val pairing_lemma =
  let
    fun stepFn LS applyIH =
      let
        val hND = Thm.assume (ctermL2 (jT (lnodup LS)));
        val hF2 = Thm.assume (ctermL2 (jT (H2body LS)));
        val hF3 = Thm.assume (ctermL2 (jT (H3body LS)));
        val hF4 = Thm.assume (ctermL2 (jT (H4body LS)));
        val hF5 = Thm.assume (ctermL2 (jT (H5body LS)));
        val goalCong = cong pF (lprod LS) oneN;

        fun caseNil hnil =
          let
            val lpc = lprod_cong_2 (LS, lnilC) hnil;
            val lpn = lprodNil_at ();
            val lp1 = oeq_trans OF [lpc, lpn];
            val cr  = cong_refl_2 (pF, oneN);
            val lp1_s = oeq_sym OF [lp1];
            val one_refl = oeqRefl_2 oneN;
          in cong_cong_2 (pF, oneN, lprod LS, oneN, oneN) lp1_s one_refl cr end;

        fun caseCons (a, rest) hcons =
          let
            val consL = lcons a rest;
            val hcons_s = leq_sym OF [hcons];
            val a_in_cons = Thm.implies_elim (lmemConsBwd_2 (a, a, rest))
                              (disjI1_2 (oeq a a, lmem a rest) (oeqRefl_2 a));
            val memA = lmem_transfer_2 (a, consL, LS) hcons_s a_in_cons;
            val congA   = useH3_2 LS hF3 a memA;
            val neqInvA = useH4_2 LS hF4 a memA;
            val memInvA = useH2_2 LS hF2 a memA;
            val memInvA_cons = lmem_transfer_2 (inv a, LS, consL) hcons memInvA;
            val djInvA = Thm.implies_elim (lmemConsFwd_2 (inv a, a, rest)) memInvA_cons;
            val memInvA_rest =
              let
                val cEq = let val heqia = Thm.assume (ctermL2 (jT (oeq (inv a) a)))
                              val ff = mp_2 (oeq (inv a) a, oFalseC) neqInvA heqia
                          in Thm.implies_intr (ctermL2 (jT (oeq (inv a) a)))
                               (Thm.implies_elim (oFalse_elim_2 (lmem (inv a) rest)) ff) end;
                val cMem = let val hm = Thm.assume (ctermL2 (jT (lmem (inv a) rest)))
                           in Thm.implies_intr (ctermL2 (jT (lmem (inv a) rest))) hm end;
              in disjE_2 (oeq (inv a) a, lmem (inv a) rest, lmem (inv a) rest) djInvA cEq cMem end;
            val R = lremove (inv a) rest;
            val hND_cons = lnodup_transfer_2 (LS, consL) hcons hND;
            val cjND = Thm.implies_elim (lnodupConsFwd_2 (a, rest)) hND_cons;
            val a_notin_rest = conjunct1_2 (neg (lmem a rest), lnodup rest) cjND;
            val ndRest = conjunct2_2 (neg (lmem a rest), lnodup rest) cjND;

            val lp_cons = lprodCons_2 (a, rest);
            val lp_LS_cons = lprod_cong_2 (LS, consL) hcons;
            val lp_LS_1 = oeq_trans OF [lp_LS_cons, lp_cons];
            val lp_rest = extract_2 (inv a, rest) memInvA_rest;
            val step1m = mult_cong_r_2 (a, lprod rest, mult (inv a) (lprod R)) lp_rest;
            val assoc = multassoc_2 (a, inv a, lprod R);
            val assoc_s = oeq_sym OF [assoc];
            val lp_LS_final = oeq_trans OF [oeq_trans OF [lp_LS_1, step1m], assoc_s];

            val cong_factor = cong_mult_2 (pF, mult a (inv a), oneN, lprod R, lprod R)
                                congA (cong_refl_2 (pF, lprod R));
            val m1l = mult1l_2 (lprod R);
            val cong_factor2 = cong_cong_2 (pF, mult (mult a (inv a))(lprod R), mult (mult a (inv a))(lprod R),
                                                mult oneN (lprod R), lprod R)
                                 (oeqRefl_2 (mult (mult a (inv a))(lprod R))) m1l cong_factor;
            val lp_LS_final_s = oeq_sym OF [lp_LS_final];
            val cong_LS_R = cong_cong_2 (pF, mult (mult a (inv a))(lprod R), lprod LS, lprod R, lprod R)
                              lp_LS_final_s (oeqRefl_2 (lprod R)) cong_factor2;

            val ltRrest = llen_remove_2 (inv a, rest) memInvA_rest;
            val llc = llenCons_2 (a, rest);
            val llen_LS_cons = llen_cong_2 (LS, consL) hcons;
            val llen_LS_suc = oeq_trans OF [llen_LS_cons, llc];
            val lt_rest_suc = lt_suc_2 (llen rest);
            val llen_LS_suc_s = oeq_sym OF [llen_LS_suc];
            val zPrlt = Free("z_prlt", natT);
            val Prlt = Term.lambda zPrlt (lt (llen rest) zPrlt);
            val lt_rest_LS = oeq_rw_2 (Prlt, suc (llen rest), llen LS) llen_LS_suc_s lt_rest_suc;
            val ltR_LS = lt_trans_2 (llen R, llen rest, llen LS) ltRrest lt_rest_LS;
            val phiR = applyIH R ltR_LS;

            val ndR = nodup_remove_2 (inv a, rest) ndRest;
            fun mem_R_to_rest y hyR = mem_remove_fwd_2 (y, inv a, rest) hyR;
            fun rest_to_LS y hyRest =
              let val mem_cons = Thm.implies_elim (lmemConsBwd_2 (y, a, rest))
                                   (disjI2_2 (oeq y a, lmem y rest) hyRest)
              in lmem_transfer_2 (y, consL, LS) hcons_s mem_cons end;
            fun y_neq_invA y hyR = mem_remove_neq_2 (y, inv a, rest) ndRest hyR;

            val h3R =
              let val yf = Free("yh3r", natT)
                  val Pabs = Term.lambda yf (mkImp (lmem yf R) (cong pF (mult yf (inv yf)) oneN))
                  val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                  val res = useH3_2 LS hF3 yf (rest_to_LS yf (mem_R_to_rest yf hyR))
                  val imp = impI_2 (lmem yf R, cong pF (mult yf (inv yf)) oneN)
                              (Thm.implies_intr (ctermL2 (jT (lmem yf R))) res)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;
            val h4R =
              let val yf = Free("yh4r", natT)
                  val Pabs = Term.lambda yf (mkImp (lmem yf R) (neg (oeq (inv yf) yf)))
                  val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                  val res = useH4_2 LS hF4 yf (rest_to_LS yf (mem_R_to_rest yf hyR))
                  val imp = impI_2 (lmem yf R, neg (oeq (inv yf) yf))
                              (Thm.implies_intr (ctermL2 (jT (lmem yf R))) res)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;
            val h5R =
              let val yf = Free("yh5r", natT)
                  val Pabs = Term.lambda yf (mkImp (lmem yf R) (oeq (inv (inv yf)) yf))
                  val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                  val res = useH5_2 LS hF5 yf (rest_to_LS yf (mem_R_to_rest yf hyR))
                  val imp = impI_2 (lmem yf R, oeq (inv (inv yf)) yf)
                              (Thm.implies_intr (ctermL2 (jT (lmem yf R))) res)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;
            (* (e) H2body R : closed under inv (the hard one) *)
            val h2R =
              let
                val yf = Free("yh2r", natT)
                val Pabs = Term.lambda yf (mkImp (lmem yf R) (lmem (inv yf) R))
                val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                val hyRest = mem_R_to_rest yf hyR
                val hyLS   = rest_to_LS yf hyRest
                val hyNeqIA = y_neq_invA yf hyR
                val memInvY_LS = useH2_2 LS hF2 yf hyLS
                val invY_neq_invA =
                  let val hEq = Thm.assume (ctermL2 (jT (oeq (inv yf) (inv a))))
                      val h5fn = (fn z => fn (hm:thm) => useH5_2 LS hF5 z hm)
                      val yEqA = inv_inj_2 h5fn (yf, a) hyLS memA hEq
                      val Pr = Abs("z", natT, lmem (Bound 0) rest)
                      val memArest = oeq_rw_2 (Pr, yf, a) yEqA hyRest
                      val ff = mp_2 (lmem a rest, oFalseC) a_notin_rest memArest
                  in impI_2 (oeq (inv yf) (inv a), oFalseC)
                       (Thm.implies_intr (ctermL2 (jT (oeq (inv yf) (inv a)))) ff) end;
                val memInvY_cons = lmem_transfer_2 (inv yf, LS, consL) hcons memInvY_LS
                val djInvY = Thm.implies_elim (lmemConsFwd_2 (inv yf, a, rest)) memInvY_cons
                val memInvY_rest =
                  let
                    val cEq = let val hia = Thm.assume (ctermL2 (jT (oeq (inv yf) a)))
                                  val invInvY_eq_invA = inv_cong_2 (inv yf, a) hia
                                  val h5y = useH5_2 LS hF5 yf hyLS
                                  val h5y_s = oeq_sym OF [h5y]
                                  val yEqInvA = oeq_trans OF [h5y_s, invInvY_eq_invA]
                                  val ff = mp_2 (oeq yf (inv a), oFalseC) hyNeqIA yEqInvA
                              in Thm.implies_intr (ctermL2 (jT (oeq (inv yf) a)))
                                   (Thm.implies_elim (oFalse_elim_2 (lmem (inv yf) rest)) ff) end
                    val cMem = let val hm = Thm.assume (ctermL2 (jT (lmem (inv yf) rest)))
                               in Thm.implies_intr (ctermL2 (jT (lmem (inv yf) rest))) hm end
                  in disjE_2 (oeq (inv yf) a, lmem (inv yf) rest, lmem (inv yf) rest) djInvY cEq cMem end;
                val conjBwd = conjI_2 (lmem (inv yf) rest, neg (oeq (inv yf) (inv a))) memInvY_rest invY_neq_invA
                val memInvY_R = mem_remove_bwd_2 (inv yf, inv a, rest) conjBwd
                val imp = impI_2 (lmem yf R, lmem (inv yf) R)
                            (Thm.implies_intr (ctermL2 (jT (lmem yf R))) memInvY_R)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;

            val congR1 =
              let
                val s1 = mp_2 (lnodup R, mkImp (H2body R)(mkImp (H3body R)(mkImp (H4body R)(mkImp (H5body R)(cong pF (lprod R) oneN))))) phiR ndR
                val s2 = mp_2 (H2body R, mkImp (H3body R)(mkImp (H4body R)(mkImp (H5body R)(cong pF (lprod R) oneN)))) s1 h2R
                val s3 = mp_2 (H3body R, mkImp (H4body R)(mkImp (H5body R)(cong pF (lprod R) oneN))) s2 h3R
                val s4 = mp_2 (H4body R, mkImp (H5body R)(cong pF (lprod R) oneN)) s3 h4R
                val s5 = mp_2 (H5body R, cong pF (lprod R) oneN) s4 h5R
              in s5 end;
          in cong_trans_2 (pF, lprod LS, lprod R, oneN) cong_LS_R congR1 end;

        val congLS = list_cases (LS, goalCong) caseNil caseCons;
        val i5 = Thm.implies_intr (ctermL2 (jT (H5body LS))) congLS;
        val r5 = impI_2 (H5body LS, cong pF (lprod LS) oneN) i5;
        val i4 = Thm.implies_intr (ctermL2 (jT (H4body LS))) r5;
        val r4 = impI_2 (H4body LS, mkImp (H5body LS)(cong pF (lprod LS) oneN)) i4;
        val i3 = Thm.implies_intr (ctermL2 (jT (H3body LS))) r4;
        val r3 = impI_2 (H3body LS, mkImp (H4body LS)(mkImp (H5body LS)(cong pF (lprod LS) oneN))) i3;
        val i2 = Thm.implies_intr (ctermL2 (jT (H2body LS))) r3;
        val r2 = impI_2 (H2body LS, mkImp (H3body LS)(mkImp (H4body LS)(mkImp (H5body LS)(cong pF (lprod LS) oneN)))) i2;
        val i1 = Thm.implies_intr (ctermL2 (jT (lnodup LS))) r2;
        val r1 = impI_2 (lnodup LS, mkImp (H2body LS)(mkImp (H3body LS)(mkImp (H4body LS)(mkImp (H5body LS)(cong pF (lprod LS) oneN)))) ) i1;
      in r1 end;
    val (LF, resPhi) = list_strong_induct_2 PhiBody stepFn;
  in varify resPhi end;

val () = out "OK pairing_lemma constructed\n";

(* ============================================================================
   VALIDATION : 0-hyp + aconv intended (inv/p/L schematic Vars after varify).
   ============================================================================ *)
val invV = Var (("inv",0), natT --> natT);
fun invv t = invV $ t;
val pV   = Var (("p",0), natT);
val LV   = Var (("L_fin",0), natlistT);
fun H2bodyV L = let val xf = Free("xh2",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (lmem (invv xf) L))) end;
fun H3bodyV L = let val xf = Free("xh3",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (cong pV (mult xf (invv xf)) (suc ZeroC)))) end;
fun H4bodyV L = let val xf = Free("xh4",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (neg (oeq (invv xf) xf)))) end;
fun H5bodyV L = let val xf = Free("xh5",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (oeq (invv (invv xf)) xf))) end;
val pairing_intended =
  jT (mkImp (lnodup LV)
       (mkImp (H2bodyV LV)
         (mkImp (H3bodyV LV)
           (mkImp (H4bodyV LV)
             (mkImp (H5bodyV LV)
               (cong pV (lprod LV) (suc ZeroC)))))));

val r_pairing =
  let val nh = length (Thm.hyps_of pairing_lemma)
      val ac = (Thm.prop_of pairing_lemma) aconv pairing_intended
  in if nh=0 andalso ac then (out "OK pairing_lemma (0-hyp, aconv intended)\n"; true)
     else (out ("FAIL pairing_lemma (hyps="^Int.toString nh^" aconv="^Bool.toString ac^")\n"
                ^"  got      = "^Syntax.string_of_term ctxtL2 (Thm.prop_of pairing_lemma)^"\n"
                ^"  intended = "^Syntax.string_of_term ctxtL2 pairing_intended^"\n"); false) end;

val pairing_noH3 =
  jT (mkImp (lnodup LV)
       (mkImp (H2bodyV LV)
         (mkImp (H4bodyV LV)
           (mkImp (H5bodyV LV)
             (cong pV (lprod LV) (suc ZeroC))))));
val probe_uses_H3 = not ((Thm.prop_of pairing_lemma) aconv pairing_noH3);
val () = if probe_uses_H3 then out "PROBE_OK pairing_lemma genuinely uses H3 (inverse hyp)\n"
         else out "PROBE_FAIL pairing_lemma dropped H3\n";

val probe_conditional = not ((Thm.prop_of pairing_lemma) aconv (jT (cong pV (lprod LV) (suc ZeroC))));
val () = if probe_conditional then out "PROBE_OK pairing_lemma is conditional (not unconditional)\n"
         else out "PROBE_FAIL pairing_lemma collapsed to unconditional\n";

val () =
  if r_pairing andalso probe_uses_H3 andalso probe_conditional
  then out "PAIRING_OK\n"
  else out "PAIRING_FAILED\n";
