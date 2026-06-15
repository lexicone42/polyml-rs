(* ============================================================================
   FUNDAMENTAL THEOREM OF ARITHMETIC (existence) in Isabelle/Pure on the
   polyml-rs interpreter.  (test: isabelle_fta.rs)
   ----------------------------------------------------------------------------
     fta_existence :
       |- !n. 2 <= n ==> ?ps. all_prime ps /\ product ps = n
   Every natural number n >= 2 is a product of primes.  A 0-hypothesis theorem,
   proved by strong (course-of-values) induction; only classical assumption =
   excluded middle.  This FUSES two strands of the self-derived Isabelle number
   theory: the LIST theory (an inductive natlist + product + all_prime) and the
   classical PRIME theory (the derived prime_cases + prime_divisor_exists).

   PROOF: strong induction on n.  prime_cases n splits 1<n into:
     - n prime: the singleton list (Cons n Nil) -- product = n*1 = n, all_prime
       by prime n.
     - n composite: a proper divisor d (1<d<n, d|n); the `cofactor` lemma turns
       d|n into a cofactor e with 1<e, e<n, n = d*e.  Both d,e < n, so the strong
       IH gives prime-lists pd, pe with products d, e; append them: product
       (append pd pe) = product pd * product pe = d*e = n (product_append), and
       all_prime (append pd pe) (all_prime_append).

   Built (on isabelle_classical_primes.sml) by a 2-phase ultracode pipeline
   (wf_15cdc379-e01): list/product helpers (natlist + product + all_prime +
   product_append + all_prime_append + cofactor) -> FTA (2 seats, both proved it).

   Together with isabelle_euclid.sml (infinitely many primes) and
   isabelle_sqrt2.sml (sqrt 2 irrational), this completes a genuine elementary
   number theory built from first principles on the Rust PolyML interpreter.
   ============================================================================ *)


(* ============================================================================
   ============================================================================
   ***  FTA HELPERS : natlist + product + all_prime + cofactor lemmas  ***
   ----------------------------------------------------------------------------
   Built on the SINGLE FINAL classical/number-theory context.  We extend the
   theory ONE more time (`thyL`) with:
     - a type `natlist` and constructors Nil : natlist, Cons : nat=>natlist=>natlist
     - list equality leq : natlist=>natlist=>o (leq_refl + leq_subst, a la oeq)
     - a structural list_induct axiom
     - append : natlist=>natlist=>natlist  (append_Nil / append_Cons)
     - product : natlist=>nat              (product_Nil / product_Cons)
     - all_prime : natlist=>o              (all_prime_Nil + all_prime_Cons iff)
   re-init ONE final context ctxtL / ctermL, re-varify EVERY reused base lemma
   onto it, and route ALL new cterms through ctermL.

   PROVED (each 0-hyp / 0-extra-hyp, validated aconv):
     product_append   : oeq (product (append a b)) (mult (product a) (product b))
     all_prime_append : jT (all_prime a) ==> jT (all_prime b)
                          ==> jT (all_prime (append a b))
     cofactor         : jT (lt 1 d) ==> jT (lt d n) ==> jT (dvd d n)
                          ==> jT (Ex (%e. Conj (Conj (lt 1 e) (lt e n))
                                               (oeq n (mult d e))))
   ============================================================================ *)

val () = out "FTA_HELPERS_BEGIN\n";

(* ---- the natlist type + constructors on thyL0 ---- *)
val thyL0 = Sign.add_types_global [(Binding.name "natlist",0,NoSyn)] thyS2;
val natlistN = Sign.full_name thyL0 (Binding.name "natlist");
val natlistT = Type (natlistN,[]);
val listpredT = natlistT --> oT;       (* natlist => o *)

val thyL1 = Sign.add_consts
  [(Binding.name "Nil",     natlistT, NoSyn),
   (Binding.name "Cons",    natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "append",  natlistT --> natlistT --> natlistT, NoSyn),
   (Binding.name "product", natlistT --> natT, NoSyn),
   (Binding.name "leq",     natlistT --> natlistT --> oT, NoSyn),
   (Binding.name "all_prime", natlistT --> oT, NoSyn)] thyL0;

fun lcnst nm T = Const (Sign.full_name thyL1 (Binding.name nm), T);
val NilC     = lcnst "Nil" natlistT;
val ConsC    = lcnst "Cons" (natT --> natlistT --> natlistT);
fun cons x l = ConsC $ x $ l;
val appendC  = lcnst "append" (natlistT --> natlistT --> natlistT);
fun append s t = appendC $ s $ t;
val productC = lcnst "product" (natlistT --> natT);
fun product l = productC $ l;
val leqC     = lcnst "leq" (natlistT --> natlistT --> oT);
fun leq s t = leqC $ s $ t;
val all_primeC = lcnst "all_prime" (natlistT --> oT);
fun all_prime l = all_primeC $ l;

(* ---- list-equality axioms (mirror oeq_refl / oeq_subst) ---- *)
val aL = Free ("a", natlistT); val bL = Free ("b", natlistT);
val PL = Free ("P", listpredT);
val ((_,leq_refl_ax),  thyL2) = Thm.add_axiom_global (Binding.name "leq_refl",
      jT (leq aL aL)) thyL1;
val ((_,leq_subst_ax), thyL3) = Thm.add_axiom_global (Binding.name "leq_subst",
      Logic.mk_implies (jT (leq aL bL), Logic.mk_implies (jT (PL $ aL), jT (PL $ bL)))) thyL2;

(* ---- list_induct : P Nil ==> (!!x l. P l ==> P (Cons x l)) ==> P k ---- *)
val PhiLT = natlistT --> propT;
val PhiL  = Free ("PhiL", PhiLT);
val xLI   = Free ("x", natT);
val lLI   = Free ("l", natlistT);
val kLI   = Free ("k", natlistT);
val list_induct_prop =
  Logic.mk_implies (PhiL $ NilC,
    Logic.mk_implies (Logic.all xLI (Logic.all lLI
        (Logic.mk_implies (PhiL $ lLI, PhiL $ (cons xLI lLI)))),
      PhiL $ kLI));
val ((_,list_induct_ax), thyL4) =
  Thm.add_axiom_global (Binding.name "list_induct", list_induct_prop) thyL3;

(* ---- append recursion equations (oeq on nats? NO — append returns natlist;
       use leq for list-level equations) ---- *)
val mAp = Free ("m", natlistT);
val xAp = Free ("x", natT);  val lAp = Free ("l", natlistT);
val ((_,append_Nil_ax),  thyL5) = Thm.add_axiom_global (Binding.name "append_Nil",
      jT (leq (append NilC mAp) mAp)) thyL4;
val ((_,append_Cons_ax), thyL6) = Thm.add_axiom_global (Binding.name "append_Cons",
      jT (leq (append (cons xAp lAp) mAp) (cons xAp (append lAp mAp)))) thyL5;

(* ---- product recursion equations (oeq on nats) ---- *)
val ((_,product_Nil_ax),  thyL7) = Thm.add_axiom_global (Binding.name "product_Nil",
      jT (oeq (product NilC) (suc ZeroC))) thyL6;
val ((_,product_Cons_ax), thyL8) = Thm.add_axiom_global (Binding.name "product_Cons",
      jT (oeq (product (cons xAp lAp)) (mult xAp (product lAp)))) thyL7;

(* ---- all_prime axioms : Nil is true; Cons is the iff (Conj of two Imps) ---- *)
val ((_,all_prime_Nil_ax), thyL9) = Thm.add_axiom_global (Binding.name "all_prime_Nil",
      jT (all_prime NilC)) thyL8;
(* all_prime_Cons : (all_prime (Cons x l))  <->  Conj (prime x) (all_prime l)
   encoded as the two directional axioms (the <-> is their conjunction). *)
val ((_,all_prime_Cons_fwd_ax), thyL10) = Thm.add_axiom_global (Binding.name "all_prime_Cons_fwd",
      Logic.mk_implies (jT (all_prime (cons xAp lAp)),
                        jT (mkConj (prime2 xAp) (all_prime lAp)))) thyL9;
val ((_,all_prime_Cons_bwd_ax), thyL) = Thm.add_axiom_global (Binding.name "all_prime_Cons_bwd",
      Logic.mk_implies (jT (mkConj (prime2 xAp) (all_prime lAp)),
                        jT (all_prime (cons xAp lAp)))) thyL10;

(* ---- THE ONE FINAL CONTEXT ctxtL / ctermL ---- *)
val ctxtL  = Proof_Context.init_global thyL;
val ctermL = Thm.cterm_of ctxtL;

val () = out "FTA_CONSTS_READY\n";

(* ---- re-varify EVERY reused base axiom/lemma onto ctxtL ---- *)
val oeq_refl_vL    = varify oeq_refl;
val oeq_subst_vL   = varify oeq_subst;
val add_0_vL       = varify add_0;
val add_Suc_vL     = varify add_Suc;
val add_0_right_vL = varify add_0_right;
val add_Suc_right_vL = varify add_Suc_right;
val mult_0_vL        = varify mult_0;
val mult_Suc_vL      = varify mult_Suc;
val mult_0_right_vL  = varify mult_0_right;
val mult_Suc_right_vL= varify mult_Suc_right;
val mult_1_right_vL  = varify mult_1_right;
val mult_1_left_vL   = varify mult_1_left;
val right_distrib_vL = varify right_distrib;
val Suc_inj_vL       = varify Suc_inj_ax;
val Suc_neq_Zero_vL  = varify Suc_neq_Zero_ax;
val exI_vL           = varify exI_ax;
val exE_vL           = varify exE_ax;
val oFalse_elim_vL   = varify oFalse_elim_ax;
val conjI_vL         = varify conjI_ax;
val conjunct1_vL     = varify conjunct1_ax;
val conjunct2_vL     = varify conjunct2_ax;
val mp_vL            = varify mp_ax;
val impI_vL          = varify impI_ax;
val ne0_suc_vL       = varify ne0_suc;
val gt1_of_ne0_ne1_vL= varify gt1_of_ne0_ne1;
val lt_irrefl_vL     = varify lt_irrefl;
val le_trans_vL      = varify le_trans;
val leq_refl_vL      = varify leq_refl_ax;
val leq_subst_vL     = varify leq_subst_ax;
val list_induct_vL   = varify list_induct_ax;
val append_Nil_vL    = varify append_Nil_ax;
val append_Cons_vL   = varify append_Cons_ax;
val product_Nil_vL   = varify product_Nil_ax;
val product_Cons_vL  = varify product_Cons_ax;
val all_prime_Nil_vL     = varify all_prime_Nil_ax;
val all_prime_Cons_fwd_vL= varify all_prime_Cons_fwd_ax;
val all_prime_Cons_bwd_vL= varify all_prime_Cons_bwd_ax;

(* ---- ground instantiators on ctxtL ---- *)
fun add0L_at t         = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] add_0_vL);
fun addSucL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtL
                            [(("m",0), ctermL mt),(("n",0), ctermL nt)] add_Suc_vL);
fun add0rL_at t        = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] add_0_right_vL);
fun addSrL_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtL
                            [(("m",0), ctermL mt),(("n",0), ctermL nt)] add_Suc_right_vL);
fun mult0L_at t        = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] mult_0_vL);
fun multSucL_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtL
                            [(("m",0), ctermL mt),(("n",0), ctermL nt)] mult_Suc_vL);
fun mult0rL_at t       = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] mult_0_right_vL);
fun multSrL_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtL
                            [(("n",0), ctermL nt),(("m",0), ctermL mt)] mult_Suc_right_vL);
fun mult1rL_at t       = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] mult_1_right_vL);
fun mult1lL_at t       = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] mult_1_left_vL);
fun oeqreflL_at t      = beta_norm (Drule.infer_instantiate ctxtL [(("a",0), ctermL t)] oeq_refl_vL);
fun Suc_inj_atL (uT,vT)= beta_norm (Drule.infer_instantiate ctxtL
                            [(("a",0), ctermL uT),(("b",0), ctermL vT)] Suc_inj_vL);
fun Suc_neq_Zero_atL t = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL t)] Suc_neq_Zero_vL);
fun rdistL_at (aT,bT,kT)= beta_norm (Drule.infer_instantiate ctxtL
        [(("m",0), ctermL aT),(("n",0), ctermL bT),(("k",0), ctermL kT)] right_distrib_vL);

(* ---- oeq congruence helpers on ctxtL (nat-level) ---- *)
fun mult_cong_lL (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL pT), (("b",0), ctermL qT)] oeq_subst_vL);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtL [(("a",0), ctermL (mult pT kT))] oeq_refl_vL);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rL (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL pT), (("b",0), ctermL qT)] oeq_subst_vL);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtL [(("a",0), ctermL (mult hT pT))] oeq_refl_vL);
  in inst OF [hpq, refl_hp] end;
fun add_cong_lL (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL pT), (("b",0), ctermL qT)] oeq_subst_vL);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtL [(("a",0), ctermL (add pT kT))] oeq_refl_vL);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rL (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL pT), (("b",0), ctermL qT)] oeq_subst_vL);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtL [(("a",0), ctermL (add hT pT))] oeq_refl_vL);
  in inst OF [hpq, refl_hp] end;

(* le on ctxtL : le m n == Ex(%p. oeq n (add m (Bound 0))).  le_introL via exI. *)
fun le_introL (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL w)] exI_vL);
  in inst OF [hyp] end;

(* exI / exE / conj / mp / impI on ctxtL (object-nat existentials) *)
fun exI_atL Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("P",0), ctermL Pabs), (("a",0), ctermL at)] exI_vL)
  in Thm.implies_elim inst hbody end;
fun exE_elimL (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermL hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermL wF) (Thm.implies_intr (ctermL hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtL
                    [(("P",0), ctermL Pabs), (("Q",0), ctermL goalC)] exE_vL);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
fun conjI_atL (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("A",0), ctermL At), (("B",0), ctermL Bt)] conjI_vL)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atL (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("A",0), ctermL At), (("B",0), ctermL Bt)] conjunct1_vL)
  in Thm.implies_elim inst hC end;
fun conjunct2_atL (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("A",0), ctermL At), (("B",0), ctermL Bt)] conjunct2_vL)
  in Thm.implies_elim inst hC end;
fun mp_atL (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("A",0), ctermL At), (("B",0), ctermL Bt)] mp_vL)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_atL (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("A",0), ctermL At), (("B",0), ctermL Bt)] impI_vL)
  in Thm.implies_elim inst hImpThm end;
fun oFalse_elimL_at rT = beta_norm (Drule.infer_instantiate ctxtL
        [(("R",0), ctermL rT)] oFalse_elim_vL);

(* ground instantiators for lifted number-theory rules on ctxtL *)
fun ne0_suc_atL dt hne0 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL [(("d",0), ctermL dt)] ne0_suc_vL)
  in Thm.implies_elim inst hne0 end;
fun gt1_of_ne0_ne1_atL dt hne0 hne1 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL [(("d",0), ctermL dt)] gt1_of_ne0_ne1_vL)
  in Thm.implies_elim (Thm.implies_elim inst hne0) hne1 end;
fun lt_irrefl_atL nt hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL [(("n",0), ctermL nt)] lt_irrefl_vL)
  in Thm.implies_elim inst hlt end;
fun le_trans_atL (mt,nt,kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("m",0), ctermL mt),(("n",0), ctermL nt),(("k",0), ctermL kt)] le_trans_vL)
  in (inst OF [h1]) OF [h2] end;

(* lt on ctxtL: lt m n == le (Suc m) n (same abbreviation) *)
fun ltL mT nT = le (suc mT) nT;

(* ---- leq congruence/symmetry derived from leq_refl + leq_subst (a la oeq) ---- *)
fun leqreflL_at t = beta_norm (Drule.infer_instantiate ctxtL [(("a",0), ctermL t)] leq_refl_vL);

(* leq_sym : leq a b ==> leq b a *)
val leq_sym =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT);
    val Pabs = Abs("z", natlistT, leq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL aF), (("b",0), ctermL bF)] leq_subst_vL);
    val refl_aa = leqreflL_at aF;
    val step = inst OF [Thm.assume (ctermL (jT (leq aF bF))), refl_aa];
  in varify (Thm.implies_intr (ctermL (jT (leq aF bF))) step) end;
val leq_sym_vL = varify leq_sym;
fun leq_sym_atL (at,bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("a",0), ctermL at),(("b",0), ctermL bt)] leq_sym_vL)
  in Thm.implies_elim inst h end;

(* leq_trans : leq a b ==> leq b c ==> leq a c *)
val leq_trans =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT); val cF = Free("c",natlistT);
    val Pabs = Abs("z", natlistT, leq aF (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL bF), (("b",0), ctermL cF)] leq_subst_vL);
    val H1 = Thm.assume (ctermL (jT (leq aF bF)));
    val H2 = Thm.assume (ctermL (jT (leq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (ctermL (jT (leq bF cF))) step;
    val t1 = Thm.implies_intr (ctermL (jT (leq aF bF))) t0;
  in varify t1 end;
val leq_trans_vL = varify leq_trans;
fun leq_trans_atL (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL
        [(("a",0), ctermL at),(("b",0), ctermL bt),(("c",0), ctermL ct)] leq_trans_vL)
  in (inst OF [h1]) OF [h2] end;

val () = out "FTA_LEQ_READY\n";

(* ---- product_cong : leq a b ==> oeq (product a) (product b)  (subst on leq) ---- *)
fun product_cong_at (at, bt) hleq =
  let
    val Pabs = Abs("z", natlistT, oeq (product at) (product (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL at), (("b",0), ctermL bt)] leq_subst_vL);
    val refl_pa = oeqreflL_at (product at);
  in inst OF [hleq, refl_pa] end;

(* ---- all_prime_cong : leq a b ==> jT (all_prime a) ==> jT (all_prime b) ---- *)
fun all_prime_cong_at (at, bt) hleq hap =
  let
    val Pabs = Abs("z", natlistT, all_prime (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxtL
          [(("P",0), ctermL Pabs), (("a",0), ctermL at), (("b",0), ctermL bt)] leq_subst_vL);
  in (inst OF [hleq]) OF [hap] end;

(* ground instances of the recursion equations *)
fun append_Nil_at mt = beta_norm (Drule.infer_instantiate ctxtL [(("m",0), ctermL mt)] append_Nil_vL);
fun append_Cons_at (xt,lt,mt) = beta_norm (Drule.infer_instantiate ctxtL
        [(("x",0), ctermL xt),(("l",0), ctermL lt),(("m",0), ctermL mt)] append_Cons_vL);
val product_Nil_thm = product_Nil_vL;   (* oeq (product Nil) (Suc Zero) *)
fun product_Cons_at (xt,lt) = beta_norm (Drule.infer_instantiate ctxtL
        [(("x",0), ctermL xt),(("l",0), ctermL lt)] product_Cons_vL);
fun all_prime_Cons_fwd_at (xt,lt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtL
        [(("x",0), ctermL xt),(("l",0), ctermL lt)] all_prime_Cons_fwd_vL)) h;
fun all_prime_Cons_bwd_at (xt,lt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtL
        [(("x",0), ctermL xt),(("l",0), ctermL lt)] all_prime_Cons_bwd_vL)) h;

(* ---- mult_assoc lifted onto ctxtL ---- *)
val mult_assoc_vL = varify mult_assoc;
fun multassocL_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtL
        [(("m",0), ctermL mt),(("n",0), ctermL nt),(("k",0), ctermL kt)] mult_assoc_vL);

val () = out "FTA_CONG_READY\n";

(* ============================================================================
   product_append : oeq (product (append a b)) (mult (product a) (product b))
   BY list induction on a.
     Nil:  product (append Nil b) = product b      [append_Nil + product_cong]
                                  = mult 1 (product b)   [mult_1_left sym]
                                  = mult (product Nil) (product b)  [product_Nil sym in the mult-left]
     Cons x l (IH : oeq (product (append l b)) (mult (product l)(product b))):
        product (append (Cons x l) b)
          = product (Cons x (append l b))           [append_Cons + product_cong]
          = mult x (product (append l b))            [product_Cons]
          = mult x (mult (product l) (product b))    [IH, mult_cong_r]
          = mult (mult x (product l)) (product b)    [mult_assoc sym]
          = mult (product (Cons x l)) (product b)    [product_Cons sym in mult-left]
   ============================================================================ *)
val product_append =
  let
    val bF = Free("b", natlistT);
    (* induction predicate (meta-prop wrapper) on a:  %z. jT (oeq (product (append z b))
       (mult (product z) (product b))).  No object Ex/le/dvd of bound var -> Abs OK,
       but build with Term.lambda over a Free to be safe. *)
    val zL = Free("z_pa", natlistT);
    val Qpred = Term.lambda zL
        (jT (oeq (product (append zL bF)) (mult (product zL) (product bF))));
    val kF = Free("a", natlistT);   (* name -> Var(("a",0)) after varify, matches intended *)
    val ind = beta_norm (Drule.infer_instantiate ctxtL
          [(("PhiL",0), ctermL Qpred), (("k",0), ctermL kF)] list_induct_vL);

    (* BASE : a = Nil *)
    val base =
      let
        val ap0   = append_Nil_at bF;                          (* leq (append Nil b) b *)
        val pcong = product_cong_at (append NilC bF, bF) ap0;  (* oeq (product (append Nil b)) (product b) *)
        (* product b = mult 1 (product b) = mult (product Nil) (product b) *)
        val m1l   = mult1lL_at (product bF);                   (* oeq (mult 1 (product b)) (product b) *)
        val m1ls  = oeq_sym OF [m1l];                          (* oeq (product b) (mult 1 (product b)) *)
        (* mult (product Nil) (product b) : rewrite the 1 to (product Nil) using product_Nil sym *)
        val pNil  = product_Nil_thm;                           (* oeq (product Nil) (Suc Zero) *)
        val pNils = oeq_sym OF [pNil];                         (* oeq (Suc Zero) (product Nil) *)
        val cong  = mult_cong_lL (suc ZeroC, product NilC, product bF) pNils;
                                                               (* oeq (mult 1 (product b)) (mult (product Nil)(product b)) *)
        val rhs   = oeq_trans OF [m1ls, cong];                 (* oeq (product b) (mult (product Nil)(product b)) *)
      in oeq_trans OF [pcong, rhs] end;                        (* oeq (product (append Nil b)) (mult (product Nil)(product b)) *)

    (* STEP : !!x l. Q l ==> Q (Cons x l) *)
    val step =
      let
        val xF = Free("x_pa", natT); val lF = Free("l_pa", natlistT);
        val ihprop = jT (oeq (product (append lF bF)) (mult (product lF) (product bF)));
        val IH = Thm.assume (ctermL ihprop);
        val apC   = append_Cons_at (xF, lF, bF);               (* leq (append (Cons x l) b) (Cons x (append l b)) *)
        val pcong = product_cong_at (append (cons xF lF) bF, cons xF (append lF bF)) apC;
                                                               (* oeq (product (append (Cons x l) b)) (product (Cons x (append l b))) *)
        val pCons1= product_Cons_at (xF, append lF bF);        (* oeq (product (Cons x (append l b))) (mult x (product (append l b))) *)
        val e1    = oeq_trans OF [pcong, pCons1];              (* = mult x (product (append l b)) *)
        val congIH= mult_cong_rL (xF, product (append lF bF), mult (product lF) (product bF)) IH;
                                                               (* oeq (mult x (product (append l b))) (mult x (mult (product l)(product b))) *)
        val e2    = oeq_trans OF [e1, congIH];                 (* = mult x (mult (product l)(product b)) *)
        val assoc = multassocL_at (xF, product lF, product bF);(* oeq (mult (mult x (product l))(product b)) (mult x (mult (product l)(product b))) *)
        val assocs= oeq_sym OF [assoc];                        (* oeq (mult x (mult (product l)(product b))) (mult (mult x (product l))(product b)) *)
        val e3    = oeq_trans OF [e2, assocs];                 (* = mult (mult x (product l))(product b) *)
        (* mult x (product l) = product (Cons x l)  via product_Cons sym, in mult-left *)
        val pCons2= product_Cons_at (xF, lF);                  (* oeq (product (Cons x l)) (mult x (product l)) *)
        val pCons2s = oeq_sym OF [pCons2];                     (* oeq (mult x (product l)) (product (Cons x l)) *)
        val congP = mult_cong_lL (mult xF (product lF), product (cons xF lF), product bF) pCons2s;
                                                               (* oeq (mult (mult x (product l))(product b)) (mult (product (Cons x l))(product b)) *)
        val stepconcl = oeq_trans OF [e3, congP];              (* = mult (product (Cons x l))(product b) *)
        val inner = Thm.implies_intr (ctermL ihprop) stepconcl;
      in Thm.forall_intr (ctermL xF) (Thm.forall_intr (ctermL lF) inner) end;

    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step;
  in varify r2 end;

(* validation *)
fun checkL (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtL (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtL intended ^ "\n");
          false)
  end;

val aVL = Var (("a",0), natlistT);
val bVL = Var (("b",0), natlistT);
val product_append_intended =
  jT (oeq (product (append aVL bVL)) (mult (product aVL) (product bVL)));
val r_product_append = checkL ("product_append", product_append, product_append_intended);

(* ============================================================================
   all_prime_append : jT (all_prime a) ==> jT (all_prime b)
                        ==> jT (all_prime (append a b))
   BY list induction on a.
     Nil:  all_prime (append Nil b) <- all_prime b  [append_Nil + all_prime_cong]
           (the all_prime a = all_prime Nil premise is discharged trivially / unused
            beyond being present in the implication shape).
     Cons x l (IH : all_prime l ==> all_prime b ==> all_prime (append l b)):
        all_prime (Cons x l) -> (prime x AND all_prime l)  [all_prime_Cons_fwd]
        IH (all_prime l)(all_prime b) -> all_prime (append l b)
        (prime x) AND (all_prime (append l b)) -> all_prime (Cons x (append l b))
                                                  [all_prime_Cons_bwd]
        append (Cons x l) b ~ Cons x (append l b)  [append_Cons], transport back.
   ============================================================================ *)
val all_prime_append =
  let
    val bF = Free("b", natlistT);
    val hBprop = jT (all_prime bF);
    (* induction predicate on a:  %z. jT (all_prime z) ==> jT (all_prime (append z b)).
       (b is fixed; we carry the all_prime b premise as a separate assumption.) *)
    val zL = Free("z_ap", natlistT);
    val Qpred = Term.lambda zL
        (Logic.mk_implies (jT (all_prime zL), jT (all_prime (append zL bF))));
    val kF = Free("a", natlistT);    (* -> Var(("a",0)) after varify *)
    val ind = beta_norm (Drule.infer_instantiate ctxtL
          [(("PhiL",0), ctermL Qpred), (("k",0), ctermL kF)] list_induct_vL);

    val hB = Thm.assume (ctermL hBprop);

    (* BASE : all_prime Nil ==> all_prime (append Nil b) *)
    val base =
      let
        val hNil = Thm.assume (ctermL (jT (all_prime NilC)));    (* unused content; shape only *)
        val ap0  = append_Nil_at bF;                             (* leq (append Nil b) b *)
        val ap0s = leq_sym_atL (append NilC bF, bF) ap0;         (* leq b (append Nil b) *)
        val concl= all_prime_cong_at (bF, append NilC bF) ap0s hB;  (* all_prime (append Nil b) *)
      in Thm.implies_intr (ctermL (jT (all_prime NilC))) concl end;

    (* STEP : !!x l. (all_prime l ==> all_prime (append l b))
                       ==> (all_prime (Cons x l) ==> all_prime (append (Cons x l) b)) *)
    val step =
      let
        val xF = Free("x_ap", natT); val lF = Free("l_ap", natlistT);
        val ihprop = Logic.mk_implies (jT (all_prime lF), jT (all_prime (append lF bF)));
        val IH = Thm.assume (ctermL ihprop);
        val hCons = Thm.assume (ctermL (jT (all_prime (cons xF lF))));   (* all_prime (Cons x l) *)
        val conj  = all_prime_Cons_fwd_at (xF, lF) hCons;       (* Conj (prime x) (all_prime l) *)
        val hPrimeX = conjunct1_atL (prime2 xF, all_prime lF) conj;  (* prime x *)
        val hAPl    = conjunct2_atL (prime2 xF, all_prime lF) conj;  (* all_prime l *)
        val hAPlb   = Thm.implies_elim IH hAPl;                 (* all_prime (append l b) *)
        val conjBwd = conjI_atL (prime2 xF, all_prime (append lF bF)) hPrimeX hAPlb;
                                                               (* Conj (prime x) (all_prime (append l b)) *)
        val apCons  = all_prime_Cons_bwd_at (xF, append lF bF) conjBwd;
                                                               (* all_prime (Cons x (append l b)) *)
        (* transport via append_Cons : append (Cons x l) b ~ Cons x (append l b) *)
        val apC     = append_Cons_at (xF, lF, bF);             (* leq (append (Cons x l) b) (Cons x (append l b)) *)
        val apCs    = leq_sym_atL (append (cons xF lF) bF, cons xF (append lF bF)) apC;
                                                               (* leq (Cons x (append l b)) (append (Cons x l) b) *)
        val concl   = all_prime_cong_at (cons xF (append lF bF), append (cons xF lF) bF) apCs apCons;
                                                               (* all_prime (append (Cons x l) b) *)
        val inner   = Thm.implies_intr (ctermL (jT (all_prime (cons xF lF)))) concl;
        val withIH  = Thm.implies_intr (ctermL ihprop) inner;
      in Thm.forall_intr (ctermL xF) (Thm.forall_intr (ctermL lF) withIH) end;

    val r1   = Thm.implies_elim ind base;
    val rAk  = Thm.implies_elim r1 step;        (* all_prime a ==> all_prime (append a b)  (a := kF) *)
    val hAk  = Thm.assume (ctermL (jT (all_prime kF)));
    val apab = Thm.implies_elim rAk hAk;        (* all_prime (append a b) *)
    val d1   = Thm.implies_intr (ctermL hBprop) apab;            (* all_prime b ==> ... *)
    val d2   = Thm.implies_intr (ctermL (jT (all_prime kF))) d1; (* all_prime a ==> all_prime b ==> ... *)
  in varify d2 end;

val all_prime_append_intended =
  Logic.mk_implies (jT (all_prime aVL),
    Logic.mk_implies (jT (all_prime bVL), jT (all_prime (append aVL bVL))));
val r_all_prime_append = checkL ("all_prime_append", all_prime_append, all_prime_append_intended);

(* ============================================================================
   ARITHMETIC PREREQS for cofactor (proved inline on ctxtL)
   ============================================================================ *)

(* n_ne0_of_ltXn : from jT (lt x n) get jT (neg (oeq n Zero)).
     lt x n = le (Suc x) n = Ex p. oeq n (add (Suc x) p).  exE witness p:
       n = add (Suc x) p = Suc(add x p)  [add_Suc]  =/= 0  [Suc_neq_Zero]. *)
fun n_ne0_of_ltXn (xT, nF) h_lt =
  let
    val Pabs = Abs("p", natT, oeq nF (add (suc xT) (Bound 0)));
    val ez   = Thm.assume (ctermL (jT (oeq nF ZeroC)));
    fun body p (hp : thm) =                              (* hp : oeq n (add (Suc x) p) *)
      let
        val aS    = addSucL_at (xT, p);                  (* (Suc x + p) = Suc (x + p) *)
        val n_Sp  = oeq_trans OF [hp, aS];               (* n = Suc (x + p) *)
        val z_Sp  = oeq_trans OF [oeq_sym OF [ez], n_Sp];(* 0 = Suc (x + p) *)
        val Sp_z  = oeq_sym OF [z_Sp];                   (* Suc (x + p) = 0 *)
      in (Suc_neq_Zero_atL (add xT p)) OF [Sp_z] end;    (* oFalse *)
    val falseThm = exE_elimL (Pabs, oFalseC) h_lt "wp" body;
    val imp = Thm.implies_intr (ctermL (jT (oeq nF ZeroC))) falseThm;
  in impI_atL (oeq nF ZeroC, oFalseC) imp end;           (* jT (neg (oeq n 0)) *)

(* mult_le_mono_r : jT (le j k) ==> jT (le (mult j c) (mult k c))   (right factor c fixed)
     le j k = Ex p. oeq k (add j p).  exE witness p:
       mult k c = mult (add j p) c = add (mult j c) (mult p c)   [right_distrib]
       => le (mult j c)(mult k c) witness (mult p c). *)
fun mult_le_mono_r (jT_, kT, cT) h_le =
  let
    val Pabs  = Abs("p", natT, oeq kT (add jT_ (Bound 0)));
    val goalC = le (mult jT_ cT) (mult kT cT);
    fun body p (hp : thm) =                              (* hp : oeq k (add j p) *)
      let
        val cong = mult_cong_lL (kT, add jT_ p, cT) hp;  (* (k*c) = ((j+p)*c) *)
        val rd   = rdistL_at (jT_, p, cT);               (* ((j+p)*c) = (j*c + p*c) *)
        val keq  = oeq_trans OF [cong, rd];              (* (k*c) = (j*c + p*c) *)
      in le_introL (mult jT_ cT, mult kT cT, mult p cT) keq end;
  in exE_elimL (Pabs, goalC) h_le "wp" body end;

(* mult2_eq_add : oeq (mult (Suc(Suc Zero)) e) (add e e)
     mult (Suc(Suc 0)) e = add e (mult (Suc 0) e)   [mult_Suc]
                         = add e e                    [mult_1_left + cong] *)
fun mult2_eq_add eT =
  let
    val mS  = multSucL_at (suc ZeroC, eT);              (* mult (Suc(Suc 0)) e = add e (mult (Suc 0) e) *)
    val m1  = mult1lL_at eT;                            (* mult (Suc 0) e = e *)
    val cong= add_cong_rL (eT, mult (suc ZeroC) eT, eT) m1;  (* add e (mult (Suc 0) e) = add e e *)
  in oeq_trans OF [mS, cong] end;                       (* mult (Suc(Suc 0)) e = add e e *)

(* le_rewrite : oeq m m' ==> oeq n n' ==> jT (le m n) ==> jT (le m' n') *)
fun le_rewrite (mT, mT', nT, nT') (h_mm : thm) (h_nn : thm) (h_le : thm) =
  let
    val Pabs  = Abs("w", natT, oeq nT (add mT (Bound 0)));
    val goalC = le mT' nT';
    fun body w (hw : thm) =                              (* hw : oeq n (add m w) *)
      let
        val n'_n   = oeq_sym OF [h_nn];                  (* oeq n' n *)
        val n'_amw = oeq_trans OF [n'_n, hw];            (* oeq n' (add m w) *)
        val cong   = add_cong_lL (mT, mT', w) h_mm;      (* oeq (add m w) (add m' w) *)
        val n'_am'w= oeq_trans OF [n'_amw, cong];        (* oeq n' (add m' w) *)
      in le_introL (mT', nT', w) n'_am'w end;
  in exE_elimL (Pabs, goalC) h_le "wr" body end;

val () = out "FTA_ARITH_READY\n";

(* ============================================================================
   cofactor : jT (lt 1 d) ==> jT (lt d n) ==> jT (dvd d n)
                ==> jT (Ex (%e. Conj (Conj (lt 1 e) (lt e n)) (oeq n (mult d e))))
   ============================================================================ *)
val two = suc (suc ZeroC);

val cofactor =
  let
    val dF = Free("d", natT); val nF = Free("n", natT);
    val h_lt1dP = jT (lt (suc ZeroC) dF);     (* lt 1 d == le 2 d *)
    val h_ltdnP = jT (lt dF nF);              (* lt d n == le (Suc d) n *)
    val h_dvdP  = jT (dvd dF nF);             (* Ex k. oeq n (mult d k) *)
    val h_lt1d  = Thm.assume (ctermL h_lt1dP);
    val h_ltdn  = Thm.assume (ctermL h_ltdnP);
    val h_dvd   = Thm.assume (ctermL h_dvdP);

    (* goal existential (capture-avoiding: oeq/mult/lt of bound var -> lt injects Ex,
       so build with Term.lambda over a Free) *)
    val resAbs =
      let val eF = Free("e_co", natT)
      in Term.lambda eF (mkConj (mkConj (lt (suc ZeroC) eF) (lt eF nF)) (oeq nF (mult dF eF))) end;
    val goalEx = mkEx resAbs;

    (* n != 0 from lt d n *)
    val h_n_ne0 = n_ne0_of_ltXn (dF, nF) h_ltdn;       (* jT (neg (oeq n 0)) *)

    val PabsK = Abs("k", natT, oeq nF (mult dF (Bound 0)));  (* dvd d n body *)
    fun dvdBody e (he : thm) =                          (* he : oeq n (mult d e) *)
      let
        (* ---- e != 0 ----  e=0 => n = mult d 0 = 0, contra n!=0 *)
        val e_ne0 =
          let
            val hez = Thm.assume (ctermL (jT (oeq e ZeroC)));      (* oeq e 0 *)
            val congr = mult_cong_rL (dF, e, ZeroC) hez;           (* (d*e) = (d*0) *)
            val md0_0 = mult0rL_at dF;                             (* (d*0) = 0 *)
            val n_de  = he;                                        (* n = (d*e) *)
            val n_d0  = oeq_trans OF [n_de, congr];                (* n = (d*0) *)
            val n_0   = oeq_trans OF [n_d0, md0_0];                (* n = 0 *)
            val fls   = mp_atL (oeq nF ZeroC, oFalseC) h_n_ne0 n_0;(* oFalse *)
          in impI_atL (oeq e ZeroC, oFalseC)
               (Thm.implies_intr (ctermL (jT (oeq e ZeroC))) fls) end;  (* neg (oeq e 0) *)

        (* ---- e != 1 ----  e=1 => n = mult d 1 = d, then lt d n & oeq n d => lt d d => oFalse *)
        val e_ne1 =
          let
            val he1 = Thm.assume (ctermL (jT (oeq e (suc ZeroC))));(* oeq e 1 *)
            val congr = mult_cong_rL (dF, e, suc ZeroC) he1;       (* (d*e) = (d*1) *)
            val md1_d = mult1rL_at dF;                             (* (d*1) = d *)
            val n_de  = he;                                        (* n = (d*e) *)
            val n_d1  = oeq_trans OF [n_de, congr];                (* n = (d*1) *)
            val n_d   = oeq_trans OF [n_d1, md1_d];                (* n = d *)
            (* lt d n = le (Suc d) n ; rewrite n -> d : le (Suc d) d = lt d d *)
            val reflSd= oeqreflL_at (suc dF);                      (* oeq (Suc d)(Suc d) *)
            val lt_dd = le_rewrite (suc dF, suc dF, nF, dF) reflSd n_d h_ltdn;  (* le (Suc d) d = lt d d *)
            val fls   = lt_irrefl_atL dF lt_dd;                    (* oFalse *)
          in impI_atL (oeq e (suc ZeroC), oFalseC)
               (Thm.implies_intr (ctermL (jT (oeq e (suc ZeroC)))) fls) end;  (* neg (oeq e 1) *)

        (* ---- lt 1 e ---- *)
        val h_lt1e = gt1_of_ne0_ne1_atL e e_ne0 e_ne1;            (* lt 1 e == le 2 e *)

        (* ---- lt e n ---- *)
        (* le 2 d  (== lt 1 d == h_lt1d) -> le (mult 2 e)(mult d e) *)
        val le_2e_de = mult_le_mono_r (two, dF, e) h_lt1d;        (* le (2*e)(d*e) *)
        (* 2*e = e+e ; d*e ~ n :  rewrite le (2*e)(d*e) -> le (e+e) n *)
        val m2_add   = mult2_eq_add e;                            (* (2*e) = (e+e) *)
        val n_de2    = he;                                        (* n = (d*e) *)
        val de_n     = oeq_sym OF [n_de2];                        (* (d*e) = n *)
        val le_ee_n  = le_rewrite (mult two e, add e e, mult dF e, nF) m2_add de_n le_2e_de;
                                                                  (* le (e+e) n *)
        (* lt e (e+e) : e = Suc e0 (from e != 0), witness e0 *)
        val ex_e0    = ne0_suc_atL e e_ne0;                       (* Ex(%m. oeq e (Suc m)) *)
        val Pe0      = Abs("m", natT, oeq e (suc (Bound 0)));
        val lt_e_ee  =
          let
            fun e0Body e0 (he0 : thm) =                           (* he0 : oeq e (Suc e0) *)
              let
                (* want oeq (add e e) (add (Suc e) e0) ; both = Suc(add e e0) *)
                val rhs_S = addSucL_at (e, e0);                   (* (Suc e + e0) = Suc(e + e0) *)
                (* add e e = add e (Suc e0) [cong on right via he0] = Suc(add e e0) [add_Suc_right] *)
                val congR = add_cong_rL (e, e, suc e0) he0;       (* (e + e) = (e + Suc e0) *)
                val aSr   = addSrL_at (e, e0);                    (* (e + Suc e0) = Suc(e + e0) *)
                val lhs_S = oeq_trans OF [congR, aSr];            (* (e + e) = Suc(e + e0) *)
                val rhs_Ss= oeq_sym OF [rhs_S];                   (* Suc(e + e0) = (Suc e + e0) *)
                val witEq = oeq_trans OF [lhs_S, rhs_Ss];         (* (e + e) = (Suc e + e0) *)
              in le_introL (suc e, add e e, e0) witEq end;        (* le (Suc e)(e+e) = lt e (e+e) *)
          in exE_elimL (Pe0, lt e (add e e)) ex_e0 "e0w" e0Body end;
        (* lt e n : le (Suc e)(e+e) and le (e+e) n => le (Suc e) n *)
        val h_lt_en  = le_trans_atL (suc e, add e e, nF) lt_e_ee le_ee_n;  (* le (Suc e) n = lt e n *)

        (* ---- oeq n (mult d e) ---- *)
        val h_n_de   = he;                                        (* n = (d*e) *)

        (* ---- assemble the witness conjunction ---- *)
        val conjInner = conjI_atL (lt (suc ZeroC) e, lt e nF) h_lt1e h_lt_en;
        val conjFull  = conjI_atL (mkConj (lt (suc ZeroC) e) (lt e nF), oeq nF (mult dF e))
                          conjInner h_n_de;
      in exI_atL resAbs e conjFull end;                          (* jT goalEx *)

    val afterExE = exE_elimL (PabsK, goalEx) h_dvd "ew" dvdBody;
    val d1 = Thm.implies_intr (ctermL h_dvdP)  afterExE;
    val d2 = Thm.implies_intr (ctermL h_ltdnP) d1;
    val d3 = Thm.implies_intr (ctermL h_lt1dP) d2;
  in varify d3 end;

(* validation *)
val dVco = Var (("d",0), natT);
val nVco = Var (("n",0), natT);
val cofactor_intended =
  let
    val resAbsI =
      let val eF = Free("e_co", natT)
      in Term.lambda eF (mkConj (mkConj (lt (suc ZeroC) eF) (lt eF nVco)) (oeq nVco (mult dVco eF))) end;
  in Logic.mk_implies (jT (lt (suc ZeroC) dVco),
       Logic.mk_implies (jT (lt dVco nVco),
         Logic.mk_implies (jT (dvd dVco nVco), jT (mkEx resAbsI)))) end;
val r_cofactor = checkL ("cofactor", cofactor, cofactor_intended);

(* ============================================================================
   FTA HELPERS FINAL VERDICT
   ============================================================================ *)
val () =
  if r_product_append andalso r_all_prime_append andalso r_cofactor
  then out "FTA_HELPERS_OK\n"
  else out "FTA_HELPERS_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  FTA EXISTENCE : every n >= 2 is a product of a list of primes  ***
   ----------------------------------------------------------------------------
   The result existential quantifies over `ps : natlist`, but the base `Ex` is
   monomorphic over `nat` (Ex : (nat=>o)=>o).  So we extend the theory ONE more
   time (thyM) with a natlist-level existential ExL : (natlist=>o)=>o plus its
   intro/elim axioms (exactly mirroring exI_ax / exE_ax), re-init the FINAL
   context ctxtM/ctermM, and route the list-existential pieces through it.  The
   nat-level helpers (conjI_atL / mp_atL / exI_atL / exE_elimL / disjE / ...)
   stay on ctxtL (thyM extends thyL, so ctxtL-proved thms are valid in ctxtM).

   TARGET:
     fta_existence : jT (le 2 n)
        ==> jT (ExL (%ps. Conj (all_prime ps) (oeq (product ps) n)))

   PROOF by strong_induct on n with the course-of-values predicate
     R n := Imp (le 2 n) (ExL (%ps. Conj (all_prime ps) (oeq (product ps) n))).
   ============================================================================ *)

val () = out "FTA_MAIN_BEGIN\n";

(* ---- theory extension : natlist-level existential ExL + exI_L / exE_L ---- *)
val predListT = natlistT --> oT;                       (* natlist => o *)
val thyM1 = Sign.add_consts [(Binding.name "ExL", predListT --> oT, NoSyn)] thyL;
val ExLC  = Const (Sign.full_name thyM1 (Binding.name "ExL"), predListT --> oT);
fun mkExL pr = ExLC $ pr;

val PpL = Free ("P", predListT);
val aEL = Free ("a", natlistT);
val exI_L_prop = Logic.mk_implies (jT (PpL $ aEL), jT (mkExL PpL));
val ((_,exI_L_ax), thyM2) = Thm.add_axiom_global (Binding.name "exI_L", exI_L_prop) thyM1;

val QfreeL = Free ("Q", oT);
val xEL = Free ("x", natlistT);
val exE_L_prop =
  Logic.mk_implies (jT (mkExL PpL),
    Logic.mk_implies (Logic.all xEL (Logic.mk_implies (jT (PpL $ xEL), jT QfreeL)),
      jT QfreeL));
val ((_,exE_L_ax), thyM) = Thm.add_axiom_global (Binding.name "exE_L", exE_L_prop) thyM2;

(* ---- THE FINAL final context ---- *)
val ctxtM  = Proof_Context.init_global thyM;
val ctermM = Thm.cterm_of ctxtM;

val exI_L_vM = varify exI_L_ax;
val exE_L_vM = varify exE_L_ax;

(* list-existential intro / elim on ctxtM *)
fun exI_atM Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("P",0), ctermM Pabs), (("a",0), ctermM at)] exI_L_vM)
  in Thm.implies_elim inst hbody end;
fun exE_elimM (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natlistT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermM hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermM wF) (Thm.implies_intr (ctermM hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtM
                    [(("P",0), ctermM Pabs), (("Q",0), ctermM goalC)] exE_L_vM);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* ---- lift the big theorems schematically (valid in thyM, which extends thyL) ---- *)
val strong_induct_vM = varify strong_induct;     (* H ==> jT (P k) *)
val prime_cases_vM   = varify prime_cases;       (* jT (lt 1 n) ==> jT (Disj (prime2 n)(pdEx)) *)
val cofactor_vM      = varify cofactor;          (* lt1d ==> ltdn ==> dvddn ==> jT (Ex e. ...) *)
val product_append_vM   = varify product_append;
val all_prime_append_vM = varify all_prime_append;

(* disjE on ctxtM (object Disj from prime_cases) *)
val disjE_vM = varify disjE_ax;
fun disjE_elimM (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtM
          [(("A",0), ctermM At), (("B",0), ctermM Bt), (("C",0), ctermM Ct)] disjE_vM);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;

(* nat-level connective helpers re-stated on ctxtM (route through ctermM) *)
val exI_vM = varify exI_ax;  val exE_vM = varify exE_ax;
val conjI_vM = varify conjI_ax;
val conjunct1_vM = varify conjunct1_ax; val conjunct2_vM = varify conjunct2_ax;
val mp_vM = varify mp_ax; val impI_vM = varify impI_ax;
fun conjI_atM (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("A",0), ctermM At), (("B",0), ctermM Bt)] conjI_vM)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atM (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("A",0), ctermM At), (("B",0), ctermM Bt)] conjunct1_vM)
  in Thm.implies_elim inst hC end;
fun conjunct2_atM (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("A",0), ctermM At), (("B",0), ctermM Bt)] conjunct2_vM)
  in Thm.implies_elim inst hC end;
fun mp_atM (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("A",0), ctermM At), (("B",0), ctermM Bt)] mp_vM)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_atM (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("A",0), ctermM At), (("B",0), ctermM Bt)] impI_vM)
  in Thm.implies_elim inst hImpThm end;

(* nat-existential intro / elim on ctxtM (for the cofactor / proper-divisor Ex's) *)
fun exI_atM_n Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("P",0), ctermM Pabs), (("a",0), ctermM at)] exI_vM)
  in Thm.implies_elim inst hbody end;
fun exE_elimM_n (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermM hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermM wF) (Thm.implies_intr (ctermM hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtM
                    [(("P",0), ctermM Pabs), (("Q",0), ctermM goalC)] exE_vM);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* instantiators for big theorems on ctxtM *)
fun prime_cases_atM nt hgt1 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM nt)] prime_cases_vM)
  in Thm.implies_elim inst hgt1 end;
fun cofactor_atM (dt, nt) h1 h2 h3 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("d",0), ctermM dt), (("n",0), ctermM nt)] cofactor_vM)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst h1) h2) h3 end;
fun product_append_atM (at, bt) =
  beta_norm (Drule.infer_instantiate ctxtM
    [(("a",0), ctermM at), (("b",0), ctermM bt)] product_append_vM);
fun all_prime_append_atM (at, bt) hAa hAb =
  let val inst = beta_norm (Drule.infer_instantiate ctxtM
        [(("a",0), ctermM at), (("b",0), ctermM bt)] all_prime_append_vM)
  in Thm.implies_elim (Thm.implies_elim inst hAa) hAb end;

(* nat-equality / nat-list helpers re-instantiated on ctxtM where they build cterms.
   The base FTA helpers (product_Cons_at, all_prime_*, mult_cong_*, mult1rL_at,
   product_Nil_thm) route through ctermL; their RESULT thms are valid in ctxtM
   (thyM extends thyL).  oeq_sym / oeq_trans are schematic (OF works anywhere). *)

val () = out "FTA_MAIN_HELPERS_READY\n";

(* ---- the result existential body (over natlist) ---- *)
fun resBodyAbs nt =                       (* %ps. Conj (all_prime ps) (oeq (product ps) n) *)
  let val psF = Free("ps_rb", natlistT)
  in Term.lambda psF (mkConj (all_prime psF) (oeq (product psF) nt)) end;
fun resEx nt = mkExL (resBodyAbs nt);
fun Rtm nt = mkImp (le two nt) (resEx nt);    (* Imp (le 2 n) (ExL ps. ...) *)

val Rpred_fta =                               (* %n. R n  (nat=>o) *)
  let val nF = Free("n_R", natT)
  in Term.lambda nF (Rtm nF) end;

(* ============================================================================
   The strong-induction step body : fix n, given strong IH G, prove jT (R n).
   ============================================================================ *)
val fta_existence =
  let
    val nStep = Free("n_step", natT);
    val mIH = Free("m_ih", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (Rtm mIH)));
    val Hthm  = Thm.assume (ctermM Gprop);
    fun applyIH dt h_lt =                        (* lt d n -> jT (R d) *)
      let val hAt = Thm.forall_elim (ctermM dt) Hthm
      in Thm.implies_elim hAt h_lt end;

    val le2n_P = jT (le two nStep);
    val h_le2n = Thm.assume (ctermM le2n_P);     (* le 2 n == lt 1 n *)

    val pd_Abs =
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (mkConj (lt (suc ZeroC) dF) (lt dF nStep)) (dvd dF nStep)) end;
    val pdEx = mkEx pd_Abs;
    val dThm = prime_cases_atM nStep h_le2n;     (* Disj (prime2 n) pdEx *)

    val goalC = resEx nStep;

    (* ===== CASE A : prime2 n -> witness ps := Cons n Nil ===== *)
    val caseA =
      let
        val hp = Thm.assume (ctermM (jT (prime2 nStep)));     (* prime2 n *)
        val hAPnil = all_prime_Nil_vL;                        (* jT (all_prime Nil) *)
        val conjAP = conjI_atM (prime2 nStep, all_prime NilC) hp hAPnil;
        val hAPcons= all_prime_Cons_bwd_at (nStep, NilC) conjAP;          (* all_prime (Cons n Nil) *)
        val pCons  = product_Cons_at (nStep, NilC);           (* product(Cons n Nil) = mult n (product Nil) *)
        val pNil   = product_Nil_thm;                         (* product Nil = Suc Zero *)
        val congN  = mult_cong_rL (nStep, product NilC, suc ZeroC) pNil;  (* mult n (product Nil) = mult n 1 *)
        val m1r    = mult1rL_at nStep;                        (* mult n 1 = n *)
        val e1     = oeq_trans OF [pCons, congN];
        val prodEq = oeq_trans OF [e1, m1r];                  (* product(Cons n Nil) = n *)
        val psW    = cons nStep NilC;
        val conjW  = conjI_atM (all_prime psW, oeq (product psW) nStep) hAPcons prodEq;
        val ex     = exI_atM (resBodyAbs nStep) psW conjW;    (* jT (resEx n) *)
      in Thm.implies_intr (ctermM (jT (prime2 nStep))) ex end;

    (* ===== CASE B : pdEx -> exE d, cofactor, IH x2, append ===== *)
    val caseB =
      let
        val hpd = Thm.assume (ctermM (jT pdEx));
        fun pdBody d (hConj : thm) =    (* hConj : jT (Conj (Conj (1<d)(d<n)) (d|n)) *)
          let
            val innerC = mkConj (lt (suc ZeroC) d) (lt d nStep);
            val hInner = conjunct1_atM (innerC, dvd d nStep) hConj;
            val hDvdDN = conjunct2_atM (innerC, dvd d nStep) hConj;          (* d|n *)
            val h_1ltd = conjunct1_atM (lt (suc ZeroC) d, lt d nStep) hInner;(* 1<d == le 2 d *)
            val h_ltdn = conjunct2_atM (lt (suc ZeroC) d, lt d nStep) hInner;(* d<n == lt d n *)
            val cofAbs =
              let val eF = Free("e_co", natT)
              in Term.lambda eF (mkConj (mkConj (lt (suc ZeroC) eF) (lt eF nStep)) (oeq nStep (mult d eF))) end;
            val hCof   = cofactor_atM (d, nStep) h_1ltd h_ltdn hDvdDN;       (* jT (Ex e. ...) *)
            fun cofBody e (hC2 : thm) =   (* hC2 : jT (Conj(Conj(1<e)(e<n))(oeq n (mult d e))) *)
              let
                val innerE = mkConj (lt (suc ZeroC) e) (lt e nStep);
                val hInE   = conjunct1_atM (innerE, oeq nStep (mult d e)) hC2;
                val hNde   = conjunct2_atM (innerE, oeq nStep (mult d e)) hC2;  (* oeq n (mult d e) *)
                val h_1lte = conjunct1_atM (lt (suc ZeroC) e, lt e nStep) hInE; (* 1<e == le 2 e *)
                val h_lten = conjunct2_atM (lt (suc ZeroC) e, lt e nStep) hInE; (* e<n == lt e n *)
                val Rd     = applyIH d h_ltdn;                                (* jT (Imp (le 2 d)(resEx d)) *)
                val exPd   = mp_atM (le two d, resEx d) Rd h_1ltd;           (* jT (resEx d) *)
                val Re     = applyIH e h_lten;                               (* jT (Imp (le 2 e)(resEx e)) *)
                val exPe   = mp_atM (le two e, resEx e) Re h_1lte;          (* jT (resEx e) *)
                fun pdInner pd (hpdC : thm) =
                  let
                    val hAPpd  = conjunct1_atM (all_prime pd, oeq (product pd) d) hpdC;
                    val hProdPd= conjunct2_atM (all_prime pd, oeq (product pd) d) hpdC;
                    fun peInner pe (hpeC : thm) =
                      let
                        val hAPpe  = conjunct1_atM (all_prime pe, oeq (product pe) e) hpeC;
                        val hProdPe= conjunct2_atM (all_prime pe, oeq (product pe) e) hpeC;
                        val psW    = append pd pe;
                        val hAPps  = all_prime_append_atM (pd, pe) hAPpd hAPpe;   (* all_prime (append pd pe) *)
                        val pa     = product_append_atM (pd, pe);   (* product(append pd pe) = mult (product pd)(product pe) *)
                        val congL  = mult_cong_lL (product pd, d, product pe) hProdPd;
                                                                    (* mult (product pd)(product pe) = mult d (product pe) *)
                        val congR  = mult_cong_rL (d, product pe, e) hProdPe;
                                                                    (* mult d (product pe) = mult d e *)
                        val e1     = oeq_trans OF [pa, congL];
                        val e2     = oeq_trans OF [e1, congR];       (* product(append pd pe) = mult d e *)
                        val de_n   = oeq_sym OF [hNde];             (* mult d e = n *)
                        val prodEq = oeq_trans OF [e2, de_n];       (* product(append pd pe) = n *)
                        val conjW  = conjI_atM (all_prime psW, oeq (product psW) nStep) hAPps prodEq;
                      in exI_atM (resBodyAbs nStep) psW conjW end;   (* jT (resEx n) *)
                  in exE_elimM (resBodyAbs e, goalC) exPe "pe_w" peInner end;
              in exE_elimM (resBodyAbs d, goalC) exPd "pd_w" pdInner end;
          in exE_elimM_n (cofAbs, goalC) hCof "e_w" cofBody end;
        val g = exE_elimM_n (pd_Abs, goalC) hpd "d_w" pdBody;
      in Thm.implies_intr (ctermM (jT pdEx)) g end;

    val concl = disjE_elimM (prime2 nStep, pdEx, goalC) dThm caseA caseB;  (* jT (resEx n) *)
    val impRn = impI_atM (le two nStep, resEx nStep)
                  (Thm.implies_intr (ctermM le2n_P) concl);                (* jT (R n) *)
    val stepThm = Thm.forall_intr (ctermM nStep) (Thm.implies_intr (ctermM Gprop) impRn);

    val kF = Free("n", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtM
                   [(("P",0), ctermM Rpred_fta), (("k",0), ctermM kF)] strong_induct_vM);
    val Rk    = Thm.implies_elim siInst stepThm;          (* jT (R k) *)
    val h_le2k= Thm.assume (ctermM (jT (le two kF)));
    val exK   = mp_atM (le two kF, resEx kF) Rk h_le2k;   (* jT (resEx k) *)
    val disch = Thm.implies_intr (ctermM (jT (le two kF))) exK;
  in varify disch end;

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal.
   ============================================================================ *)
fun checkM (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtM (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtM intended ^ "\n");
          false)
  end;

val nVfta = Var (("n",0), natT);
val fta_existence_intended =
  let
    val bodyAbsI =
      let val psF = Free("ps_rb", natlistT)
      in Term.lambda psF (mkConj (all_prime psF) (oeq (product psF) nVfta)) end;
  in Logic.mk_implies (jT (le two nVfta), jT (mkExL bodyAbsI)) end;

val r_fta = checkM ("fta_existence", fta_existence, fta_existence_intended);

(* ---- SOUNDNESS PROBES : kernel must REJECT false variants ---- *)
val probe_fta_allprime =
  let
    val bogusAbs =
      let val psF = Free("ps_rb", natlistT)
      in Term.lambda psF (oeq (product psF) nVfta) end;          (* drops all_prime *)
    val bogus = Logic.mk_implies (jT (le two nVfta), jT (mkExL bogusAbs));
  in not ((Thm.prop_of fta_existence) aconv bogus) end;
val probe_fta_product =
  let
    val bogusAbs =
      let val psF = Free("ps_rb", natlistT)
      in Term.lambda psF (all_prime psF) end;                    (* drops product = n *)
    val bogus = Logic.mk_implies (jT (le two nVfta), jT (mkExL bogusAbs));
  in not ((Thm.prop_of fta_existence) aconv bogus) end;
val probe_fta_hyp =
  let
    val bodyAbsI =
      let val psF = Free("ps_rb", natlistT)
      in Term.lambda psF (mkConj (all_prime psF) (oeq (product psF) nVfta)) end;
    val bogus = jT (mkExL bodyAbsI);                              (* drops le 2 n premise *)
  in not ((Thm.prop_of fta_existence) aconv bogus) end;

val () =
  if probe_fta_allprime andalso probe_fta_product andalso probe_fta_hyp
  then out "PROBE_OK fta_existence keeps all_prime, product=n, and 2<=n\n"
  else out "PROBE_UNSOUND fta_existence dropped a conjunct or the hypothesis!\n";

val () =
  if r_fta then out "OK fta_existence\n" else out "FAILED fta_existence\n";

val () =
  if r_fta andalso probe_fta_allprime andalso probe_fta_product andalso probe_fta_hyp
  then out "FTA_DONE\n"
  else out "FTA_FAILED\n";
