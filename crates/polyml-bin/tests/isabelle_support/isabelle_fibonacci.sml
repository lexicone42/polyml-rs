(* ======================================================================
   CLASSICAL FIBONACCI IDENTITIES in Isabelle/Pure, on with_nt_helpers.

   Standard Fibonacci (conservative recursion): fib 0 = 0, fib 1 = 1,
   fib (n+2) = fib (n+1) + fib n  (0,1,1,2,3,5,8,…; distinct from the
   Zeckendorf zfib 1,2,3,5,8). Each result 0-hyp, aconv-intended,
   soundness-probed; only classical assumption = ex_middle.

   SUM (FIB_SUM_OK):  ⊢ fibsum n + 1 = fib (n+2)
       (the subtraction-free telescoping form of ∑_{i=0}^n fib i = fib(n+2)−1).
   ADDITION LAW (FIB_ADD_OK):  ⊢ fib (m+n+1) = fib(m+1)·fib(n+1) + fib(m)·fib(n)
       (sign-free; induction on m with the two-consecutive-cases predicate).
   CASSINI (FIB_CASSINI_OK), the ℕ parity form (the +1 on OPPOSITE sides =
   (−1)ⁿ rendered sign-free; ONE simultaneous induction on k, dbl k = 2k):
       cassini_a:  fib(2k)·fib(2k+2) + 1 = fib(2k+1)²
       cassini_b:  fib(2k+1)·fib(2k+3) = fib(2k+2)² + 1

   = fib_base.sml (fib + fibsum + SUM) + fib_addition_delta + fib_cassini_delta,
   spliced via common::with_nt_helpers. ultracode wf_c7994e02-6d9.
   ====================================================================== *)

(* ============================================================================
   FIBONACCI BASE + the FIBONACCI SUM identity, in Isabelle/Pure on the
   polyml-rs interpreter.  Spliced AFTER common::with_nt_helpers (object logic +
   Peano add/mult + commutative semiring + order + strong induction + classical
   FOL).  Final foundation context = ctxtS2 / ctermS2 on theory thyS2.

   STANDARD Fibonacci (0,1,1,2,3,5,8,...), DISTINCT from the Zeckendorf zfib:
     fib 0 = 0,  fib 1 = 1,  fib (Suc (Suc n)) = fib (Suc n) + fib n.
   (conservative recursion axioms fib_0 / fib_1 / fib_SS)

   fibsum n = sum_{i=0..n} fib i, by recursion:
     fibsum 0 = 0,  fibsum (Suc n) = fibsum n + fib (Suc n).

   THE SUM IDENTITY (subtraction-free telescoping form):
     fibsum n + 1 = fib (Suc (Suc n)).
   Base n=0 : 0 + 1 = fib 2 = 1.
   Step     : fibsum(Suc n) + 1 = (fibsum n + fib(Suc n)) + 1
                                 = (fibsum n + 1) + fib(Suc n)     [comm/assoc]
                                 = fib(Suc(Suc n)) + fib(Suc n)    [IH]
                                 = fib(Suc(Suc(Suc n))).           [fib_SS sym]

   Adding fib / fibsum EXTENDS the theory, so we build ONE final context
   ctxtF / ctermF and re-varify reused base lemmas onto it (the standard
   new-const discipline).
   ============================================================================ *)

val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

(* ---- FRESH consts fib, fibsum : nat -> nat, on top of thyS2 ---- *)
val thyF0 = Sign.add_consts
  [(Binding.name "fib",    natT --> natT, NoSyn),
   (Binding.name "fibsum", natT --> natT, NoSyn)] thyS2;
val fibC    = Const (Sign.full_name thyF0 (Binding.name "fib"),    natT --> natT);
fun fib t   = fibC $ t;
val fibsumC = Const (Sign.full_name thyF0 (Binding.name "fibsum"), natT --> natT);
fun fibsum t= fibsumC $ t;

val one  = suc ZeroC;
val nF0  = Free ("nF", natT);
val kF0  = Free ("kF", natT);

(* ---- conservative recursion axioms ---- *)
val ((_,fib_0),  tF1) = Thm.add_axiom_global (Binding.name "fib_0",
      jT (oeq (fib ZeroC) ZeroC)) thyF0;
val ((_,fib_1),  tF2) = Thm.add_axiom_global (Binding.name "fib_1",
      jT (oeq (fib one) one)) tF1;
val ((_,fib_SS), tF3) = Thm.add_axiom_global (Binding.name "fib_SS",
      jT (oeq (fib (suc (suc kF0))) (add (fib (suc kF0)) (fib kF0)))) tF2;
val ((_,fibsum_0),  tF4) = Thm.add_axiom_global (Binding.name "fibsum_0",
      jT (oeq (fibsum ZeroC) ZeroC)) tF3;
val ((_,fibsum_Suc),thyF) = Thm.add_axiom_global (Binding.name "fibsum_Suc",
      jT (oeq (fibsum (suc nF0)) (add (fibsum nF0) (fib (suc nF0))))) tF4;

(* ---- THE ONE FINAL CONTEXT ctxtF / ctermF ---- *)
val ctxtF  = Proof_Context.init_global thyF;
val ctermF = Thm.cterm_of ctxtF;

(* ---- re-varify reused foundation axioms/lemmas onto ctxtF ---- *)
val fib_0_v       = varify fib_0;
val fib_1_v       = varify fib_1;
val fib_SS_v      = varify fib_SS;
val fibsum_0_v    = varify fibsum_0;
val fibsum_Suc_v  = varify fibsum_Suc;

val oeq_refl_vF   = varify oeq_refl;
val oeq_sym_vF    = varify oeq_sym;          (* schematic; varify just re-zeroes *)
val oeq_trans_vF  = varify oeq_trans;
val Suc_cong_vF   = varify Suc_cong;
val add_0_vF      = varify add_0;
val add_Suc_vF    = varify add_Suc;
val add_0_right_vF= varify add_0_right;
val add_Suc_right_vF = varify add_Suc_right;
val add_comm_vF   = varify add_comm;
val add_assoc_vF  = varify add_assoc;
val nat_induct_vF = varify nat_induct;

(* ---- ground instantiators on ctxtF ---- *)
fun oeqreflF_at t  = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF t)] oeq_refl_vF);
fun add0F_at t     = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] add_0_vF);
fun addSucF_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF
                          [(("m",0), ctermF mt),(("n",0), ctermF nt)] add_Suc_vF);
fun add0rF_at t    = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] add_0_right_vF);
fun addSrF_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF
                          [(("m",0), ctermF mt),(("n",0), ctermF nt)] add_Suc_right_vF);
fun addcommF_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF
                          [(("m",0), ctermF mt),(("n",0), ctermF nt)] add_comm_vF);
fun addassocF_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtF
                          [(("m",0), ctermF mt),(("n",0), ctermF nt),(("k",0), ctermF kt)] add_assoc_vF);
fun fib0_at ()     = fib_0_v;
fun fib1_at ()     = fib_1_v;
fun fibSS_at t     = beta_norm (Drule.infer_instantiate ctxtF [(("kF",0), ctermF t)] fib_SS_v);
fun fibsum0_at ()  = fibsum_0_v;
fun fibsumSuc_at t = beta_norm (Drule.infer_instantiate ctxtF [(("nF",0), ctermF t)] fibsum_Suc_v);

(* add congruence on the LEFT operand, on ctxtF *)
val oeq_subst_vF = varify oeq_subst;
fun add_cong_lF (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (add pT kT))] oeq_refl_vF);
  in inst OF [hpq, refl_pk] end;

(* small validator on ctxtF (aconv is context-free) *)
fun checkF (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtF (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtF intended ^ "\n");
          false)
  end;

(* ============================================================================
   HELPER : the recurrence as a usable rewrite is just fibSS_at.
   fib 2 = 1  (fib_two), a small sanity lemma used by the base case.
     fib 2 = fib(Suc(Suc 0)) = fib 1 + fib 0 = 1 + 0 = 1.
   ============================================================================ *)
val fib_two =                                            (* oeq (fib (suc (suc Zero))) one *)
  let
    val ss0  = fibSS_at ZeroC;                           (* oeq (fib 2) (add (fib 1)(fib 0)) *)
    val f1   = fib1_at ();                               (* oeq (fib 1) 1 *)
    val f0   = fib0_at ();                               (* oeq (fib 0) 0 *)
    (* add (fib 1)(fib 0) -> add 1 (fib 0) [cong left by f1] -> add 1 0 [cong right]
       -> 1 [add0r]. Easiest: add (fib 1)(fib 0) ~ add 1 0 ~ 1. *)
    val congL = add_cong_lF (fib one, one, fib ZeroC) f1; (* oeq (add (fib1)(fib0)) (add 1 (fib0)) *)
    (* add 1 (fib 0) ~ add 1 0 via right cong : use oeq_subst with Pabs = %z. oeq (add 1 (fib0)) (add 1 z) *)
    val congR =
      let
        val Pabs = Abs("z", natT, oeq (add one (fib ZeroC)) (add one (Bound 0)));
        val inst = beta_norm (Drule.infer_instantiate ctxtF
              [(("P",0), ctermF Pabs),(("a",0), ctermF (fib ZeroC)),(("b",0), ctermF ZeroC)] oeq_subst_vF);
        val refl = beta_norm (Drule.infer_instantiate ctxtF
              [(("a",0), ctermF (add one (fib ZeroC)))] oeq_refl_vF);
      in inst OF [f0, refl] end;                          (* oeq (add 1 (fib0)) (add 1 0) *)
    val add1_0 = add0rF_at one;                           (* oeq (add 1 0) 1 *)
    val chain1 = oeq_trans OF [ss0, congL];               (* oeq (fib2) (add 1 (fib0)) *)
    val chain2 = oeq_trans OF [chain1, congR];            (* oeq (fib2) (add 1 0) *)
    val chain3 = oeq_trans OF [chain2, add1_0];           (* oeq (fib2) 1 *)
  in varify chain3 end;

val fib_two_intended = jT (oeq (fib (suc (suc ZeroC))) one);
val r_fib_two = checkF ("fib_two", fib_two, fib_two_intended);

(* ============================================================================
   THE SUM IDENTITY :  oeq (add (fibsum n) 1) (fib (Suc (Suc n)))   (for all n)
   by induction on n.
   ============================================================================ *)
val fib_sum =
  let
    val Qpred = Abs("z", natT, oeq (add (fibsum (Bound 0)) one) (fib (suc (suc (Bound 0)))));
    val nVar  = Free ("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Qpred), (("k",0), ctermF nVar)] nat_induct_vF);

    (* ---- BASE n = 0 :  oeq (add (fibsum 0) 1) (fib 2) ---- *)
    val base =
      let
        val fs0  = fibsum0_at ();                          (* oeq (fibsum 0) 0 *)
        (* add (fibsum 0) 1 ~ add 0 1 [cong left] ~ 1 [add0] ; and fib2 ~ 1 ; combine sym *)
        val congL = add_cong_lF (fibsum ZeroC, ZeroC, one) fs0; (* oeq (add (fibsum0) 1) (add 0 1) *)
        val add01 = add0F_at one;                          (* oeq (add 0 1) 1 *)
        val lhs1  = oeq_trans OF [congL, add01];           (* oeq (add (fibsum0) 1) 1 *)
        val f2_1  = fib_two;                               (* oeq (fib2) 1 *)
        val one_f2= oeq_sym OF [f2_1];                     (* oeq 1 (fib2) *)
      in oeq_trans OF [lhs1, one_f2] end;                  (* oeq (add (fibsum0) 1) (fib2) *)

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add (fibsum xF) one) (fib (suc (suc xF))));
    val IH = Thm.assume (ctermF ihprop);
    val step =
      let
        (* LHS = add (fibsum (Suc x)) 1 .
           fibsum_Suc : oeq (fibsum (Suc x)) (add (fibsum x)(fib(Suc x))) *)
        val fsS = fibsumSuc_at xF;                         (* oeq (fibsum(Sx)) (add (fibsum x)(fib(Sx))) *)
        (* cong left into +1 : oeq (add (fibsum(Sx)) 1) (add (add (fibsum x)(fib(Sx))) 1) *)
        val e1  = add_cong_lF (fibsum (suc xF), add (fibsum xF) (fib (suc xF)), one) fsS;
        (* reassociate : add (add (fibsum x)(fib(Sx))) 1 ~ add (fibsum x) (add (fib(Sx)) 1)  [add_assoc] *)
        val asc = addassocF_at (fibsum xF, fib (suc xF), one);
        (* swap inner : add (fib(Sx)) 1 ~ add 1 (fib(Sx))  [add_comm] -> we instead want
           (fibsum x + 1) + fib(Sx). Route: add (fibsum x)(add (fib(Sx)) 1)
             ~ add (fibsum x)(add 1 (fib(Sx)))      [cong right, add_comm]
             ~ add (add (fibsum x) 1) (fib(Sx))     [add_assoc sym] *)
        val comm_inner = addcommF_at (fib (suc xF), one);  (* oeq (add (fib(Sx)) 1) (add 1 (fib(Sx))) *)
        (* cong right under (fibsum x + _) *)
        val congR =
          let
            val Pabs = Abs("z", natT, oeq (add (fibsum xF) (add (fib (suc xF)) one))
                                          (add (fibsum xF) (Bound 0)));
            val inst = beta_norm (Drule.infer_instantiate ctxtF
                  [(("P",0), ctermF Pabs),
                   (("a",0), ctermF (add (fib (suc xF)) one)),
                   (("b",0), ctermF (add one (fib (suc xF))))] oeq_subst_vF);
            val refl = beta_norm (Drule.infer_instantiate ctxtF
                  [(("a",0), ctermF (add (fibsum xF) (add (fib (suc xF)) one)))] oeq_refl_vF);
          in inst OF [comm_inner, refl] end;
        (* now add (fibsum x)(add 1 (fib(Sx))) ~ add (add (fibsum x) 1) (fib(Sx)) [add_assoc sym] *)
        val asc2sym = oeq_sym OF [addassocF_at (fibsum xF, one, fib (suc xF))];
        (* assemble LHS chain so far:
             e1   : (fibsum(Sx)+1) ~ (fibsum x + fib(Sx)) + 1
             asc  : (fibsum x + fib(Sx)) + 1 ~ fibsum x + (fib(Sx)+1)
             congR: fibsum x + (fib(Sx)+1) ~ fibsum x + (1+fib(Sx))
             asc2sym: fibsum x + (1+fib(Sx)) ~ (fibsum x + 1) + fib(Sx) *)
        val l1 = oeq_trans OF [e1, asc];
        val l2 = oeq_trans OF [l1, congR];
        val l3 = oeq_trans OF [l2, asc2sym];               (* ~ (fibsum x + 1) + fib(Sx) *)
        (* IH : (fibsum x + 1) ~ fib(Suc(Suc x)) ; cong left into _ + fib(Sx) *)
        val ihCong = add_cong_lF (add (fibsum xF) one, fib (suc (suc xF)), fib (suc xF)) IH;
                                                           (* ~ fib(SSx) + fib(Sx) *)
        val l4 = oeq_trans OF [l3, ihCong];                (* (fibsum(Sx)+1) ~ fib(SSx)+fib(Sx) *)
        (* fib_SS at (Suc x) : fib(S S (Sx)) = fib(S(Sx)) + fib(Sx) ; we need
           fib(SSx) + fib(Sx) ~ fib(SSS x).  fibSS_at (suc x) :
             oeq (fib (suc(suc (suc x)))) (add (fib (suc (suc x))) (fib (suc x))) *)
        (* fib_SS at k := (suc x): suc(suc k) = suc(suc(suc x)) *)
        val fssSx = fibSS_at (suc xF);   (* oeq (fib(SSSx)) (add (fib(SSx)) (fib(Sx))) *)
        val fssSx_sym = oeq_sym OF [fssSx];                (* (add (fib(SSx))(fib(Sx))) ~ fib(SSSx) *)
        val concl = oeq_trans OF [l4, fssSx_sym];          (* (fibsum(Sx)+1) ~ fib(SSSx) *)
      in concl end;
    val step1 = Thm.forall_intr (ctermF xF) (Thm.implies_intr (ctermF ihprop) step);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val nVcap = Var (("n",0), natT);
val fib_sum_intended = jT (oeq (add (fibsum nVcap) one) (fib (suc (suc nVcap))));
val r_fib_sum = checkF ("fib_sum", fib_sum, fib_sum_intended);

(* ---- SOUNDNESS PROBE : the kernel must REJECT the off-by-one variant
        (dropping the +1, i.e. fibsum n = fib(Suc(Suc n)) is FALSE). ---- *)
val probe_offby1 =
  let val bogus = jT (oeq (fibsum nVcap) (fib (suc (suc nVcap))))
  in not ((Thm.prop_of fib_sum) aconv bogus) end;
val () = if probe_offby1
         then out "PROBE_OK fib_sum keeps the +1\n"
         else out "PROBE_UNSOUND fib_sum dropped the +1!\n";

val () =
  if r_fib_two andalso r_fib_sum andalso probe_offby1
  then out "FIB_SUM_OK\n"
  else out "FIB_SUM_FAILED\n";

(* ============================================================================
   THE FIBONACCI ADDITION LAW (sign-free), in Isabelle/Pure on polyml-rs.

     fib_add :  |- fib (Suc (add m n))
                 = add (mult (fib (Suc m)) (fib (Suc n)))
                       (mult (fib m) (fib n))      (schematic in m, n; 0-hyp)

   Spliced AFTER  isabelle_nt_helpers.sml  +  /tmp/fib_base.sml  (the fib/fibsum
   foundation on the FINAL context ctxtF / ctermF, theory thyF).

   `mult` lives in the foundation (thyM, visible in thyF); we re-varify the mult
   lemmas onto ctxtF.  Proof = nat_induct on m, with predicate
       P m  ==  Conj (Q m) (Q (Suc m))
   (the "two consecutive cases" trick) so the step has the identity at BOTH the
   previous values, which the fib recurrence (fib(SS t)=fib(St)+fib t) needs.
   n is carried as a Free and forall_intr'd at the end.
   ============================================================================ *)

(* ---- mult const re-bound (already `mult`/`multC` from the foundation) ---- *)
(* mult lemmas re-varified onto ctxtF (varify re-zeroes indices for ctxtF use) *)
val mult_0_vF        = varify mult_0;
val mult_Suc_vF      = varify mult_Suc;
val mult_0_right_vF  = varify mult_0_right;
val mult_Suc_right_vF= varify mult_Suc_right;
val mult_comm_vF     = varify mult_comm;
val mult_assoc_vF    = varify mult_assoc;
val mult_1_right_vF  = varify mult_1_right;
val left_distrib_vF  = varify left_distrib;
val right_distrib_vF = varify right_distrib;

(* classical-FOL conjunction axioms, varified onto ctxtF *)
val conjI_vF     = varify conjI_ax;
val conjunct1_vF = varify conjunct1_ax;
val conjunct2_vF = varify conjunct2_ax;

(* ---- ground instantiators on ctxtF ---- *)
fun mult0F_at t          = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_0_vF);
fun multSucF_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtF
                              [(("m",0), ctermF mt),(("n",0), ctermF nt)] mult_Suc_vF);
fun mult0rF_at t         = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_0_right_vF);
fun mult1rF_at t         = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_1_right_vF);
fun multcommF_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF
                              [(("m",0), ctermF mt),(("n",0), ctermF nt)] mult_comm_vF);
(* right_distrib : oeq (mult (add m n) k) (add (mult m k) (mult n k)) *)
fun rdistF_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtF
                              [(("m",0), ctermF mt),(("n",0), ctermF nt),(("k",0), ctermF kt)] right_distrib_vF);

(* conjI / conjunct1 / conjunct2 used directly via OF (schematic A,B) *)

(* ---- congruence helpers on ctxtF (all from oeq_subst_vF, already in base) ---- *)
(* add cong on RIGHT operand:  oeq p q  ==>  oeq (add k p) (add k q) *)
fun add_cong_rF (kT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add kT pT) (add kT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_kp = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (add kT pT))] oeq_refl_vF);
  in inst OF [hpq, refl_kp] end;

(* mult cong on LEFT operand:  oeq p q  ==>  oeq (mult p k) (mult q k) *)
fun mult_cong_lF (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (mult pT kT))] oeq_refl_vF);
  in inst OF [hpq, refl_pk] end;

(* mult cong on RIGHT operand:  oeq p q  ==>  oeq (mult k p) (mult k q) *)
fun mult_cong_rF (kT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult kT pT) (mult kT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_kp = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (mult kT pT))] oeq_refl_vF);
  in inst OF [hpq, refl_kp] end;

(* fib cong:  oeq a b  ==>  oeq (fib a) (fib b) *)
fun fib_cong (aT, bT) hab =
  let
    val Pabs = Abs("z", natT, oeq (fib aT) (fib (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF aT), (("b",0), ctermF bT)] oeq_subst_vF);
    val refl_fa = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (fib aT))] oeq_refl_vF);
  in inst OF [hab, refl_fa] end;

(* convenience oeq_refl on ctxtF *)
fun reflF t = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF t)] oeq_refl_vF);
(* chain a list of oeq steps via oeq_trans *)
fun chain [] = raise Fail "chain []"
  | chain [t] = t
  | chain (t::ts) = oeq_trans OF [t, chain ts];

(* ---- mult_1_left : oeq (mult (Suc Zero) x) x  (mult_comm + mult_1_right) ---- *)
fun mult1l_at t =
  let
    val c  = multcommF_at (one, t);        (* oeq (mult 1 t) (mult t 1) *)
    val m1 = mult1rF_at t;                  (* oeq (mult t 1) t *)
  in oeq_trans OF [c, m1] end;

(* ============================================================================
   Build the addition law.  Fix n as a Free.
   Q t = oeq (fib (Suc (add t n)))
             (add (mult (fib (Suc t)) (fib (Suc n))) (mult (fib t) (fib n)))
   ============================================================================ *)
val nFree = Free ("n", natT);

fun Qrhs t = add (mult (fib (suc t)) (fib (suc nFree))) (mult (fib t) (fib nFree));
fun Qlhs t = fib (suc (add t nFree));
fun Qprop t = oeq (Qlhs t) (Qrhs t);

(* predicate P : nat -> o ,  P z = Conj (Q z) (Q (Suc z)) *)
val Ppred = Abs ("z", natT, mkConj (Qprop (Bound 0)) (Qprop (suc (Bound 0))));

(* ---------------------------------------------------------------------------
   Q 0 :  fib(Suc(add 0 n)) = mult (fib 1) (fib(Suc n)) + mult (fib 0) (fib n)
   LHS ~ fib(Suc n) ;  RHS ~ fib(Suc n).
   --------------------------------------------------------------------------- *)
val Q0 =
  let
    (* LHS:  fib(Suc(add 0 n)) ~ fib(Suc n) *)
    val a0      = add0F_at nFree;                              (* add 0 n ~ n *)
    val sc      = Suc_cong OF [a0];                            (* Suc(add 0 n) ~ Suc n *)
    val lhsEq   = fib_cong (suc (add ZeroC nFree), suc nFree) sc; (* fib.. ~ fib(Suc n) *)
    (* RHS:  add (mult (fib1)(fib(Sn))) (mult (fib0)(fib n)) ~ fib(Suc n) *)
    val f1      = fib1_at ();                                  (* fib 1 ~ 1 *)
    val t1a     = mult_cong_lF (fib one, one, fib (suc nFree)) f1; (* mult(fib1)(..)~mult 1 (..) *)
    val t1b     = mult1l_at (fib (suc nFree));                 (* mult 1 (fib(Sn)) ~ fib(Sn) *)
    val term1   = oeq_trans OF [t1a, t1b];                     (* mult(fib1)(fib Sn) ~ fib(Sn) *)
    val f0      = fib0_at ();                                  (* fib 0 ~ 0 *)
    val t2a     = mult_cong_lF (fib ZeroC, ZeroC, fib nFree) f0; (* mult(fib0)(..)~mult 0 (..) *)
    val t2b     = mult0F_at (fib nFree);                        (* mult 0 (fib n) ~ 0 *)
    val term2   = oeq_trans OF [t2a, t2b];                     (* mult(fib0)(fib n) ~ 0 *)
    (* add term1 term2 : congruence both sides to (add (fib Sn) 0) ~ fib Sn *)
    val rL      = add_cong_lF (mult (fib one) (fib (suc nFree)), fib (suc nFree),
                               mult (fib ZeroC) (fib nFree)) term1;
                  (* RHS ~ add (fib Sn) (mult(fib0)(fib n)) *)
    val rR      = add_cong_rF (fib (suc nFree), mult (fib ZeroC) (fib nFree), ZeroC) term2;
                  (* ~ add (fib Sn) 0 *)
    val r0      = add0rF_at (fib (suc nFree));                 (* add (fib Sn) 0 ~ fib Sn *)
    val rhsEq   = chain [rL, rR, r0];                          (* RHS ~ fib(Sn) *)
    (* Q0 : LHS ~ RHS  =  LHS ~ fib(Sn) ~ RHS  (rhsEq reversed) *)
  in oeq_trans OF [lhsEq, oeq_sym OF [rhsEq]] end;

(* ---------------------------------------------------------------------------
   Q 1 :  fib(Suc(add 1 n)) = mult (fib 2)(fib(Sn)) + mult (fib 1)(fib n)
   LHS ~ fib(Suc(Suc n)) ~ add (fib Sn)(fib n) ~ RHS.
   --------------------------------------------------------------------------- *)
val Q1 =
  let
    (* LHS: add 1 n = add (Suc 0) n ~ Suc(add 0 n) ~ Suc n ;
            Suc(add 1 n) ~ Suc(Suc n) ; fib.. ~ fib(SSn) *)
    val aS      = addSucF_at (ZeroC, nFree);                   (* add (Suc 0) n ~ Suc(add 0 n) *)
    val a0      = add0F_at nFree;                              (* add 0 n ~ n *)
    val a0s     = Suc_cong OF [a0];                            (* Suc(add 0 n) ~ Suc n *)
    val add1n   = oeq_trans OF [aS, a0s];                      (* add 1 n ~ Suc n *)
    val sc      = Suc_cong OF [add1n];                         (* Suc(add 1 n) ~ Suc(Suc n) *)
    val lhsEq   = fib_cong (suc (add one nFree), suc (suc nFree)) sc; (* fib.. ~ fib(SSn) *)
    (* fib(SSn) ~ add (fib Sn)(fib n)  via fib_SS at n *)
    val fSS     = fibSS_at nFree;                              (* fib(SSn) ~ add (fib Sn)(fib n) *)
    (* RHS: mult (fib2)(fib Sn) ~ fib Sn ;  mult (fib1)(fib n) ~ fib n *)
    val f2      = fib_two;                                     (* fib 2 ~ 1 *)
    val t1a     = mult_cong_lF (fib (suc (suc ZeroC)), one, fib (suc nFree)) f2;
    val t1b     = mult1l_at (fib (suc nFree));
    val term1   = oeq_trans OF [t1a, t1b];                     (* mult(fib2)(fib Sn) ~ fib Sn *)
    val f1      = fib1_at ();                                  (* fib 1 ~ 1 *)
    val t2a     = mult_cong_lF (fib one, one, fib nFree) f1;
    val t2b     = mult1l_at (fib nFree);
    val term2   = oeq_trans OF [t2a, t2b];                     (* mult(fib1)(fib n) ~ fib n *)
    val rL      = add_cong_lF (mult (fib (suc (suc ZeroC))) (fib (suc nFree)), fib (suc nFree),
                               mult (fib one) (fib nFree)) term1;
    val rR      = add_cong_rF (fib (suc nFree), mult (fib one) (fib nFree), fib nFree) term2;
    val rhsEq   = oeq_trans OF [rL, rR];                       (* RHS ~ add (fib Sn)(fib n) *)
    (* assemble: LHS ~ fib(SSn) ~ add (fib Sn)(fib n) ~ RHS(rev) *)
  in chain [lhsEq, fSS, oeq_sym OF [rhsEq]] end;

(* BASE : jT (P 0) = jT (Conj (Q 0) (Q 1))
   Q0, Q1 already have prop  Trueprop (oeq ...) , so conjI applies directly. *)
val baseConj = conjI_vF OF [Q0, Q1];   (* jT (Conj (Q 0) (Q 1)) *)

(* ---------------------------------------------------------------------------
   STEP :  !!x. jT (P x) ==> jT (P (Suc x))
   IH = jT (Conj (Q x) (Q (Suc x))).
   Want jT (Conj (Q (Suc x)) (Q (Suc (Suc x)))).
   - first conjunct = conjunct2 IH = Q(Suc x).
   - second conjunct Q(Suc(Suc x)) from Qx and Q(Suc x) via the recurrence.
   --------------------------------------------------------------------------- *)
val xF = Free ("x", natT);
val ihprop = jT (mkConj (Qprop xF) (Qprop (suc xF)));
val IH = Thm.assume (ctermF ihprop);
val Qx   = conjunct1_vF OF [IH];     (* jT (Q x)      *)
val QSx  = conjunct2_vF OF [IH];     (* jT (Q (Suc x))*)

(* abbreviations for the fib values appearing in the algebra *)
val fSn  = fib (suc nFree);          (* fib (Suc n) *)
val fn0  = fib nFree;                (* fib n *)
val fx   = fib xF;                   (* fib x *)
val fSx  = fib (suc xF);             (* fib (Suc x) *)
val fSSx = fib (suc (suc xF));       (* fib (Suc (Suc x)) *)
val fSSSx= fib (suc (suc (suc xF))); (* fib (Suc (Suc (Suc x))) *)

val QSSx =
  let
    (* ===== LHS : fib(Suc(add (Suc(Suc x)) n)) ~ fib(SSS(add x n))
       add (Suc(Suc x)) n ~ Suc(add (Suc x) n) ~ Suc(Suc(add x n))      [add_Suc x2]
       so Suc(add (SSx) n) ~ Suc(Suc(Suc(add x n)))                      [Suc_cong]  ===== *)
    val axn  = add xF nFree;                      (* add x n *)
    val aS1   = addSucF_at (suc xF, nFree);        (* add (SSx) n ~ Suc(add (Sx) n) *)
    val aS2   = addSucF_at (xF, nFree);            (* add (Sx) n ~ Suc(add x n) *)
    val aS2c  = Suc_cong OF [aS2];                 (* Suc(add (Sx) n) ~ Suc(Suc(add x n)) *)
    val addSSxn = oeq_trans OF [aS1, aS2c];        (* add (SSx) n ~ Suc(Suc(add x n)) *)
    val scLHS = Suc_cong OF [addSSxn];             (* Suc(add (SSx) n) ~ Suc(Suc(Suc(add x n))) *)
    val lhsEq = fib_cong (suc (add (suc (suc xF)) nFree), suc (suc (suc axn))) scLHS;
                (* fib(Suc(add (SSx) n)) ~ fib(SSS(add x n)) *)

    (* fib(SSS(add x n)) ~ fib(SS(add x n)) + fib(S(add x n))    [fib_SS at (Suc(add x n))] *)
    val fibSSS = fibSS_at (suc axn);
                (* oeq (fib(SSS(add x n))) (add (fib(SS(add x n))) (fib(S(add x n)))) *)

    (* fib(SS(add x n)) = Qlhs(Suc x) ; rewrite by Q(Suc x) to its Qrhs *)
    (* Qlhs (Suc x) = fib(Suc(add (Suc x) n)).  add (Sx) n ~ Suc(add x n) [aS2], so
       fib(Suc(add (Sx) n)) ~ fib(Suc(Suc(add x n))) = fib(SS(add x n)). We need the
       OTHER direction: rewrite fib(SS(add x n)) -> Qrhs(Suc x). Build:
         fib(SS(add x n)) ~ fib(Suc(add (Sx) n))   [fib_cong (Suc(aS2)) sym]
                          ~ Qrhs(Suc x)            [Q(Suc x)] *)
    val aS2s  = oeq_sym OF [Suc_cong OF [aS2]];     (* Suc(Suc(add x n)) ~ Suc(add (Sx) n) *)
    val bridgeSx = fib_cong (suc (suc axn), suc (add (suc xF) nFree)) aS2s;
                (* fib(SS(add x n)) ~ fib(Suc(add (Sx) n)) = Qlhs(Suc x) *)
    val QSx_eq = oeq_trans OF [bridgeSx, QSx];      (* fib(SS(add x n)) ~ Qrhs(Suc x) *)

    (* fib(S(add x n)) = Qlhs x ; rewrite by Q x. Qlhs x = fib(Suc(add x n)) directly. *)
    val Qx_eq = Qx;                                 (* fib(Suc(add x n)) ~ Qrhs x *)

    (* So fib(SSS(add x n)) ~ add (Qrhs(Suc x)) (Qrhs x) :
         fibSSS : ~ add (fib(SS(add x n))) (fib(S(add x n)))
         cong-left  by QSx_eq , cong-right by Qx_eq                                  *)
    val cL = add_cong_lF (fib (suc (suc axn)), Qrhs (suc xF), fib (suc axn)) QSx_eq;
             (* add (fib SS..) (fib S..) ~ add (Qrhs Sx) (fib S..) *)
    val cR = add_cong_rF (Qrhs (suc xF), fib (suc axn), Qrhs xF) Qx_eq;
             (* ~ add (Qrhs Sx) (Qrhs x) *)
    val lhsToSum = chain [lhsEq, fibSSS, cL, cR];
        (* LHS = fib(Suc(add (SSx) n)) ~ add (Qrhs(Suc x)) (Qrhs x) *)

    (* Now name the four product terms:
         Qrhs(Suc x) = add (mult fSSx fSn) (mult fSx fn)
         Qrhs(x)     = add (mult fSx  fSn) (mult fx  fn)
       So  SUM = add (add (mult fSSx fSn) (mult fSx fn))
                     (add (mult fSx  fSn) (mult fx  fn))                            *)
    val p1 = mult fSSx fSn;   (* fib(SSx)*fib(Sn) *)
    val p2 = mult fSx  fn0;   (* fib(Sx) *fib(n)  *)
    val p3 = mult fSx  fSn;   (* fib(Sx) *fib(Sn) *)
    val p4 = mult fx   fn0;   (* fib(x)  *fib(n)  *)
    (* SUM = (p1 + p2) + (p3 + p4).  We must show SUM ~ RHS, where
       RHS = add (mult fSSSx fSn) (mult fSSx fn).
       Expand RHS:
         fSSSx = fSSx + fSx        [fib_SS at (Suc x)]
         fSSx  = fSx + fx          [fib_SS at x]
         mult fSSSx fSn = mult (fSSx+fSx) fSn = (fSSx*fSn) + (fSx*fSn) = p1 + p3  [rdist]
         mult fSSx fn  = mult (fSx+fx)  fn  = (fSx*fn) + (fx*fn) = p2 + p4        [rdist]
       so RHS ~ (p1 + p3) + (p2 + p4).
       And SUM = (p1 + p2) + (p3 + p4).  Need (p1+p2)+(p3+p4) ~ (p1+p3)+(p2+p4).
       Pure add comm/assoc rearrangement. *)

    (* ----- RHS side : RHS ~ (p1 + p3) + (p2 + p4) ----- *)
    (* fSSSx ~ fSSx + fSx *)
    val fibSSSx = fibSS_at (suc xF);   (* oeq fSSSx (add fSSx fSx) *)
    (* fSSx ~ fSx + fx *)
    val fibSSx  = fibSS_at xF;         (* oeq fSSx (add fSx fx) *)
    (* mult fSSSx fSn ~ mult (fSSx+fSx) fSn   [cong-left fibSSSx] *)
    val rA1 = mult_cong_lF (fSSSx, add fSSx fSx, fSn) fibSSSx;
    (* mult (fSSx+fSx) fSn ~ (fSSx*fSn)+(fSx*fSn) = p1 + p3   [right_distrib] *)
    val rA2 = rdistF_at (fSSx, fSx, fSn);     (* oeq (mult (add fSSx fSx) fSn) (add (mult fSSx fSn)(mult fSx fSn)) *)
    val termA = oeq_trans OF [rA1, rA2];      (* mult fSSSx fSn ~ add p1 p3 *)
    (* mult fSSx fn ~ mult (fSx+fx) fn ~ (fSx*fn)+(fx*fn) = p2 + p4 *)
    val rB1 = mult_cong_lF (fSSx, add fSx fx, fn0) fibSSx;
    val rB2 = rdistF_at (fSx, fx, fn0);       (* oeq (mult (add fSx fx) fn) (add (mult fSx fn)(mult fx fn)) *)
    val termB = oeq_trans OF [rB1, rB2];      (* mult fSSx fn ~ add p2 p4 *)
    (* RHS = add (mult fSSSx fSn)(mult fSSx fn) ~ add (add p1 p3)(add p2 p4) *)
    val rhsExpL = add_cong_lF (mult fSSSx fSn, add p1 p3, mult fSSx fn0) termA;
    val rhsExpR = add_cong_rF (add p1 p3, mult fSSx fn0, add p2 p4) termB;
    val rhsExp  = oeq_trans OF [rhsExpL, rhsExpR];
        (* RHS ~ add (add p1 p3) (add p2 p4) *)

    (* ----- the pure additive rearrangement :
             (p1 + p2) + (p3 + p4)  ~  (p1 + p3) + (p2 + p4)
       Route:
         (p1+p2)+(p3+p4)
            ~ p1 + (p2 + (p3+p4))        [assoc]
            ~ p1 + ((p2+p3) + p4)        [assoc sym, inside]
            ~ p1 + ((p3+p2) + p4)        [comm on p2 p3, inside]
            ~ p1 + (p3 + (p2 + p4))      [assoc, inside]
            ~ (p1 + p3) + (p2 + p4)      [assoc sym]                              ----- *)
    val rr1 = addassocF_at (p1, p2, add p3 p4);        (* (p1+p2)+(p3+p4) ~ p1 + (p2+(p3+p4)) *)
    (* inside : p2 + (p3 + p4) ~ (p2 + p3) + p4   [assoc sym] *)
    val inA = oeq_sym OF [addassocF_at (p2, p3, p4)];   (* p2+(p3+p4) ~ (p2+p3)+p4 *)
    val rr2 = add_cong_rF (p1, add p2 (add p3 p4), add (add p2 p3) p4) inA;
    (* inside : (p2+p3) ~ (p3+p2)   [comm] ; cong-left into _ + p4 *)
    val cmm = addcommF_at (p2, p3);                     (* p2+p3 ~ p3+p2 *)
    val inB = add_cong_lF (add p2 p3, add p3 p2, p4) cmm; (* (p2+p3)+p4 ~ (p3+p2)+p4 *)
    val rr3 = add_cong_rF (p1, add (add p2 p3) p4, add (add p3 p2) p4) inB;
    (* inside : (p3+p2)+p4 ~ p3 + (p2+p4)   [assoc] *)
    val inC = addassocF_at (p3, p2, p4);               (* (p3+p2)+p4 ~ p3+(p2+p4) *)
    val rr4 = add_cong_rF (p1, add (add p3 p2) p4, add p3 (add p2 p4)) inC;
    (* outer : p1 + (p3 + (p2+p4)) ~ (p1+p3) + (p2+p4)   [assoc sym] *)
    val rr5 = oeq_sym OF [addassocF_at (p1, p3, add p2 p4)];
    val rearr = chain [rr1, rr2, rr3, rr4, rr5];
        (* (p1+p2)+(p3+p4) ~ (p1+p3)+(p2+p4) *)

    (* Now: SUM (= add (Qrhs Sx) (Qrhs x)) is literally (p1+p2)+(p3+p4) since
         Qrhs(Suc x) = add p1 p2  and  Qrhs x = add p3 p4 ... CHECK orientation:
         Qrhs(Suc x) = add (mult fSSx fSn) (mult fSx fn) = add p1 p2.    YES.
         Qrhs(x)     = add (mult fSx  fSn) (mult fx  fn) = add p3 p4.    YES.
       So  add (Qrhs Sx) (Qrhs x)  IS  (p1+p2)+(p3+p4)  definitionally. Good. *)

    (* assemble :  LHS ~ SUM ~ (rearr) ~ RHS(rev) *)
  in chain [lhsToSum, rearr, oeq_sym OF [rhsExp]] end;

(* QSSx : jT (Q (Suc (Suc x))) -- verify it is the intended Q at (Suc(Suc x)) *)
val () =
  if (Thm.prop_of QSSx) aconv (jT (Qprop (suc (suc xF))))
  then out "OK QSSx shape\n"
  else (out ("FAIL QSSx shape\n  got = "
             ^ Syntax.string_of_term ctxtF (Thm.prop_of QSSx) ^ "\n"
             ^ "  want= " ^ Syntax.string_of_term ctxtF (jT (Qprop (suc (suc xF)))) ^ "\n"));

(* P(Suc x) = Conj (Q(Suc x)) (Q(Suc(Suc x))) *)
val stepConj = conjI_vF OF [QSx, QSSx];          (* jT (Conj (Q Sx) (Q SSx)) *)
val stepThm  = Thm.forall_intr (ctermF xF) (Thm.implies_intr (ctermF ihprop) stepConj);

(* ---- apply nat_induct on P, then project conjunct1 to get Q k ---- *)
val kFree = Free ("k", natT);
val ind = beta_norm (Drule.infer_instantiate ctxtF
      [(("P",0), ctermF Ppred), (("k",0), ctermF kFree)] nat_induct_vF);
val pk_at_base = Thm.implies_elim ind baseConj;          (* (step) ==> jT (P k) *)
val pk = Thm.implies_elim pk_at_base stepThm;            (* jT (P k) = jT (Conj (Q k)(Q (Suc k))) *)
val qk = conjunct1_vF OF [pk];                           (* jT (Q k)  -- the identity at k *)

(* qk has free vars k (from kFree) and n (from nFree); varify turns them schematic. *)
val fib_add2 = varify qk;

val mV = Var (("k",0), natT);   (* qk's free var name was k (kFree) *)
val nV = Var (("n",0), natT);
val fib_add_intended =
  jT (oeq (fib (suc (add mV nV)))
          (add (mult (fib (suc mV)) (fib (suc nV))) (mult (fib mV) (fib nV))));

val r_fib_add = checkF ("fib_add", fib_add2, fib_add_intended);

(* ---- SOUNDNESS PROBE : kernel must REJECT dropping the second product
        (i.e. fib(Suc(m+n)) = fib(Sm)*fib(Sn) alone is FALSE). ---- *)
val probe_add =
  let val bogus = jT (oeq (fib (suc (add mV nV))) (mult (fib (suc mV)) (fib (suc nV))))
  in not ((Thm.prop_of fib_add2) aconv bogus) end;
val () = if probe_add then out "PROBE_OK fib_add keeps both product terms\n"
                      else out "PROBE_UNSOUND fib_add dropped a term!\n";

val () =
  if r_fib_add andalso probe_add
  then out "FIB_ADD_OK\n"
  else out "FIB_ADD_FAILED\n";

(* ============================================================================
   CASSINI'S IDENTITY for the standard Fibonacci numbers, in N, sign-free,
   via the PARITY / two-index simultaneous-induction route.

   Spliced AFTER fib_base.sml (on common::with_nt_helpers).  In scope:
   ctxtF/ctermF, fib/fib_0/fib_1/fib_SS/fib_two, oeq/add/mult/suc/ZeroC/one,
   jT/varify/beta_norm/out, oeq_refl/oeq_sym/oeq_trans/oeq_subst/Suc_cong,
   add_*/mult_*/left_distrib/right_distrib/nat_induct,
   mkConj/ConjC/conjI_ax/conjunct1_ax/conjunct2_ax.

   Parity lemmas (s = Suc, d = dbl k = 2k):
     (a)  fib(d)   * fib(s s d)   + 1  =  fib(s d)^2          [even index]
     (b)  fib(s d) * fib(s s s d)      =  fib(s s d)^2 + 1    [odd index]
   ONE simultaneous induction on k proving  Conj (A (dbl k)) (B (dbl k)).

   Forward-only N step derivations (symbolically verified):
     A(s s d) from B(d):
       fib(ssd)*fib(ssssd)+1
       = fib(ssd)*(fib(sssd)+fib(ssd)) + 1            [fib_SS at (ss d)]
       = fib(ssd)*fib(sssd) + (fib(ssd)*fib(ssd)+1)   [left_distrib + add_assoc]
       = fib(ssd)*fib(sssd) + fib(sd)*fib(sssd)       [B(d)]
       = (fib(ssd)+fib(sd))*fib(sssd)                 [right_distrib^-1]
       = fib(sssd)*fib(sssd)                          [fib_SS at (s d), symm]
     B(s s d) from A(s s d):
       fib(sssd)*fib(sssssd)
       = fib(sssd)*(fib(ssssd)+fib(sssd))             [fib_SS at (sss d)]
       = fib(sssd)*fib(ssssd) + fib(sssd)*fib(sssd)   [left_distrib]
       = fib(sssd)*fib(ssssd) + (fib(ssd)*fib(ssssd)+1) [A(ss d)]
       = (fib(sssd)+fib(ssd))*fib(ssssd) + 1          [right_distrib^-1 + add_assoc]
       = fib(ssssd)*fib(ssssd) + 1                    [fib_SS at (ss d), symm]

   Fresh const `dbl` EXTENDS the theory -> ONE further context ctxtF2/ctermF2.
   ============================================================================ *)

(* ---- fresh const dbl : nat -> nat,  dbl 0 = 0, dbl(Suc k) = Suc(Suc(dbl k)) ---- *)
val thyF2a = Sign.add_consts [(Binding.name "dbl", natT --> natT, NoSyn)] thyF;
val dblC = Const (Sign.full_name thyF2a (Binding.name "dbl"), natT --> natT);
fun dbl t = dblC $ t;
val kFd = Free ("kFd", natT);
val ((_,dbl_0), thyF2b) = Thm.add_axiom_global (Binding.name "dbl_0",
      jT (oeq (dbl ZeroC) ZeroC)) thyF2a;
val ((_,dbl_S), thyF2)  = Thm.add_axiom_global (Binding.name "dbl_S",
      jT (oeq (dbl (suc kFd)) (suc (suc (dbl kFd))))) thyF2b;

val ctxtF2  = Proof_Context.init_global thyF2;
val ctermF2 = Thm.cterm_of ctxtF2;

(* ---- re-varify reused lemmas onto ctxtF2 ---- *)
val oeq_refl_2   = varify oeq_refl;
val oeq_sym_2    = varify oeq_sym;
val oeq_trans_2  = varify oeq_trans;
val oeq_subst_2  = varify oeq_subst;
val Suc_cong_2   = varify Suc_cong;
val add_comm_2   = varify add_comm;
val add_assoc_2  = varify add_assoc;
val add_0_2      = varify add_0;
val add_Suc_2    = varify add_Suc;
val add_0_right_2= varify add_0_right;
val mult_comm_2  = varify mult_comm;
val mult_assoc_2 = varify mult_assoc;
val left_distrib_2  = varify left_distrib;
val right_distrib_2 = varify right_distrib;
val mult_0_2     = varify mult_0;
val mult_Suc_2   = varify mult_Suc;
val nat_induct_2 = varify nat_induct;
val fib_0_2      = varify fib_0;
val fib_1_2      = varify fib_1;
val fib_SS_2     = varify fib_SS;
val fib_two_2    = varify fib_two;
val conjI_2      = varify conjI_ax;
val conjunct1_2  = varify conjunct1_ax;
val conjunct2_2  = varify conjunct2_ax;
val dbl_0_2      = varify dbl_0;
val dbl_S_2      = varify dbl_S;

(* ---- instantiators / chaining on ctxtF2 ---- *)
fun oeqrefl2 t   = beta_norm (Drule.infer_instantiate ctxtF2 [(("a",0), ctermF2 t)] oeq_refl_2);
fun symm2 h      = oeq_sym_2 OF [h];
fun trans2 (h1,h2) = oeq_trans_2 OF [h1, h2];
fun chain2 [] = raise Fail "chain2 empty"
  | chain2 [h] = h
  | chain2 (h::hs) = trans2 (h, chain2 hs);
fun fibSS2 t   = beta_norm (Drule.infer_instantiate ctxtF2 [(("kF",0), ctermF2 t)] fib_SS_2);
fun addassoc2 (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtF2
                   [(("m",0), ctermF2 mt),(("n",0), ctermF2 nt),(("k",0), ctermF2 kt)] add_assoc_2);
fun ldist2 (aT,bT,kT) = beta_norm (Drule.infer_instantiate ctxtF2
                   [(("x",0), ctermF2 aT),(("m",0), ctermF2 bT),(("n",0), ctermF2 kT)] left_distrib_2);
fun rdist2 (aT,bT,kT) = beta_norm (Drule.infer_instantiate ctxtF2
                   [(("m",0), ctermF2 aT),(("n",0), ctermF2 bT),(("k",0), ctermF2 kT)] right_distrib_2);
fun dblS2 t    = beta_norm (Drule.infer_instantiate ctxtF2 [(("kFd",0), ctermF2 t)] dbl_S_2);
val dbl0_2     = dbl_0_2;
fun add0_2 t   = beta_norm (Drule.infer_instantiate ctxtF2 [(("n",0), ctermF2 t)] add_0_2);
fun add0r_2 t  = beta_norm (Drule.infer_instantiate ctxtF2 [(("n",0), ctermF2 t)] add_0_right_2);
fun addSuc2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF2
                   [(("m",0), ctermF2 mt),(("n",0), ctermF2 nt)] add_Suc_2);
fun mult0_2 t  = beta_norm (Drule.infer_instantiate ctxtF2 [(("n",0), ctermF2 t)] mult_0_2);
fun multSuc2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF2
                   [(("m",0), ctermF2 mt),(("n",0), ctermF2 nt)] mult_Suc_2);

(* congruences on ctxtF2 *)
fun add_cong_l2 (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("P",0), ctermF2 Pabs), (("a",0), ctermF2 pT), (("b",0), ctermF2 qT)] oeq_subst_2);
  in inst OF [hpq, oeqrefl2 (add pT kT)] end;
fun add_cong_r2 (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("P",0), ctermF2 Pabs), (("a",0), ctermF2 pT), (("b",0), ctermF2 qT)] oeq_subst_2);
  in inst OF [hpq, oeqrefl2 (add hT pT)] end;
fun mult_cong_l2 (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("P",0), ctermF2 Pabs), (("a",0), ctermF2 pT), (("b",0), ctermF2 qT)] oeq_subst_2);
  in inst OF [hpq, oeqrefl2 (mult pT kT)] end;
fun mult_cong_r2 (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("P",0), ctermF2 Pabs), (("a",0), ctermF2 pT), (("b",0), ctermF2 qT)] oeq_subst_2);
  in inst OF [hpq, oeqrefl2 (mult hT pT)] end;

(* GENERAL TRANSPORT of a propositional schema by an index equality.
   mkProp : term -> term  builds the OBJECT proposition (an oT term, no jT).
   given (h : oeq d1 d2) and (proof : jT (mkProp d1)), returns jT (mkProp d2).
   Uses oeq_subst with P := %w. mkProp w. *)
fun transport mkProp (d1, d2) hEq proofAt1 =
  let
    val w = Bound 0;
    val Pabs = Abs("w", natT, mkProp w);
    val inst = beta_norm (Drule.infer_instantiate ctxtF2
          [(("P",0), ctermF2 Pabs), (("a",0), ctermF2 d1), (("b",0), ctermF2 d2)] oeq_subst_2);
  in Thm.implies_elim (Thm.implies_elim inst hEq) proofAt1 end;

(* Conj helpers on ctxtF2 *)
fun mkConjF s t = ConjC $ s $ t;
fun conjI_F (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("A",0), ctermF2 At),(("B",0), ctermF2 Bt)] conjI_2);
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_F (At,Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("A",0), ctermF2 At),(("B",0), ctermF2 Bt)] conjunct1_2);
  in Thm.implies_elim inst hC end;
fun conjunct2_F (At,Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF2
            [(("A",0), ctermF2 At),(("B",0), ctermF2 Bt)] conjunct2_2);
  in Thm.implies_elim inst hC end;

fun checkF2 (nm, th, intended) =
  let val nh = length (Thm.hyps_of th);
      val ac = (Thm.prop_of th) aconv intended;
  in if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
     else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
                ^ "  got      = " ^ Syntax.string_of_term ctxtF2 (Thm.prop_of th) ^ "\n"
                ^ "  intended = " ^ Syntax.string_of_term ctxtF2 intended ^ "\n"); false)
  end;

(* ---- the A / B parity statements (object props, functions of index d) ---- *)
fun sq t = mult t t;
fun Aprop d = oeq (add (mult (fib d) (fib (suc (suc d)))) one) (sq (fib (suc d)));
fun Bprop d = oeq (mult (fib (suc d)) (fib (suc (suc (suc d)))))
                  (add (sq (fib (suc (suc d)))) one);
fun Pprop d = mkConjF (Aprop d) (Bprop d);

val () = out "checkpoint defs built\n";

(* ============================================================================
   small numeric fib facts on ctxtF2
   ============================================================================ *)
val f0 = fib_0_2;                 (* oeq (fib 0) 0 *)
val f1 = fib_1_2;                 (* oeq (fib 1) 1 *)
val f2 = fib_two_2;              (* oeq (fib (s s 0)) 1 *)
val two = suc one;               (* s s 0 = 2 *)
(* add 1 1 = s(s 0) = two *)
val add_1_1 =
  let
    val aS = addSuc2 (ZeroC, one);   (* add (s 0)(s 0) = s (add 0 (s 0)) *)
    val a0 = add0_2 one;             (* add 0 (s 0) = s 0 *)
    val sc = Suc_cong_2 OF [a0];     (* s(add 0 (s 0)) = s (s 0) *)
  in chain2 [aS, sc] end;            (* add 1 1 = two *)
(* fib 3 = fib 2 + fib 1 = 1 + 1 = two *)
val f3v =
  let
    val ss  = fibSS2 (suc ZeroC);                                 (* fib 3 = add (fib2)(fib1) *)
    val cL  = add_cong_l2 (fib (suc (suc ZeroC)), one, fib one) f2;  (* = add 1 (fib1) *)
    val cR  = add_cong_r2 (one, fib one, one) f1;                 (* = add 1 1 *)
  in chain2 [ss, cL, cR, add_1_1] end;                           (* fib 3 = two *)
(* mult 1 t = t  (mult_1_left), small helper for the base *)
fun mult1L t =
  let
    val mS = multSuc2 (ZeroC, t);    (* mult (s 0) t = add t (mult 0 t) *)
    val m0 = mult0_2 t;              (* mult 0 t = 0 *)
    val cr = add_cong_r2 (t, mult ZeroC t, ZeroC) m0;  (* add t (mult 0 t) = add t 0 *)
    val a0 = add0r_2 t;              (* add t 0 = t *)
  in chain2 [mS, cr, a0] end;        (* mult 1 t = t *)

(* ============================================================================
   BASE  A(0) , B(0)  at literal index 0
   ============================================================================ *)
val A0 =
  let
    (* LHS: add (mult (fib 0)(fib 2)) 1 = 1 *)
    val c1 = mult_cong_l2 (fib ZeroC, ZeroC, fib (suc (suc ZeroC))) f0;  (* mult(fib0)(fib2)=mult 0 (fib2) *)
    val c2 = mult0_2 (fib (suc (suc ZeroC)));                            (* mult 0 (fib2)=0 *)
    val m0 = chain2 [c1, c2];                                            (* mult(fib0)(fib2)=0 *)
    val cl = add_cong_l2 (mult (fib ZeroC) (fib (suc (suc ZeroC))), ZeroC, one) m0; (* +1 -> add 0 1 *)
    val a01= add0_2 one;                                                 (* add 0 1 = 1 *)
    val lhs= chain2 [cl, a01];                                           (* LHS = 1 *)
    (* RHS: mult(fib1)(fib1) = mult 1 (fib1) = mult 1 1 = 1 *)
    val r1 = mult_cong_l2 (fib one, one, fib one) f1;     (* = mult 1 (fib1) *)
    val r2 = mult_cong_r2 (one, fib one, one) f1;         (* = mult 1 1 *)
    val r3 = mult1L one;                                  (* mult 1 1 = 1 *)
    val rhs= chain2 [r1, r2, r3];                         (* RHS = 1 *)
  in chain2 [lhs, symm2 rhs] end;                         (* LHS = RHS  => A(0) *)

val B0 =
  let
    (* LHS: mult(fib1)(fib3) = mult 1 (fib3) = mult 1 two = two *)
    val c1 = mult_cong_l2 (fib one, one, fib (suc (suc (suc ZeroC)))) f1;
    val c2 = mult_cong_r2 (one, fib (suc (suc (suc ZeroC))), two) f3v;   (* = mult 1 two *)
    val c3 = mult1L two;                                                 (* mult 1 two = two *)
    val lhs= chain2 [c1, c2, c3];                                        (* LHS = two *)
    (* RHS: add (mult(fib2)(fib2)) 1 = add (mult 1 1) 1 = add 1 1 = two *)
    val r1 = mult_cong_l2 (fib (suc (suc ZeroC)), one, fib (suc (suc ZeroC))) f2;
    val r2 = mult_cong_r2 (one, fib (suc (suc ZeroC)), one) f2;          (* = mult 1 1 *)
    val r3 = mult1L one;                                                 (* mult 1 1 = 1 *)
    val m11= chain2 [r1, r2, r3];                                        (* mult(fib2)(fib2)=1 *)
    val cl = add_cong_l2 (sq (fib (suc (suc ZeroC))), one, one) m11;     (* add (...) 1 = add 1 1 *)
    val rhs= chain2 [cl, add_1_1];                                       (* RHS = two *)
  in chain2 [lhs, symm2 rhs] end;                                        (* LHS = RHS => B(0) *)

(* transport A0/B0 from index 0 to index (dbl 0), then bundle as Conj.
   We need Aprop(dbl 0) and Bprop(dbl 0); have Aprop 0, Bprop 0; dbl_0 : oeq (dbl 0) 0.
   transport Aprop (0, dbl 0) needs oeq 0 (dbl 0) = symm(dbl_0). *)
val dbl0eq = dbl0_2;                              (* oeq (dbl 0) 0 *)
val zero_eq_dbl0 = symm2 dbl0eq;                  (* oeq 0 (dbl 0) *)
val A_dbl0 = transport Aprop (ZeroC, dbl ZeroC) zero_eq_dbl0 A0;   (* jT (Aprop (dbl 0)) *)
val B_dbl0 = transport Bprop (ZeroC, dbl ZeroC) zero_eq_dbl0 B0;
val baseThm = conjI_F (Aprop (dbl ZeroC), Bprop (dbl ZeroC)) A_dbl0 B_dbl0; (* jT (Pprop (dbl 0)) *)

val () = out "checkpoint base built\n";

(* ============================================================================
   STEP : assume IH : jT (Pprop (dbl x)) ; prove jT (Pprop (dbl (Suc x))).
   Let d = dbl x.  We derive A(s s d) from B(d), then B(s s d) from A(s s d),
   then conjI and transport (s s d -> dbl(Suc x)) by dbl_S.
   ============================================================================ *)
val xF = Free ("xCass", natT);
val dX = dbl xF;                                   (* d = dbl x *)
val ihprop = jT (Pprop dX);
val IH = Thm.assume (ctermF2 ihprop);
val Ad = conjunct1_F (Aprop dX, Bprop dX) IH;      (* jT (Aprop d) *)
val Bd = conjunct2_F (Aprop dX, Bprop dX) IH;      (* jT (Bprop d) *)

(* index abbreviations in terms of d *)
val d0 = dX;
val d1 = suc dX;          (* s d   *)
val d2 = suc (suc dX);    (* ss d  *)
val d3 = suc (suc (suc dX));        (* sss d  *)
val d4 = suc (suc (suc (suc dX)));  (* ssss d *)
val d5 = suc (suc (suc (suc (suc dX)))); (* sssss d *)
val fd0 = fib d0; val fd1 = fib d1; val fd2 = fib d2;
val fd3 = fib d3; val fd4 = fib d4; val fd5 = fib d5;

(* ---- A(s s d) : add (mult fd2 fd4) 1 = sq fd3 ---- *)
val A_ssd =
  let
    (* (1) fib_SS at (ss d): fib(d4) = add fd3 fd2 *)
    val ss4 = fibSS2 d2;                            (* oeq fd4 (add fd3 fd2) *)
    (* mult fd2 fd4 = mult fd2 (add fd3 fd2)  [cong r] *)
    val s1 = mult_cong_r2 (fd2, fd4, add fd3 fd2) ss4;
    (* (2) left_distrib: mult fd2 (add fd3 fd2) = add (mult fd2 fd3)(mult fd2 fd2) *)
    val s2 = ldist2 (fd2, fd3, fd2);
    val multStep = chain2 [s1, s2];                 (* mult fd2 fd4 = add (mult fd2 fd3)(mult fd2 fd2) *)
    (* (3) lift through (add _ 1) *)
    val l3 = add_cong_l2 (mult fd2 fd4, add (mult fd2 fd3) (mult fd2 fd2), one) multStep;
    (* (4) add_assoc: add (add (mult fd2 fd3)(mult fd2 fd2)) 1
                    = add (mult fd2 fd3) (add (mult fd2 fd2) 1) *)
    val l4 = addassoc2 (mult fd2 fd3, mult fd2 fd2, one);
    (* (5) B(d): mult fd1 fd3 = add (mult fd2 fd2) 1 ; so add (mult fd2 fd2) 1 = mult fd1 fd3 [symm] *)
    val bsym = symm2 Bd;                            (* oeq (add (mult fd2 fd2) 1) (mult fd1 fd3) *)
    val l5 = add_cong_r2 (mult fd2 fd3, add (mult fd2 fd2) one, mult fd1 fd3) bsym;
    (* (6) right_distrib reverse: add (mult fd2 fd3)(mult fd1 fd3) = mult (add fd2 fd1) fd3 *)
    val rd = rdist2 (fd2, fd1, fd3);               (* mult (add fd2 fd1) fd3 = add (mult fd2 fd3)(mult fd1 fd3) *)
    val l6 = symm2 rd;                              (* add (...)(...) = mult (add fd2 fd1) fd3 *)
    (* (7) fib_SS at (s d): fib(d3) = add fd2 fd1 ; so add fd2 fd1 = fd3 [symm], cong l into mult _ fd3 *)
    val ss3 = fibSS2 d1;                            (* oeq fd3 (add fd2 fd1) *)
    val ss3s = symm2 ss3;                           (* oeq (add fd2 fd1) fd3 *)
    val l7 = mult_cong_l2 (add fd2 fd1, fd3, fd3) ss3s;  (* mult (add fd2 fd1) fd3 = mult fd3 fd3 *)
  in chain2 [l3, l4, l5, l6, l7] end;              (* add (mult fd2 fd4) 1 = mult fd3 fd3 = sq fd3 *)

(* ---- B(s s d) : mult fd3 fd5 = add (sq fd4) 1 ---- *)
val B_ssd =
  let
    (* (1) fib_SS at (sss d): fib(d5) = add fd4 fd3 *)
    val ss5 = fibSS2 d3;                            (* oeq fd5 (add fd4 fd3) *)
    val s1 = mult_cong_r2 (fd3, fd5, add fd4 fd3) ss5; (* mult fd3 fd5 = mult fd3 (add fd4 fd3) *)
    (* (2) left_distrib: mult fd3 (add fd4 fd3) = add (mult fd3 fd4)(mult fd3 fd3) *)
    val s2 = ldist2 (fd3, fd4, fd3);
    val l12 = chain2 [s1, s2];                      (* = add (mult fd3 fd4)(mult fd3 fd3) *)
    (* (3) A(ss d): add (mult fd2 fd4) 1 = mult fd3 fd3 ; so mult fd3 fd3 = add (mult fd2 fd4) 1 [symm] *)
    val asym = symm2 A_ssd;                         (* oeq (mult fd3 fd3) (add (mult fd2 fd4) 1) *)
    val l3 = add_cong_r2 (mult fd3 fd4, mult fd3 fd3, add (mult fd2 fd4) one) asym;
                                                    (* = add (mult fd3 fd4) (add (mult fd2 fd4) 1) *)
    (* (4) add_assoc reverse: add (mult fd3 fd4)(add (mult fd2 fd4) 1)
                            = add (add (mult fd3 fd4)(mult fd2 fd4)) 1 *)
    val asc = addassoc2 (mult fd3 fd4, mult fd2 fd4, one);  (* (add (m34)(m24))+1 = m34 + (m24+1) *)
    val ascS = symm2 asc;                           (* add (m34)(m24+1)... wait orientation *)
    (* asc : oeq (add (add (mult fd3 fd4)(mult fd2 fd4)) 1) (add (mult fd3 fd4)(add (mult fd2 fd4) 1)) *)
    (* we have ... = add (mult fd3 fd4)(add (mult fd2 fd4) 1) ; want add (add ..)(..) 1 ; so use symm asc *)
    val l4 = symm2 asc;                             (* add (m34)(m24+1) = add (add m34 m24) 1 *)
    (* (5) right_distrib reverse: add (mult fd3 fd4)(mult fd2 fd4) = mult (add fd3 fd2) fd4 *)
    val rd = rdist2 (fd3, fd2, fd4);               (* mult (add fd3 fd2) fd4 = add (mult fd3 fd4)(mult fd2 fd4) *)
    val rdS = symm2 rd;                             (* add (m34)(m24) = mult (add fd3 fd2) fd4 *)
    val l5 = add_cong_l2 (add (mult fd3 fd4) (mult fd2 fd4), mult (add fd3 fd2) fd4, one) rdS;
                                                    (* add (add m34 m24) 1 = add (mult (add fd3 fd2) fd4) 1 *)
    (* (6) fib_SS at (ss d): fib(d4) = add fd3 fd2 ; so add fd3 fd2 = fd4 [symm], cong l into mult _ fd4 *)
    val ss4 = fibSS2 d2;                            (* oeq fd4 (add fd3 fd2) *)
    val ss4s = symm2 ss4;                           (* add fd3 fd2 = fd4 *)
    val cl = mult_cong_l2 (add fd3 fd2, fd4, fd4) ss4s;  (* mult (add fd3 fd2) fd4 = mult fd4 fd4 *)
    val l6 = add_cong_l2 (mult (add fd3 fd2) fd4, mult fd4 fd4, one) cl;  (* +1 lifted *)
  in chain2 [l12, l3, l4, l5, l6] end;             (* mult fd3 fd5 = add (mult fd4 fd4) 1 = add (sq fd4) 1 *)

val () = out "checkpoint step components built\n";

(* check A_ssd and B_ssd have the intended (object) shape *)
val () = out ("A_ssd prop: " ^ Syntax.string_of_term ctxtF2 (Thm.prop_of A_ssd) ^ "\n");
val () = out ("B_ssd prop: " ^ Syntax.string_of_term ctxtF2 (Thm.prop_of B_ssd) ^ "\n");

(* aconv check: A_ssd should be jT (Aprop d2), B_ssd should be jT (Bprop d2) ;
   each carries exactly the IH hypothesis (so hyps = [ihprop]). *)
val () = out ("A_ssd aconv Aprop d2 : " ^ Bool.toString ((Thm.prop_of A_ssd) aconv (jT (Aprop d2))) ^ "\n");
val () = out ("B_ssd aconv Bprop d2 : " ^ Bool.toString ((Thm.prop_of B_ssd) aconv (jT (Bprop d2))) ^ "\n");
val () = out ("A_ssd #hyps = " ^ Int.toString (length (Thm.hyps_of A_ssd)) ^ "\n");

(* ---- conjI then transport (s s d) -> dbl(Suc x) ---- *)
val P_ssd = conjI_F (Aprop d2, Bprop d2) A_ssd B_ssd;   (* jT (Pprop (ss d)) , hyp = ihprop *)
(* dbl_S at x : oeq (dbl (Suc x)) (s s (dbl x)) = oeq (dbl(Sx)) d2 *)
val dblSx = dblS2 xF;                                    (* oeq (dbl (Suc x)) (s s d) *)
(* transport Pprop from (s s d) to (dbl (Suc x)) needs oeq (s s d) (dbl(Sx)) = symm dblSx *)
val ssd_eq_dblSx = symm2 dblSx;                          (* oeq (s s d) (dbl (Suc x)) *)
val P_dblSx = transport Pprop (d2, dbl (suc xF)) ssd_eq_dblSx P_ssd;  (* jT (Pprop (dbl (Suc x))) *)

(* discharge the IH, forall_intr x -> the nat_induct step premise shape *)
val stepThm = Thm.forall_intr (ctermF2 xF) (Thm.implies_intr (ctermF2 ihprop) P_dblSx);
val () = out "checkpoint step assembled\n";

(* ============================================================================
   THE INDUCTION : nat_induct with P := Ppred = %z. Pprop (dbl z), at schematic k
   ============================================================================ *)
val kCass = Free ("kInd", natT);
val Ppred = Abs ("z", natT, Pprop (dbl (Bound 0)));     (* %z. Conj (A (dbl z)) (B (dbl z)) *)
val ind = beta_norm (Drule.infer_instantiate ctxtF2
      [(("P",0), ctermF2 Ppred), (("k",0), ctermF2 kCass)] nat_induct_2);
val r1 = Thm.implies_elim ind baseThm;
val r2 = Thm.implies_elim r1 stepThm;                   (* jT (Pprop (dbl kInd)) *)
val cassiniConj = varify r2;                            (* schematic in k *)
val () = out "checkpoint induction done\n";

(* ---- extract the two parity lemmas (still schematic in k) ---- *)
val kVar = Var (("k",0), natT);
val dblk = dbl kVar;
val cassiniConj_at_k =
  beta_norm (Drule.infer_instantiate ctxtF2 [(("kInd",0), ctermF2 kVar)] cassiniConj);
val cassini_a = conjunct1_F (Aprop dblk, Bprop dblk) cassiniConj_at_k;  (* jT (Aprop (dbl k)) *)
val cassini_b = conjunct2_F (Aprop dblk, Bprop dblk) cassiniConj_at_k;  (* jT (Bprop (dbl k)) *)

(* ---- validate ---- *)
val cassini_a_intended = jT (Aprop (dbl kVar));
val cassini_b_intended = jT (Bprop (dbl kVar));
val ra = checkF2 ("cassini_a (even index 2k)", cassini_a, cassini_a_intended);
val rb = checkF2 ("cassini_b (odd index 2k+1)", cassini_b, cassini_b_intended);

(* ---- soundness probes ---- *)
(* (a) the +1 must be present (not dropped): reject the no-+1 variant of lemma (a). *)
val probe_a_plus1 =
  let val bogus = jT (oeq (mult (fib (dbl kVar)) (fib (suc (suc (dbl kVar))))) (sq (fib (suc (dbl kVar)))))
  in not ((Thm.prop_of cassini_a) aconv bogus) end;
(* (b) the +1 in lemma (b) lands on the RIGHT (not on the left): reject left-+1 variant. *)
val probe_b_side =
  let val bogus = jT (oeq (add (mult (fib (suc (dbl kVar))) (fib (suc (suc (suc (dbl kVar)))))) one)
                          (sq (fib (suc (suc (dbl kVar))))))
  in not ((Thm.prop_of cassini_b) aconv bogus) end;
val () = if probe_a_plus1 then out "PROBE_OK cassini_a keeps +1\n" else out "PROBE_UNSOUND cassini_a dropped +1\n";
val () = if probe_b_side  then out "PROBE_OK cassini_b +1 on the correct side\n" else out "PROBE_UNSOUND cassini_b +1 side wrong\n";

val () =
  if ra andalso rb andalso probe_a_plus1 andalso probe_b_side
  then out "FIB_CASSINI_OK\n"
  else out "FIB_CASSINI_FAILED\n";

(* explicit 0-hyp evidence + final statement printout *)
val () = out ("cassini_a #hyps = " ^ Int.toString (length (Thm.hyps_of cassini_a)) ^ "\n");
val () = out ("cassini_b #hyps = " ^ Int.toString (length (Thm.hyps_of cassini_b)) ^ "\n");
val () = out ("STMT cassini_a = " ^ Syntax.string_of_term ctxtF2 (Thm.prop_of cassini_a) ^ "\n");
val () = out ("STMT cassini_b = " ^ Syntax.string_of_term ctxtF2 (Thm.prop_of cassini_b) ^ "\n");
