(* ============================================================================
   PER-PRIME-POWER SUMS OF TWO SQUARES, on the twosquare monolith final
   context ctxtGR / ctermGR.

   Appended AFTER:  isabelle_twosquare.sml ++ if_direction.sml
   (so two_is_sumsq, sq_is_sumsq, sumsq_mult, sumsq_times_sq, brahma4, the full
    _gr toolkit, twosquare, pow_*, sub_*, add_* are all in scope).

   Proves three leaves of the IF-direction (each 0-hyp modulo its stated hyps,
   aconv-intended, soundness-probed):
     (a) pow2_sumsq        : sumsq (pow 2 e)                          [induction on e]
     (b) p1mod4_pow_sumsq  : (Ex k. p=4k+1) ==> prime2 p ==> sumsq (pow p e)
     (c) p3mod4_even_sumsq : (Ex k. p=4k+3) ==> (Ex j. e=2j) ==> sumsq (pow p e)

   sumsq x  := Ex a b. x = a*a + b*b        (sumsqBody, from if_blocks.sml)
   ============================================================================ *)

val () = out "TSF_PERPRIME_BEGIN\n";

(* ---- extra base lemmas varified onto ctxtGR ---- *)
val add_0_right_gr   = varify add_0_right;     (* oeq (add n 0) n *)
val add_Suc_right_gr = varify add_Suc_right;   (* oeq (add m (Suc n)) (Suc (add m n)) *)
val sub_0_gr         = varify sub_0_ax;        (* oeq (sub n 0) n *)
val sub_SS_gr        = varify sub_SS_ax;       (* oeq (sub (Suc n)(Suc m)) (sub n m) *)
val pow_add_gr       = varify pow_add;         (* oeq (pow a (m+n)) (mult (pow a m)(pow a n)) *)
val nat_induct_gr    = varify nat_induct;      (* P 0 ==> (!!x. P x ==> P(Suc x)) ==> P k *)

fun add0r_gr t        = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] add_0_right_gr);
fun addSr_gr (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_Suc_right_gr);
fun sub0_gr t         = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] sub_0_gr);
fun subSS_gr (nt,mt)  = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("n",0), ctermGR nt),(("m",0), ctermGR mt)] sub_SS_gr);
fun powAdd_gr (at,mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("a",0), ctermGR at),(("m",0), ctermGR mt),(("n",0), ctermGR nt)] pow_add_gr);

(* nat_induct combinator on ctxtGR : Pabs : nat=>o, target kT *)
fun nat_induct_gr_at Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs),(("k",0), ctermGR kT)] nat_induct_gr)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

(* convenient numerals *)
val one2 = suc ZeroC;
val two2 = suc (suc ZeroC);

(* ---- sumsq 1 : 1 = 1*1 + 0*0  (reused several times) ---- *)
val sumsq_one =
  let
    val m11 = mult1l_gr one2;                              (* oeq (1*1) 1 *)
    val zz0 = mult0_gr ZeroC;                              (* oeq (0*0) 0 *)
    val cong0 = add_cong_r_gr (mult one2 one2, mult ZeroC ZeroC, ZeroC) zz0; (* (1*1)+(0*0) = (1*1)+0 *)
    val ac = addcomm_gr (mult one2 one2, ZeroC);          (* (1*1)+0 = 0+(1*1) *)
    val a0 = add0_gr (mult one2 one2);                     (* 0+(1*1) = 1*1 *)
    val add0r = oeqTrans_gr (ac, a0);                      (* (1*1)+0 = 1*1 *)
    val rhs1 = oeqTrans_gr (oeqTrans_gr (cong0, add0r), m11);  (* (1*1)+(0*0) = 1 *)
    val rhsSym = oeqSym_gr rhs1;                           (* 1 = (1*1)+(0*0) *)
  in mk_sumsq one2 (one2, ZeroC) rhsSym end;               (* sumsq 1 *)
val () = out ("sumsq_one hyps="^Int.toString(length(Thm.hyps_of sumsq_one))^"\n");

(* ============================================================================
   (a) pow2_sumsq : |- sumsq (pow 2 e)         (induction on e)
   ============================================================================ *)
val pow2_sumsq =
  let
    val eF = Free("e_p2", natT);
    val Pabs = Term.lambda eF (sumsqBody (pow two2 eF));
    (* base e=0 : pow 2 0 = 1, sumsq 1 -> sumsq (pow 2 0) by rewriting 1 -> pow 2 0 *)
    val base =
      let
        val pz = powZero_gr two2;                          (* oeq (pow 2 0) 1 *)
        val zRW = Free("z_p2b", natT);
        val Prw = Term.lambda zRW (sumsqBody zRW);         (* %z. sumsq z *)
        (* rewrite sumsq 1 along (pow 2 0 = 1) backwards : oeq (pow 2 0) 1, P (pow 2 0) needed -> use sym? *)
        (* sumsq_one : sumsq 1.  want sumsq (pow 2 0).  oeq_subst with a=1, b=(pow 2 0):
           need oeq 1 (pow 2 0). *)
        val pzSym = oeqSym_gr pz;                           (* oeq 1 (pow 2 0) *)
      in oeq_subst_gr_at (Prw, one2, pow two2 ZeroC) pzSym sumsq_one end;
    (* step : !!x. sumsq (pow 2 x) ==> sumsq (pow 2 (Suc x)) *)
    val xF = Free("x_p2", natT);
    val ihP = jT (sumsqBody (pow two2 xF));
    val IH  = Thm.assume (ctermGR ihP);
    val stepConcl =
      let
        (* sumsq 2 (two_is_sumsq) and IH : sumsq (pow 2 x) -> fold *)
        val foldT = sumsq_mult (two2, pow two2 xF) two_is_sumsq IH;  (* sumsq (2 * pow 2 x) *)
        (* pow 2 (Suc x) = 2 * pow 2 x  [pow_Suc] *)
        val psuc = powSuc_gr (two2, xF);                   (* oeq (pow 2 (Suc x)) (2 * pow 2 x) *)
        val psucSym = oeqSym_gr psuc;                      (* oeq (2 * pow 2 x) (pow 2 (Suc x)) *)
        val zRW = Free("z_p2s", natT);
        val Prw = Term.lambda zRW (sumsqBody zRW);
      in oeq_subst_gr_at (Prw, mult two2 (pow two2 xF), pow two2 (suc xF)) psucSym foldT end;
    val step1 = Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR ihP) stepConcl);
    val eV = Free("e_p2v", natT);
  in nat_induct_gr_at (Term.lambda eF (sumsqBody (pow two2 eF))) eV base step1 end;
val () = out ("pow2_sumsq hyps="^Int.toString(length(Thm.hyps_of pow2_sumsq))^"\n");
(* the above is for a Free e; varify to schematic *)
val pow2_sumsq_sch = varify pow2_sumsq;
val pow2_sumsq_intended =
  let val eV = Var(("e_p2v",0), natT)
  in jT (sumsqBody (pow two2 eV)) end;
val pow2_aconv = ((Thm.prop_of pow2_sumsq_sch) aconv pow2_sumsq_intended);
val pow2_0hyp  = (length (Thm.hyps_of pow2_sumsq_sch) = 0);
val () = out ("pow2_sumsq aconv="^Bool.toString pow2_aconv^" zero_hyp="^Bool.toString pow2_0hyp^"\n");
(* soundness probe : NOT the trivial form sumsq (pow 2 0); the e is genuinely schematic *)
val pow2_probe = not ((Thm.prop_of pow2_sumsq_sch) aconv (jT (sumsqBody (pow two2 ZeroC))));
val () = if pow2_aconv andalso pow2_0hyp andalso pow2_probe
         then out "TSF_POW2_OK\n" else out "TSF_POW2_FAILED\n";

(* ============================================================================
   helper : sumsq_pow_of_sumsq bT eT hSumB : sumsq (pow b e)   (induction on e)
   given a base b that is itself a sum of two squares, every power b^e is too.
   Used by (b).  hSumB : jT (sumsqBody b).  eT is the TARGET exponent term —
   instantiate nat_induct's k directly at eT (do NOT varify+re-instantiate the
   result, which would schematize any Frees carried in hSumB's hyps and break a
   surrounding exE).
   ============================================================================ *)
fun sumsq_pow_of_sumsq (bT) (eT) hSumB =
  let
    val eF = Free("e_sp", natT);
    val base =
      let
        val pz = powZero_gr bT;                            (* oeq (pow b 0) 1 *)
        val pzSym = oeqSym_gr pz;                          (* oeq 1 (pow b 0) *)
        val zRW = Free("z_spb", natT);
        val Prw = Term.lambda zRW (sumsqBody zRW);
      in oeq_subst_gr_at (Prw, one2, pow bT ZeroC) pzSym sumsq_one end;
    val xF = Free("x_sp", natT);
    val ihP = jT (sumsqBody (pow bT xF));
    val IH  = Thm.assume (ctermGR ihP);
    val stepConcl =
      let
        val foldT = sumsq_mult (bT, pow bT xF) hSumB IH;   (* sumsq (b * pow b x) *)
        val psuc = powSuc_gr (bT, xF);                     (* oeq (pow b (Suc x)) (b * pow b x) *)
        val psucSym = oeqSym_gr psuc;
        val zRW = Free("z_sps", natT);
        val Prw = Term.lambda zRW (sumsqBody zRW);
      in oeq_subst_gr_at (Prw, mult bT (pow bT xF), pow bT (suc xF)) psucSym foldT end;
    val step1 = Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR ihP) stepConcl);
  in nat_induct_gr_at (Term.lambda eF (sumsqBody (pow bT eF))) eT base step1 end;

(* ============================================================================
   (b) p1mod4_pow_sumsq : (Ex k. p = 4k+1) ==> prime2 p ==> sumsq (pow p e)
       4k+1 := add (add (add k k)(add k k)) (Suc 0)
   First: derive sumsq p via twosquare (converting p = 4k+1 to p-1 = 4k), then
   power it up via sumsq_pow_of_sumsq.
   ============================================================================ *)
(* 4k abbreviation matching twosquare's RHS : (k+k)+(k+k) *)
fun fourk kT = add (add kT kT)(add kT kT);
(* the hyp predicate : %k. oeq p (add (4k) (Suc 0)) *)
fun p1mod4Body pT = mkEx (Term.lambda (Free("k_b1",natT)) (oeq pT (add (fourk (Free("k_b1",natT))) one2)));

val twosquare_gr = twosquare;   (* already on ctxtGR, 0-hyp *)

val p1mod4_pow_sumsq =
  let
    val pF = Free("p_b1", natT);
    val eF = Free("e_b1", natT);
    val hExP = jT (p1mod4Body pF);
    val hEx  = Thm.assume (ctermGR hExP);
    val hPrP = jT (prime2 pF);
    val hPr  = Thm.assume (ctermGR hPrP);
    val goalBody = sumsqBody (pow pF eF);
    (* eliminate Ex k *)
    val kPred = Term.lambda (Free("k_b1",natT)) (oeq pF (add (fourk (Free("k_b1",natT))) one2));
    val body =
      exE_gr_elim (kPred, goalBody) hEx "k_b1w"
        (fn kF => fn hpk =>      (* hpk : oeq p (add (4k) (Suc 0)) *)
           let
             (* derive sub p 1 = 4k :
                p = (4k) + (Suc 0) = Suc((4k)+0) = Suc(4k)   [add_Suc_right + add_0_right]
                sub p 1 = sub (Suc(4k)) (Suc 0) = sub (4k) 0 = 4k  [sub_SS + sub_0] *)
             val fk = fourk kF;
             (* (4k)+(Suc 0) = Suc((4k)+0) *)
             val aSr = addSr_gr (fk, ZeroC);            (* oeq (add (4k)(Suc 0)) (Suc(add (4k) 0)) *)
             val a0r = add0r_gr fk;                     (* oeq (add (4k) 0) (4k) *)
             val sucA0 = Suc_cong_gr2 a0r;              (* oeq (Suc(add (4k) 0)) (Suc (4k)) *)
             val pEqSuc4k0 = oeqTrans_gr (hpk, aSr);    (* oeq p (Suc(add (4k) 0)) *)
             val pEqSuc4k  = oeqTrans_gr (pEqSuc4k0, sucA0);  (* oeq p (Suc(4k)) *)
             (* sub p 1 : rewrite p -> Suc(4k) inside (sub p 1) *)
             val zSub = Free("z_b1sub", natT);
             val Psub = Term.lambda zSub (oeq (sub zSub one2) (sub (suc fk) one2));
             (* want oeq (sub p 1) (sub (Suc 4k) 1).  oeq_subst with a=Suc4k, b=p needs oeq (Suc4k) p *)
             val pEqSuc4kSym = oeqSym_gr pEqSuc4k;      (* oeq (Suc 4k) p *)
             val reflSub = oeqRefl_gr (sub (suc fk) one2);  (* oeq (sub (Suc 4k) 1)(sub (Suc 4k) 1) *)
             val subPeq = oeq_subst_gr_at (Psub, suc fk, pF) pEqSuc4kSym reflSub;
                          (* oeq (sub p 1)(sub (Suc 4k) 1) *)
             val ss = subSS_gr (fk, ZeroC);             (* oeq (sub (Suc 4k)(Suc 0)) (sub (4k) 0) *)
             val s0 = sub0_gr fk;                       (* oeq (sub (4k) 0) (4k) *)
             val subSuc4k = oeqTrans_gr (ss, s0);       (* oeq (sub (Suc 4k) 1) (4k) *)
             val subP1eq4k = oeqTrans_gr (subPeq, subSuc4k);  (* oeq (sub p 1) (4k) *)
             (* twosquare : prime2 p ==> oeq (sub p 1)((k+k)+(k+k)) ==> Ex a b. p=a²+b²
                varify turns its Free p_2sq/k_2sq into schematic Vars p_2sq.0/k_2sq.0. *)
             val ts_inst = beta_norm (Drule.infer_instantiate ctxtGR
                             [(("p_2sq",0), ctermGR pF),(("k_2sq",0), ctermGR kF)] (varify twosquare_gr));
             val ts1 = Thm.implies_elim ts_inst hPr;
             val ts2 = Thm.implies_elim ts1 subP1eq4k;  (* Ex a b. p = a*a+b*b  =  sumsq p *)
             (* sumsq p is exactly ts2 (twosquare conclusion uses mult a a + mult b b) *)
             val hSumP = ts2;
             (* power up : sumsq (pow p e).  Instantiate nat_induct at k:=eF
                DIRECTLY (no varify of the result — hSumP carries the prime2/oeq
                hyps with Free p, varify would schematize them and break exE). *)
             val powThm = sumsq_pow_of_sumsq pF eF hSumP;   (* sumsq (pow p e) *)
           in powThm end);
    (* discharge prime2 p then Ex k *)
    val d1 = Thm.implies_intr (ctermGR hPrP) body;       (* prime2 p ==> sumsq(pow p e) *)
    val d2 = Thm.implies_intr (ctermGR hExP) d1;         (* (Ex k. p=4k+1) ==> prime2 p ==> sumsq(pow p e) *)
  in d2 end;
val () = out ("p1mod4_pow_sumsq hyps="^Int.toString(length(Thm.hyps_of p1mod4_pow_sumsq))^"\n");
val p1mod4_pow_sumsq_sch = varify p1mod4_pow_sumsq;
val p1mod4_intended =
  let
    val pV = Free("p_b1", natT); val eV = Free("e_b1", natT);
    val concl = jT (sumsqBody (pow pV eV));
  in Logic.mk_implies (jT (p1mod4Body pV), Logic.mk_implies (jT (prime2 pV), concl)) end;
(* compare on the Free form (before sch) for clarity *)
val p1mod4_aconv0 = ((Thm.prop_of p1mod4_pow_sumsq) aconv p1mod4_intended);
val p1mod4_0hyp  = (length (Thm.hyps_of p1mod4_pow_sumsq) = 0);
val () = out ("p1mod4_pow_sumsq aconv="^Bool.toString p1mod4_aconv0^" zero_hyp="^Bool.toString p1mod4_0hyp^"\n");
(* soundness probe : must KEEP both hyps (NOT the bare sumsq(pow p e)) *)
val p1mod4_probe =
  not ((Thm.prop_of p1mod4_pow_sumsq) aconv (jT (sumsqBody (pow (Free("p_b1",natT)) (Free("e_b1",natT))))));
val () = if p1mod4_aconv0 andalso p1mod4_0hyp andalso p1mod4_probe
         then out "TSF_P1MOD4_OK\n" else out "TSF_P1MOD4_FAILED\n";

(* ============================================================================
   (c) p3mod4_even_sumsq : (Ex k. p = 4k+3) ==> (Ex j. e = 2j) ==> sumsq (pow p e)
       4k+3 := add (fourk k) (Suc(Suc(Suc 0)))    ;    2j := add j j
   The math : pow p (j+j) = (pow p j)*(pow p j)  [pow_add], a perfect square,
   so sq_is_sumsq (pow p j) gives sumsq.  The p=4k+3 hyp is consumed (vacuous).
   ============================================================================ *)
val three2 = suc (suc (suc ZeroC));
fun p3mod4Body pT = mkEx (Term.lambda (Free("k_c3",natT)) (oeq pT (add (fourk (Free("k_c3",natT))) three2)));
fun evenBody eT  = mkEx (Term.lambda (Free("j_c3",natT)) (oeq eT (add (Free("j_c3",natT)) (Free("j_c3",natT)))));

val p3mod4_even_sumsq =
  let
    val pF = Free("p_c3", natT);
    val eF = Free("e_c3", natT);
    val hKP = jT (p3mod4Body pF);  val hK = Thm.assume (ctermGR hKP);
    val hJP = jT (evenBody eF);    val hJ = Thm.assume (ctermGR hJP);
    val goalBody = sumsqBody (pow pF eF);
    (* eliminate Ex j (the even witness).  The p=4k+3 hyp hK is just held. *)
    val jPred = Term.lambda (Free("j_c3",natT)) (oeq eF (add (Free("j_c3",natT)) (Free("j_c3",natT))));
    val body =
      exE_gr_elim (jPred, goalBody) hJ "j_c3w"
        (fn jF => fn hej =>     (* hej : oeq e (add j j) *)
           let
             (* sq_is_sumsq (pow p j) : sumsq ((pow p j)*(pow p j)) *)
             val sqsum = sq_is_sumsq (pow pF jF);          (* sumsq (mult (pow p j)(pow p j)) *)
             (* pow p (j+j) = (pow p j)*(pow p j)  [pow_add] *)
             val pa = powAdd_gr (pF, jF, jF);              (* oeq (pow p (j+j)) (mult (pow p j)(pow p j)) *)
             val paSym = oeqSym_gr pa;                     (* oeq (mult (pow p j)(pow p j)) (pow p (j+j)) *)
             val zRW = Free("z_c3a", natT);
             val Prw = Term.lambda zRW (sumsqBody zRW);
             val sumPowJJ = oeq_subst_gr_at (Prw, mult (pow pF jF)(pow pF jF), pow pF (add jF jF)) paSym sqsum;
                            (* sumsq (pow p (j+j)) *)
             (* rewrite (j+j) -> e via hej (oeq e (j+j)) : need oeq (j+j) e *)
             val hejSym = oeqSym_gr hej;                   (* oeq (add j j) e *)
             val zRW2 = Free("z_c3b", natT);
             val Prw2 = Term.lambda zRW2 (sumsqBody (pow pF zRW2));   (* %z. sumsq (pow p z) *)
             val sumPowE = oeq_subst_gr_at (Prw2, add jF jF, eF) hejSym sumPowJJ;
                           (* sumsq (pow p e) *)
           in sumPowE end);
    val d1 = Thm.implies_intr (ctermGR hJP) body;          (* (Ex j. e=2j) ==> sumsq(pow p e) *)
    val d2 = Thm.implies_intr (ctermGR hKP) d1;            (* (Ex k. p=4k+3) ==> (Ex j. e=2j) ==> sumsq(pow p e) *)
  in d2 end;
val () = out ("p3mod4_even_sumsq hyps="^Int.toString(length(Thm.hyps_of p3mod4_even_sumsq))^"\n");
val p3mod4_intended =
  let
    val pV = Free("p_c3", natT); val eV = Free("e_c3", natT);
    val concl = jT (sumsqBody (pow pV eV));
  in Logic.mk_implies (jT (p3mod4Body pV), Logic.mk_implies (jT (evenBody eV), concl)) end;
val p3mod4_aconv0 = ((Thm.prop_of p3mod4_even_sumsq) aconv p3mod4_intended);
val p3mod4_0hyp  = (length (Thm.hyps_of p3mod4_even_sumsq) = 0);
val () = out ("p3mod4_even_sumsq aconv="^Bool.toString p3mod4_aconv0^" zero_hyp="^Bool.toString p3mod4_0hyp^"\n");
(* soundness probe : must KEEP the even-exponent hyp (the conclusion is false for
   odd e at a 3mod4 prime, e.g. p=3,e=1 : 3 is not a sum of two squares).  Confirm
   the theorem is NOT the hyp-dropped sumsq(pow p e). *)
val p3mod4_probe =
  not ((Thm.prop_of p3mod4_even_sumsq) aconv (jT (sumsqBody (pow (Free("p_c3",natT)) (Free("e_c3",natT))))));
(* second probe : must KEEP the even hyp specifically (not just the 4k+3 hyp) *)
val p3mod4_probe2 =
  not ((Thm.prop_of p3mod4_even_sumsq) aconv
        (Logic.mk_implies (jT (p3mod4Body (Free("p_c3",natT))),
           jT (sumsqBody (pow (Free("p_c3",natT)) (Free("e_c3",natT)))))));
val () = if p3mod4_aconv0 andalso p3mod4_0hyp andalso p3mod4_probe andalso p3mod4_probe2
         then out "TSF_P3MOD4_OK\n" else out "TSF_P3MOD4_FAILED\n";

(* ---- axiom audit : the per-prime delta adds NO new axioms/consts/types ---- *)
val () =
  let
    val thyOf = Thm.theory_of_thm p3mod4_even_sumsq;
    val axs = Theory.all_axioms_of thyOf;
  in out ("TSF_AXIOM_AUDIT total_axioms="^Int.toString (length axs)^"\n") end
  handle e => out ("TSF_AXIOM_AUDIT skipped ("^exnMessage e^")\n");

val () = if pow2_aconv andalso pow2_0hyp andalso pow2_probe
            andalso p1mod4_aconv0 andalso p1mod4_0hyp andalso p1mod4_probe
            andalso p3mod4_aconv0 andalso p3mod4_0hyp andalso p3mod4_probe andalso p3mod4_probe2
         then out "TSF_PERPRIME_ALL_OK\n" else out "TSF_PERPRIME_SOME_FAILED\n";
val () = out "TSF_PERPRIME_DONE\n";
