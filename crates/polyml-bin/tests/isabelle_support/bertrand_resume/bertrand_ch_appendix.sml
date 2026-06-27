(* ============================================================================
   BERTRAND CH — the SMALL-N CHAIN, extended to cover n < 631 (>= the 516 cutoff).
   APPENDIX to bertrand_f7_full.sml.  Final base context: ctxtV4/ctermV4/thyV4.

   The f7 base already proves bertrand_small : lt 0 n ==> lt n 83 ==> Ex prime
   (chain {2,3,5,7,13,23,43,83}).  Here we EXTEND the chain with the primes
   163, 317, 631 (each < 2x the previous : 83<163<2*83=166 ; 163<317<2*163=326 ;
   317<631<2*317=634) so that the Bertrand witness cascade covers every n with
   lt n 631, i.e. n in [1,630] ⊇ [1,515].  This is the (CH) stage : for n < 516
   (< 631) a prime in (n,2n] is exhibited by the chain.

   The three new prime2 facts are PROVED via prime2_via_check (sqrt-bounded
   primality check, O(sqrt p) cascade) — NOTHING asserted as an axiom.
   Proofterm.proofs := 0 bounds RAM; the kernel still type-checks every inference.

   Soundness : bertrand_chain (the new small-n theorem) must be 0-hyp + aconv the
   intended term (prime2 structural, prime strictly > n and <= 2n) ; only ex_middle
   classical ; NO smuggled prime-existence / Bertrand-shaped axiom.
   ============================================================================ *)
val () = (Proofterm.proofs := 0);
val () = out "CH_APPENDIX_BEGIN\n";

(* ---- prove the three new chain primes via the sqrt-bounded check ---- *)
val () = out "CH: proving prime2 163 ...\n";
val p163 = prime2_via_check 163;
val () = out ("CH prime2 163 0hyp=" ^ Bool.toString (zhV4 p163) ^ "\n");
val () = out "CH: proving prime2 317 ...\n";
val p317 = prime2_via_check 317;
val () = out ("CH prime2 317 0hyp=" ^ Bool.toString (zhV4 p317) ^ "\n");
val () = out "CH: proving prime2 631 ...\n";
val p631 = prime2_via_check 631;
val () = out ("CH prime2 631 0hyp=" ^ Bool.toString (zhV4 p631) ^ "\n");

(* aconv-gate the three new prime facts against jT (prime2 (mkNum p)) *)
fun prime2_ok (pi, th) =
  zhV4 th andalso ((Thm.prop_of th) aconv (jT (prime2 (mkNum pi))));
val ch_primes_ok = prime2_ok (163,p163) andalso prime2_ok (317,p317) andalso prime2_ok (631,p631);
val () = out ("CH new-prime aconv all=" ^ Bool.toString ch_primes_ok ^ "\n");
val () = if ch_primes_ok then out "CH_NEW_PRIMES_OK\n" else out "CH_NEW_PRIMES_FAIL\n";

(* ---- the EXTENDED chain prime table (re-use the f7 chain + the 3 new) ---- *)
val chainThmsBig =
  chainThms
  @ [(163, p163), (317, p317), (631, p631)];
fun primeThmOfBig pi =
  case List.find (fn (q,_) => q = pi) chainThmsBig of
    SOME (_, th) => th
  | NONE => raise Fail ("primeThmOfBig: no chain prime " ^ Int.toString pi);

(* mkBertWitness specialized to the big table (same body as f7's mkBertWitness but
   over chainThmsBig so 163/317/631 are reachable). *)
fun mkBertWitnessBig nF pi hLtnpk hLe2 =
  let val pkT = mkNum pi
      val twoN = add nF nF
      val hPrime = primeThmOfBig pi
      val inner = conjI_4 (lt nF pkT, le pkT twoN) hLtnpk hLe2
      val full  = conjI_4 (prime2 pkT, mkConj (lt nF pkT)(le pkT twoN)) hPrime inner
  in exI_4 (bertBodyAbs nF, pkT) full end;

(* ============================================================================
   bertrand_chain : lt 0 n ==> lt n 631 ==> Ex (bertBodyAbs n).
   Same cascade structure as f7's bertrand_small, but:
     - intervals extended with (83,163),(163,317),(317,631)
     - the terminal bound is 631 (n83 -> n631)
     - witnesses drawn from the big prime table
   Coverage : interval [lo,pk) witnessed by pk ; pk <= 2*lo guarantees le pk (2n).
     2:[1] 3:[2] 5:[3,4] 7:[5,6] 13:[7,12] 23:[13,22] 43:[23,42] 83:[43,82]
     163:[83,162] 317:[163,316] 631:[317,630].
   ============================================================================ *)
val () = out "CH_THEOREM_BEGIN\n";

val bertrand_chain =
  let
    val nF = Free("n_chn", natT)
    val oneN = suc ZeroC
    val n631 = mkNum 631
    val hn0  = Thm.assume (ctermV4 (jT (lt ZeroC nF)))    (* lt 0 n = le 1 n *)
    val hltN = Thm.assume (ctermV4 (jT (lt nF n631)))     (* lt n 631 = le (Suc n) 631 *)
    val goalEx = mkEx (bertBodyAbs nF)
    (* (lo,pk) intervals : lo is the previous lower bound s.t. pk <= 2*lo. *)
    val intervals = [(1,2),(2,3),(3,5),(5,7),(7,13),(13,23),(23,43),(43,83),
                     (83,163),(163,317),(317,631)];
    fun cascade ivs loCur hLoN =
      case ivs of
        [] =>
          (* exhausted : le 631 n (hLoN) with hltN : le (Suc n) 631 -> le (Suc n) n -> lt_irrefl *)
          let val le631n = hLoN
          in oFalse_elim_4 goalEx OF [ (lt_irrefl4_at nF) OF [ le_trans4_at (suc nF, n631, nF) hltN le631n ] ] end
      | (lo,pk)::rest =>
          let
            val pkT = mkNum pk
            val djt = le_total_4 (pkT, nF)    (* Disj (le pk n)(le n pk) *)
            val caseGE =   (* le pk n : recurse with lower bound pk *)
              let val hpkn = Thm.assume (ctermV4 (jT (le pkT nF)))
                  val g = cascade rest pk hpkn
              in Thm.implies_intr (ctermV4 (jT (le pkT nF))) g end
            val caseLT =   (* le n pk : n <= pk ; split n=pk vs n<pk *)
              let val hnpk = Thm.assume (ctermV4 (jT (le nF pkT)))
                  val dje = le_eq_or_succ_le_4 (nF, pkT) hnpk   (* Disj (oeq n pk)(le (Suc n) pk) *)
                  val caseEqNpk =
                    let val heq = Thm.assume (ctermV4 (jT (oeq nF pkT)))   (* n = pk *)
                        val g =
                          case rest of
                            ((lo2,pk2)::_) =>
                              (* witness pk2 : lt n pk2 (n=pk<pk2) ; le pk2 (2n) (pk2<=2*pk=2*n). *)
                              let val pk2T = mkNum pk2
                                  val lt_pk_pk2 = lt_eval pk pk2     (* le (Suc pk) pk2 *)
                                  val hpkn = oeq_sym OF [heq]        (* oeq pk n *)
                                  val lt_n_pk2 = le_cong_l4 (suc pkT, suc nF, pk2T) (Suc_cong OF [hpkn]) lt_pk_pk2
                                  val le_pk2_2pk = le_eval pk2 (pk+pk)
                                  val (sumT, sumEq) = add_eval pkT pkT
                                  val ann_app = oeq_trans OF [ add_cong_l4 (nF, pkT, nF) heq,
                                                               add_cong_r4 (pkT, nF, pkT) heq ]
                                  val le_pk2_addpp = le_cong_r4 (pk2T, mkNum (pk+pk), add pkT pkT) (oeq_sym OF [sumEq]) le_pk2_2pk
                                  val le_pk2_2n = le_cong_r4 (pk2T, add pkT pkT, add nF nF) (oeq_sym OF [ann_app]) le_pk2_addpp
                                  val hPrime2 = primeThmOfBig pk2
                                  val inner = conjI_4 (lt nF pk2T, le pk2T (add nF nF)) lt_n_pk2 le_pk2_2n
                                  val fullc = conjI_4 (prime2 pk2T, mkConj (lt nF pk2T)(le pk2T (add nF nF))) hPrime2 inner
                              in exI_4 (bertBodyAbs nF, pk2T) fullc end
                          | [] =>
                              (* n = 631 : but hltN lt n 631 -> le (Suc 631) 631 contra *)
                              let val leSn631 = le_cong_l4 (suc nF, suc pkT, n631) (Suc_cong OF [heq]) hltN
                                  val ff = (lt_irrefl4_at n631) OF [leSn631]
                              in oFalse_elim_4 goalEx OF [ff] end
                    in Thm.implies_intr (ctermV4 (jT (oeq nF pkT))) g end
                  val caseLtNpk =
                    let val hlt = Thm.assume (ctermV4 (jT (le (suc nF) pkT)))   (* lt n pk *)
                        val hLe2 = mkLe2 nF loCur pk hLoN     (* le pk (2n) — uses f7's mkLe2 *)
                        val g = mkBertWitnessBig nF pk hlt hLe2
                    in Thm.implies_intr (ctermV4 (jT (le (suc nF) pkT))) g end
                  val g = disjE_4 (oeq nF pkT, le (suc nF) pkT, goalEx) dje caseEqNpk caseLtNpk
              in Thm.implies_intr (ctermV4 (jT (le nF pkT))) g end
            val g = disjE_4 (le pkT nF, le nF pkT, goalEx) djt caseGE caseLT
          in g end
    val concl = cascade intervals 1 hn0
    val d2 = Thm.implies_intr (ctermV4 (jT (lt nF n631))) concl
    val d1 = Thm.implies_intr (ctermV4 (jT (lt ZeroC nF))) d2
  in varify d1 end;

val () = out ("bertrand_chain 0hyp=" ^ Bool.toString (zhV4 bertrand_chain) ^ "\n");
val () = out ("bertrand_chain : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of bertrand_chain) ^ "\n");
val i_bertrand_chain =
  let val nVz = Var(("n_chn",0),natT)
      val bb = Term.lambda (Free("p_bw",natT))
        (mkConj (prime2 (Free("p_bw",natT)))
                (mkConj (lt nVz (Free("p_bw",natT)))(le (Free("p_bw",natT))(add nVz nVz))))
  in Logic.mk_implies (jT (lt ZeroC nVz),
       Logic.mk_implies (jT (lt nVz (mkNum 631)),
         jT (mkEx bb))) end;
val r_bc = (Thm.prop_of bertrand_chain) aconv i_bertrand_chain;
val () = out ("bertrand_chain aconv=" ^ Bool.toString r_bc ^ "\n");
val bertrand_chain_ok = zhV4 bertrand_chain andalso r_bc andalso ch_primes_ok;
val () = if bertrand_chain_ok then out "SMALL_N_OK\n" else out "SMALL_N_PARTIAL\n";

(* soundness probe : the cascade must NOT prove the weakened le p n form *)
val s_bc_range =
  let val nVz = Var(("n_chn",0),natT)
      val bbW = Term.lambda (Free("p_bw",natT))
        (mkConj (prime2 (Free("p_bw",natT)))
                (mkConj (lt nVz (Free("p_bw",natT)))(le (Free("p_bw",natT)) nVz)))
  in not ((Thm.prop_of bertrand_chain) aconv
            (Logic.mk_implies (jT (lt ZeroC nVz),
               Logic.mk_implies (jT (lt nVz (mkNum 631)), jT (mkEx bbW))))) end;
val () = if s_bc_range then out "CH_RANGE_PROBE_OK (not the weakened le p n form)\n"
         else out "CH_RANGE_PROBE_FAIL\n";

(* axiom audit : only ex_middle classical, no smuggled prime/bertrand axiom *)
val () =
  let val thy = Proof_Context.theory_of ctxtV4
      val names = map fst (Theory.all_axioms_of thy)
      val classical = List.filter (fn s => String.isSubstring "ex_middle" s
                                   orelse String.isSubstring "excluded" s) names
      val suspicious = List.filter (fn s =>
         String.isSubstring "163" s orelse String.isSubstring "317" s
         orelse String.isSubstring "631" s orelse String.isSubstring "chain" s
         orelse String.isSubstring "bertrand" s orelse String.isSubstring "prime_exist" s) names
  in (out ("CH_AXIOM_AUDIT total=" ^ Int.toString (length names)
          ^ " classical=" ^ Int.toString (length classical)
          ^ " suspicious=" ^ Int.toString (length suspicious) ^ "\n");
      app (fn s => out ("  CH SUSPICIOUS: " ^ s ^ "\n")) suspicious)
  end;

val () = out "CH_APPENDIX_DONE\n";
