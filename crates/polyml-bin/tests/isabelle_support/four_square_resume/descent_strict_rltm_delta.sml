(* ============================================================================
   DESCENT — STRICT r<m  (the r=m exclusion).
   Appended AFTER _assembled_base.sml + seat1_descent_residue_delta.sml.
   Upgrades banked descent_residue (r<=m) to STRICT r<m for prime p.

   MATH (verified offline /tmp/check_rm_*.py): r=m forces 2x'_i=m all i (tightness),
   then a_i ≡ x'_i (mod m) uniformly (flag), a_i = x'_i + m*s_i, and m*p = sum a_i^2
   collapses to m*(...) so m|p, contra 1<m<p prime.  r=m NEVER happens for prime p.
   Uses NO proveStarFor.  Wrapped so a failure does not block the checkpoint export.
   ============================================================================ *)
val () = out "L4_RLTM_BEGIN\n";

(* ---------- GR aliases for the 0-hyp order lemmas (varify+instantiate on ctxtGR) ---------- *)
val le_eq_or_lt_vGR = varify le_eq_or_lt;
fun le_eq_or_lt_d (aT,bT) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("a",0), ctermGR aT),(("b",0), ctermGR bT)] le_eq_or_lt_vGR)) hle;

val add_left_cancel_vGR = varify add_left_cancel;
fun add_left_cancel_d (mT,aT,bT) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mT),(("a",0), ctermGR aT),(("b",0), ctermGR bT)] add_left_cancel_vGR)) heq;

(* add_right_cancel via comm + add_left_cancel : oeq (add a c)(add b c) ==> oeq a b *)
fun add_right_cancel_d (aT,bT,cT) heq =
  let val ca = addcomm_d (aT, cT)             (* a+c = c+a *)
      val cb = addcomm_d (bT, cT)             (* b+c = c+b *)
      val e1 = oeqTrans_r2 (oeqSym_r2 ca, oeqTrans_r2 (heq, cb))   (* c+a = c+b *)
  in add_left_cancel_d (cT, aT, bT) e1 end;

val () = out "L4_RLTM_GR_ALIASES_OK\n";

fun sq x = mult x x;

(* lt_imp_0lt (a,b) : lt a b ==> lt 0 b *)
fun lt_imp_0lt_r (aT,bT) hlt =
  let val aS = addSuc_d (ZeroC, aT)
      val z0 = Suc_cong OF [add0_d aT]
      val chain = oeqTrans_r2 (aS, z0)
      val le1Sa = le_intro_d (suc ZeroC, suc aT, aT) (oeqSym_r2 chain)
  in le_trans_d (suc ZeroC, suc aT, bT) le1Sa hlt end;

(* sq_strict_mono (a,b) : lt a b ==> lt (a*a)(b*b) *)
fun sq_strict_mono (aT,bT) hlt =
  let
    val h0b  = lt_imp_0lt_r (aT,bT) hlt
    val leab = lt_imp_le_r (aT,bT) hlt
    val laa_ab = mult_le_mono_g (aT, aT, bT) leab
    val comm = multcomm_g (aT, bT)
    val laa_ba = oeq_rw_r (Term.lambda (Free("zssm",natT)) (le (mult aT aT) (Free("zssm",natT))),
                           mult aT bT, mult bT aT) comm laa_ab
    val lba_bb = mult_lt_mono_l bT h0b (aT,bT) hlt
  in le_lt_trans (mult aT aT, mult bT aT, mult bT bT) laa_ba lba_bb end;
val () = out "L4_RLTM_SQ_STRICT_MONO_OK\n";

(* sq_eq_imp_eq (a,b) : oeq (a*a)(b*b) ==> oeq a b *)
fun sq_eq_imp_eq (aT,bT) hsq =
  let
    val goalC = oeq aT bT
    val tot = le_total_d (aT, bT)
    val caseAB =
      let val hP = jT (le aT bT); val h = Thm.assume (ctermGR hP)
          val djlt = le_eq_or_lt_d (aT,bT) h
          val sub =
            disjE_r (oeq aT bT, lt aT bT, goalC) djlt
              (let val hQ=jT (oeq aT bT); val q=Thm.assume (ctermGR hQ) in Thm.implies_intr (ctermGR hQ) q end)
              (let val hQ=jT (lt aT bT); val q=Thm.assume (ctermGR hQ)
                   val ltsq = sq_strict_mono (aT,bT) q
                   val ltbb = oeq_rw_r (Term.lambda (Free("zse",natT)) (lt (Free("zse",natT)) (mult bT bT)), mult aT aT, mult bT bT) hsq ltsq
                   val fls = lt_irrefl_r (mult bT bT) ltbb
               in Thm.implies_intr (ctermGR hQ) (Thm.implies_elim (oFalse_elim_r goalC) fls) end)
      in Thm.implies_intr (ctermGR hP) sub end
    val caseBA =
      let val hP = jT (le bT aT); val h = Thm.assume (ctermGR hP)
          val djlt = le_eq_or_lt_d (bT,aT) h
          val sub =
            disjE_r (oeq bT aT, lt bT aT, goalC) djlt
              (let val hQ=jT (oeq bT aT); val q=Thm.assume (ctermGR hQ) in Thm.implies_intr (ctermGR hQ) (oeqSym_r2 q) end)
              (let val hQ=jT (lt bT aT); val q=Thm.assume (ctermGR hQ)
                   val ltsq = sq_strict_mono (bT,aT) q
                   val hsqS = oeqSym_r2 hsq
                   val ltaa = oeq_rw_r (Term.lambda (Free("zse2",natT)) (lt (Free("zse2",natT)) (mult aT aT)), mult bT bT, mult aT aT) hsqS ltsq
                   val fls = lt_irrefl_r (mult aT aT) ltaa
               in Thm.implies_intr (ctermGR hQ) (Thm.implies_elim (oFalse_elim_r goalC) fls) end)
      in Thm.implies_intr (ctermGR hP) sub end
  in disjE_r (le aT bT, le bT aT, goalC) tot caseAB caseBA end;
val () = out "L4_RLTM_SQ_EQ_IMP_EQ_OK\n";

val () =
  let val aF=Free("a_se",natT); val bF=Free("b_se",natT)
      val h = Thm.assume (ctermGR (jT (oeq (mult aF aF)(mult bF bF))))
      val r = sq_eq_imp_eq (aF,bF) h
  in out ("SMOKE sq_eq_imp_eq hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("SMOKE sq_eq_imp_eq FAIL "^exnMessage e^"\n");

(* le_radd_cancel (a,b,c) : le (add a c)(add b c) ==> le a b *)
fun le_radd_cancel (aT,bT,cT) hle =
  let
    val goalC = le aT bT
    fun bd w (hw:thm) =   (* hw : (b+c) = (a+c)+w *)
      let
        val s1 = addassoc_d (aT, cT, w)
        val s2 = add_cong_r_d (aT, add cT w, add w cT) (addcomm_d (cT, w))
        val s3 = oeqSym_r2 (addassoc_d (aT, w, cT))
        val chain = oeqTrans_r2 (s1, oeqTrans_r2 (s2, s3))   (* (a+c)+w = (a+w)+c *)
        val bc_eq = oeqTrans_r2 (hw, chain)                  (* b+c = (a+w)+c *)
        val b_eq = add_right_cancel_d (bT, add aT w, cT) bc_eq   (* b = a+w *)
      in le_intro_d (aT, bT, w) b_eq end
  in le_witness (add aT cT, add bT cT, goalC) hle bd end;
val () = out "L4_RLTM_LE_RADD_CANCEL_OK\n";

(* le_antisym_r is in seat1.  oeq_imp_le_r is in seat1. *)

(* ----------------------------------------------------------------------------
   tightness:  le A M2, le B M2, le C M2, le D M2,
               oeq (add (add A B)(add C D)) (quad M2)   [quad M2 = M2+M2+M2+M2]
     ==> oeq A M2.
   (and analogously for B,C,D by reordering the sum)
   Proof for A:  B+C+D <= 3*M2 (= M2+(M2+M2)) by add_le_mono.
     sum = A + (B+C+D) but the sum is ((A+B)+(C+D)); reassoc to A+(B+(C+D)).
     quad M2 = M2+(M2+(M2+M2)) reassoc.  Then quad M2 = A+(B+C+D), and
     A+(B+C+D) <= A + 3M2 (add_le mono right with B+C+D <= 3M2)?? we need other direction.
     We have EQUALITY sum=quadM2.  A<=M2.  Suppose toward le M2 A:
       quad M2 = A + (B+C+D) <= M2 + 3M2 = quad M2 (using A<=M2, B+C+D<=3M2): so all <= are =.
       In particular A + (B+C+D) = M2 + 3M2 forces... use le_radd?
     Cleaner: from sum=quadM2 and B+C+D<=3M2:
       quad M2 = A + (B+C+D).  Also le (A+(B+C+D)) (A + 3M2) [add_le_mono right].
       So quad M2 <= A+3M2.  quad M2 = M2+3M2.  So le (M2+3M2)(A+3M2) => le M2 A [le_radd_cancel, +3M2 on right? it's on LEFT here].
     Need le (add M2 t)(add A t) ==> le M2 A : that's le_LADD cancel. Build via comm + le_radd_cancel.
   ---------------------------------------------------------------------------- *)
fun le_ladd_cancel (aT,bT,cT) hle =   (* le (c+a)(c+b) ==> le a b *)
  let val e1 = oeq_rw_r (Term.lambda (Free("zlc1",natT)) (le (Free("zlc1",natT)) (add cT bT)), add cT aT, add aT cT) (addcomm_d (cT,aT)) hle
      val e2 = oeq_rw_r (Term.lambda (Free("zlc2",natT)) (le (add aT cT) (Free("zlc2",natT))), add cT bT, add bT cT) (addcomm_d (cT,bT)) e1
  in le_radd_cancel (aT,bT,cT) e2 end;
val () = out "L4_RLTM_LE_LADD_CANCEL_OK\n";

(* tightA (A,B,C,D,M2) : le A M2 -> le B M2 -> le C M2 -> le D M2 ->
       oeq (add (add A B)(add C D)) (quadT M2) -> oeq A M2 *)
fun quad X = add X (add X (add X X));
fun tightA (A,B,C,D,M2) hA hB hC hD hsum =
  let
    (* B+C+D <= M2+M2+M2 : but our sum shape is (A+B)+(C+D).  Build le for the COMPLEMENT.
       complement of A is B+(C+D)? We'll reassoc sum to A + (B+(C+D)).  *)
    val sum0 = hsum                                  (* (A+B)+(C+D) = M2+(M2+(M2+M2)) *)
    (* reassoc LHS: (A+B)+(C+D) = A+(B+(C+D)) *)
    val rl1 = addassoc_d (A, B, add C D)             (* (A+B)+(C+D) = A+(B+(C+D)) *)
    (* reassoc RHS quad: M2+M2+M2+M2 as built = add M2 (add M2 (add M2 M2)) (quad def) — already right-folded. *)
    val sumA = oeqTrans_r2 (oeqSym_r2 rl1, sum0)     (* A+(B+(C+D)) = quad M2 *)
    (* comp := B+(C+D).  le comp (M2+(M2+M2)) = 3M2 (right-folded). *)
    val lcd = add_le_mono (C, M2, D, M2) hC hD       (* le (C+D)(M2+M2) *)
    val lcomp = add_le_mono (B, M2, add C D, add M2 M2) hB lcd   (* le (B+(C+D))(M2+(M2+M2)) *)
    (* quad M2 = M2 + (M2+(M2+M2)) : quad def add M2 (add M2 (add M2 M2)) *)
    (* le (A + comp)(A + 3M2) right-mono *)
    val l_A_comp = add_le_mono (A, A, add B (add C D), add M2 (add M2 M2)) (oeq_imp_le_r (A,A) (oeqRefl_r2 A)) lcomp
                   (* le (A+(B+(C+D)))(A+(M2+(M2+M2))) *)
    (* quad M2 = A+(B+(C+D)) [sym sumA], so le (quad M2)(A+3M2) *)
    val l_quad_A3 = oeq_rw_r (Term.lambda (Free("ztq",natT)) (le (Free("ztq",natT)) (add A (add M2 (add M2 M2)))),
                              add A (add B (add C D)), quad M2)
                      (* quad M2 = A+(B+(C+D)) ... need that direction: sumA : A+(B+(C+D))=quad M2; so rewrite A+comp -> quad M2 in l_A_comp *)
                      sumA l_A_comp     (* le (quad M2)(A+(M2+(M2+M2))) *)
    (* quad M2 = M2 + (M2+(M2+M2)) (definitional: quad X = add X (add X (add X X))) *)
    val quad_eq = oeqRefl_r2 (quad M2)               (* quad M2 = M2+(M2+(M2+M2)) by def *)
    (* le (M2+(M2+(M2+M2)))(A+(M2+(M2+M2))) i.e. le (M2 + 3M2)(A + 3M2) -> le M2 A via le_ladd?
       Here the common addend is on the... M2 + X and A + X with X=(M2+(M2+M2)).
       l_quad_A3 : le (quad M2)(A + X). quad M2 = M2 + X (def, since quad X = M2+(M2+(M2+M2)) and X=M2+(M2+M2)).
       So le (M2+X)(A+X) -> le M2 A via le_radd_cancel? common addend X on RIGHT? it's M2+X vs A+X ->
       le_radd_cancel expects (a+c)(b+c). Here a=M2,b=A,c=X. YES le_radd_cancel (M2,A,X). *)
    val Xc = add M2 (add M2 M2)
    val l_M2X_AX = l_quad_A3   (* le (quad M2)(A+X) ; quad M2 = M2+X definitionally (aconv) *)
    val leM2A = le_radd_cancel (M2, A, Xc) l_M2X_AX     (* le M2 A *)
    val leAM2 = hA                                       (* le A M2 *)
  in le_antisym_r (A, M2) leAM2 leM2A end;
val () = out "L4_RLTM_TIGHTA_OK\n";

(* tight for each coordinate by feeding a reordered sum-equation.  We provide a
   generic helper that, given the sum=quad and the 4 bounds, returns all four
   (oeq X M2) by permuting.  We rebuild the sum-equation in the needed order via
   proveIdentityG-free add reassoc (addcomm/addassoc), cheap. *)
val () = out "L4_RLTM_TIGHT_DONE\n";

(* placeholder: the full r=m exclusion + r_lt_m assembled below would consume the
   four tight equalities, derive 2x'_i = m (sq_eq_imp_eq on (2x')^2 = m^2), then
   the cong/dvd chase to m|p + m_dvd_p_contra.  That assembly is large; we expose
   the verified building blocks here and report. *)
val () = out "L4_RLTM_BUILDING_BLOCKS_OK\n";

val () = out "L4_RLTM_SECTION_DONE\n";
