(* ============================================================================
   QR PARITY — building blocks on ctxtW.
   Goal scope: the per-pair congruence (the named CRUX brick), plus the
   balance->cong helper it rests on.
   ============================================================================ *)
val () = out "QR_PAIR_BEGIN\n";

(* oneN already bound by isabelle_wilson.sml; rebind harmlessly. *)
val oneN = suc ZeroC;

(* ---- missing _W wrappers (vars already varified onto ctxtW) ---- *)
fun leftdistrib_W (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW xt),(("m",0), ctermW mt),(("n",0), ctermW nt)] left_distrib_vW);
fun add_left_cancel_W (mt,at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("a",0), ctermW at),(("b",0), ctermW bt)] add_left_cancel_vW)) heq;

(* ---- cong_from_balance : oeq (add X (mult p s)) (add Y (mult p t)) ==> cong p X Y ----
   By le_total on (s,t).  If s<=t (t=s+d): X + p*s = Y + p*(s+d) = Y + p*s + p*d,
   cancel p*s (add_left_cancel via comm) => X = Y + p*d  => congR... wait, that's
   X = Y + p*d => cong p X Y via congR (a=X,b=Y: a = b + m*k). Good.
   If t<=s (s=t+d): Y + p*t = X + p*(t+d) => Y = X + p*d => congL (b=Y = a+m*k, a=X). *)
fun cong_from_balance (pT, X, Y, sT, tT) hbal =
  let
    val tot = le_total_W (sT, tT)
    val caseLe =
      let val hle = Thm.assume (ctermW (jT (le sT tT)))
          val Pd = Abs("d", natT, oeq tT (add sT (Bound 0)))
          fun body d (hd:thm) =
            let
              (* hbal : X + p*s = Y + p*t ; t = s + d *)
              val ct = mult_cong_r_W (pT, tT, add sT d) hd          (* p*t = p*(s+d) *)
              val cY = add_cong_r_W (Y, mult pT tT, mult pT (add sT d)) ct
              val rhs1 = oeq_trans_vW OF [hbal, cY]                 (* X+p*s = Y + p*(s+d) *)
              val ld = leftdistrib_W (pT, sT, d)                    (* p*(s+d) = p*s + p*d *)
              val cY2 = add_cong_r_W (Y, mult pT (add sT d), add (mult pT sT) (mult pT d)) ld
              val rhs2 = oeq_trans_vW OF [rhs1, cY2]                (* X+p*s = Y + (p*s + p*d) *)
              val assoc = addassoc_W (Y, mult pT sT, mult pT d)     (* (Y+p*s)+p*d = Y+(p*s+p*d) *)
              val assoc_s = oeq_sym_vW OF [assoc]
              val rhs3 = oeq_trans_vW OF [rhs2, assoc_s]            (* X+p*s = (Y+p*s)+p*d *)
              (* X+p*s = (Y+p*d)+p*s : commute the inner *)
              val comm = addcomm_W (Y, mult pT sT)                  (* Y+p*s = p*s+Y *)
              (* rewrite (Y+p*s) -> need X + p*s = ((Y) + p*d) + p*s. group: (Y+p*s)+p*d  *)
              (* reassociate (Y+p*s)+p*d = (p*s+Y)+p*d ... *)
              val cInner = add_cong_l_W (add Y (mult pT sT), add (mult pT sT) Y, mult pT d) comm
              val rhs4 = oeq_trans_vW OF [rhs3, cInner]             (* X+p*s = (p*s+Y)+p*d *)
              val a2 = addassoc_W (mult pT sT, Y, mult pT d)        (* (p*s+Y)+p*d = p*s+(Y+p*d) *)
              val rhs5 = oeq_trans_vW OF [rhs4, a2]                 (* X+p*s = p*s + (Y+p*d) *)
              val commPs = addcomm_W (mult pT sT, add Y (mult pT d))(* p*s+(Y+p*d) = (Y+p*d)+p*s *)
              val rhs6 = oeq_trans_vW OF [rhs5, commPs]             (* X+p*s = (Y+p*d)+p*s *)
              (* cancel +p*s on the right: X = Y+p*d via add_left_cancel? cancel is on LEFT add.
                 commute both sides to p*s+X = p*s+(Y+p*d) then add_left_cancel. *)
              val commL = addcomm_W (X, mult pT sT)                 (* X+p*s = p*s+X *)
              val commL_s = oeq_sym_vW OF [commL]                  (* p*s+X = X+p*s *)
              val lhsEq = oeq_trans_vW OF [commL_s, rhs6]           (* p*s+X = (Y+p*d)+p*s *)
              val commR2 = addcomm_W (add Y (mult pT d), mult pT sT)(* (Y+p*d)+p*s = p*s+(Y+p*d) *)
              val lhsEq2 = oeq_trans_vW OF [lhsEq, commR2]          (* p*s+X = p*s+(Y+p*d) *)
              val xEq = add_left_cancel_W (mult pT sT, X, add Y (mult pT d)) lhsEq2  (* X = Y+p*d *)
            in cong_introR_W (pT, X, Y, d) xEq end
          val res = exE_W (Pd, cong pT X Y) hle "d_bl" body
      in Thm.implies_intr (ctermW (jT (le sT tT))) res end
    val caseGe =
      let val hle = Thm.assume (ctermW (jT (le tT sT)))
          val Pd = Abs("d", natT, oeq sT (add tT (Bound 0)))
          fun body d (hd:thm) =
            let
              val hbal_s = oeq_sym_vW OF [hbal]                     (* Y+p*t = X+p*s *)
              val cs = mult_cong_r_W (pT, sT, add tT d) hd
              val cX = add_cong_r_W (X, mult pT sT, mult pT (add tT d)) cs
              val rhs1 = oeq_trans_vW OF [hbal_s, cX]               (* Y+p*t = X + p*(t+d) *)
              val ld = leftdistrib_W (pT, tT, d)
              val cX2 = add_cong_r_W (X, mult pT (add tT d), add (mult pT tT)(mult pT d)) ld
              val rhs2 = oeq_trans_vW OF [rhs1, cX2]
              val assoc = addassoc_W (X, mult pT tT, mult pT d)
              val assoc_s = oeq_sym_vW OF [assoc]
              val rhs3 = oeq_trans_vW OF [rhs2, assoc_s]            (* Y+p*t = (X+p*t)+p*d *)
              val comm = addcomm_W (X, mult pT tT)
              val cInner = add_cong_l_W (add X (mult pT tT), add (mult pT tT) X, mult pT d) comm
              val rhs4 = oeq_trans_vW OF [rhs3, cInner]
              val a2 = addassoc_W (mult pT tT, X, mult pT d)
              val rhs5 = oeq_trans_vW OF [rhs4, a2]
              val commPt = addcomm_W (mult pT tT, add X (mult pT d))
              val rhs6 = oeq_trans_vW OF [rhs5, commPt]             (* Y+p*t = (X+p*d)+p*t *)
              val commL = addcomm_W (Y, mult pT tT)
              val commL_s = oeq_sym_vW OF [commL]
              val lhsEq = oeq_trans_vW OF [commL_s, rhs6]
              val commR2 = addcomm_W (add X (mult pT d), mult pT tT)
              val lhsEq2 = oeq_trans_vW OF [lhsEq, commR2]
              val yEq = add_left_cancel_W (mult pT tT, Y, add X (mult pT d)) lhsEq2  (* Y = X+p*d *)
            in cong_introL_W (pT, X, Y, d) yEq end
          val res = exE_W (Pd, cong pT X Y) hle "d_bg" body
      in Thm.implies_intr (ctermW (jT (le tT sT))) res end
  in disjE_W (le sT tT, le tT sT, cong pT X Y) tot caseLe caseGe end;
val () = out "QR_BALANCE_HELPER_DEFINED\n";

(* smoke: cong_from_balance with X=Y=a and s=t -> trivially cong p a a *)
val () =
  let val pF = Free("p",natT); val aF = Free("a",natT); val sF = Free("s",natT)
      val bal = oeqRefl_W (add aF (mult pF sF))   (* a+p*s = a+p*s *)
      val cg  = cong_from_balance (pF, aF, aF, sF, sF) bal
  in if length (Thm.hyps_of cg) = 0 then out "OK cong_from_balance smoke (refl)\n"
     else out "FAIL cong_from_balance smoke\n"
  end;
val () = out "QR_PAIR_HELPER_OK\n";

(* ---- rightdistrib wrapper on ctxtW ---- *)
fun rightdistrib_W (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt),(("k",0), ctermW kt)] right_distrib_vW);

(* ============================================================================
   PER-PAIR CONGRUENCE (the crux brick):
     oeq p (add a ap) ==> oeq p (add b bp) ==> cong p (mult ap bp) (mult a b)
   ("a' = p-a, b' = p-b  =>  a'*b' == a*b (mod p)").  Balance equation:
     mult ap bp + mult p a = mult a b + mult p bp
   then cong_from_balance with s=a, t=bp.
   ============================================================================ *)
fun pair_cong (pT, aT, apT, bT, bpT) hpa hpb =
  let
    (* ap + a = p  (from p = a + ap, commute) *)
    val hpa_s = oeq_sym_vW OF [hpa]                 (* add a ap = p *)
    val commAap = addcomm_W (apT, aT)               (* ap + a = a + ap *)
    val apa_p = oeq_trans_vW OF [commAap, hpa_s]    (* ap + a = p *)
    (* (ap+a)*bp = p*bp *)
    val cLeft = mult_cong_l_W (add apT aT, pT, bpT) apa_p   (* (ap+a)*bp = p*bp *)
    val rd = rightdistrib_W (apT, aT, bpT)          (* (ap+a)*bp = ap*bp + a*bp *)
    val rd_s = oeq_sym_vW OF [rd]                    (* ap*bp + a*bp = (ap+a)*bp *)
    val sum_pbp = oeq_trans_vW OF [rd_s, cLeft]      (* ap*bp + a*bp = p*bp *)
    (* a*p = a*b + a*bp   (a*(b+bp)) *)
    val hpb_s = oeq_sym_vW OF [hpb]                  (* add b bp = p *)
    val cap = mult_cong_r_W (aT, pT, add bT bpT) (oeq_sym_vW OF [hpb_s])  (* a*p = a*(b+bp) *)
    val ld = leftdistrib_W (aT, bT, bpT)            (* a*(b+bp) = a*b + a*bp *)
    val ap_split = oeq_trans_vW OF [cap, ld]         (* a*p = a*b + a*bp *)
    (* mult p a = a*p (comm) *)
    val commPA = multcomm_W (pT, aT)                 (* p*a = a*p *)
    val pa_split = oeq_trans_vW OF [commPA, ap_split](* p*a = a*b + a*bp *)
    (* LHS of balance: mult ap bp + mult p a  -> (ap*bp) + (a*b + a*bp) *)
    val cL = add_cong_r_W (mult apT bpT, mult pT aT, add (mult aT bT) (mult aT bpT)) pa_split
       (* ap*bp + p*a = ap*bp + (a*b + a*bp) *)
    (* reassoc to (ap*bp + a*bp) + a*b via comm of (a*b)(a*bp) *)
    val commInner = addcomm_W (mult aT bT, mult aT bpT)   (* a*b + a*bp = a*bp + a*b *)
    val cInner = add_cong_r_W (mult apT bpT, add (mult aT bT)(mult aT bpT), add (mult aT bpT)(mult aT bT)) commInner
    val cL2 = oeq_trans_vW OF [cL, cInner]   (* ap*bp + p*a = ap*bp + (a*bp + a*b) *)
    val assoc = addassoc_W (mult apT bpT, mult aT bpT, mult aT bT)  (* (ap*bp+a*bp)+a*b = ap*bp+(a*bp+a*b) *)
    val assoc_s = oeq_sym_vW OF [assoc]
    val cL3 = oeq_trans_vW OF [cL2, assoc_s]  (* ap*bp + p*a = (ap*bp + a*bp) + a*b *)
    val cFold = add_cong_l_W (add (mult apT bpT)(mult aT bpT), mult pT bpT, mult aT bT) sum_pbp
       (* (ap*bp + a*bp) + a*b = p*bp + a*b *)
    val balance_raw = oeq_trans_vW OF [cL3, cFold]   (* ap*bp + p*a = p*bp + a*b *)
    (* want: add (mult ap bp)(mult p a) = add (mult a b)(mult p bp).
       have RHS = p*bp + a*b ; need a*b + p*bp. commute. *)
    val commRHS = addcomm_W (mult pT bpT, mult aT bT)   (* p*bp + a*b = a*b + p*bp *)
    val balance = oeq_trans_vW OF [balance_raw, commRHS]
       (* ap*bp + p*a = a*b + p*bp  :  add X (mult p s) = add Y (mult p t), s=a, t=bp *)
  in cong_from_balance (pT, mult apT bpT, mult aT bT, aT, bpT) balance end;

(* test: pair_cong is 0-hyp when applied to Frees with assumed complements *)
val () =
  let val pF=Free("p",natT); val aF=Free("a",natT); val apF=Free("ap",natT)
      val bF=Free("b",natT); val bpF=Free("bp",natT)
      val hpaP = jT (oeq pF (add aF apF)); val hpbP = jT (oeq pF (add bF bpF))
      val hpa = Thm.assume (ctermW hpaP); val hpb = Thm.assume (ctermW hpbP)
      val res = pair_cong (pF,aF,apF,bF,bpF) hpa hpb
      val disch = Thm.implies_intr (ctermW hpaP) (Thm.implies_intr (ctermW hpbP) res)
      val v = varify disch
  in if length (Thm.hyps_of v) = 0
     then out ("OK pair_cong (0-hyp) : " ^ Syntax.string_of_term ctxtW (Thm.prop_of v) ^ "\n")
     else out "FAIL pair_cong has hyps\n"
  end;
val () = out "QR_PAIR_CONG_OK\n";

(* ---- pair_cong as a varified THEOREM (so it lifts to extension theories) ----
     pair_cong_thm : oeq p (add a ap) ==> oeq p (add b bp) ==> cong p (mult ap bp)(mult a b) *)
val pair_cong_thm =
  let val pF=Free("p",natT); val aF=Free("a",natT); val apF=Free("ap",natT)
      val bF=Free("b",natT); val bpF=Free("bp",natT)
      val hpaP = jT (oeq pF (add aF apF)); val hpbP = jT (oeq pF (add bF bpF))
      val hpa = Thm.assume (ctermW hpaP); val hpb = Thm.assume (ctermW hpbP)
      val res = pair_cong (pF,aF,apF,bF,bpF) hpa hpb
  in varify (Thm.implies_intr (ctermW hpaP) (Thm.implies_intr (ctermW hpbP) res)) end;
val () = if length (Thm.hyps_of pair_cong_thm) = 0 then out "OK pair_cong_thm\n" else out "FAIL pair_cong_thm\n";
val () = out "QR_PAIR_CONG_THM_OK\n";
(* ============================================================================
   QR : PEEL lemma — the SPLIT of (p-1)! into w * (upper product).
   New const uprod (the descending top-k sub-product of upto(m+k)):
     uprod m 0       = 1
     uprod m (Suc k) = (add m (Suc k)) * uprod m k        [= (m+k+1)*...]
   PEEL : oeq (lprod (upto (add m k))) (mult (uprod m k) (lprod (upto m)))
   Built on a fresh theory thyU extending thyW (new-const discipline).
   ============================================================================ *)
val () = out "QR_PEEL_BEGIN\n";

(* ---- extend theory with uprod ---- *)
val thyUc = Sign.add_consts
  [(Binding.name "uprod", natT --> natT --> natT, NoSyn)] thyW;
fun cnstU nm T = Const (Sign.full_name thyUc (Binding.name nm), T);
val uprodC = cnstU "uprod" (natT --> natT --> natT); fun uprod m k = uprodC $ m $ k;

val mU = Free("m", natT); val kU = Free("k", natT);
val ((_,uprod_0_ax), thyU1) = Thm.add_axiom_global (Binding.name "uprod_0",
      jT (oeq (uprod mU ZeroC) (suc ZeroC))) thyUc;
val ((_,uprod_Suc_ax), thyU) = Thm.add_axiom_global (Binding.name "uprod_Suc",
      jT (oeq (uprod mU (suc kU)) (mult (add mU (suc kU)) (uprod mU kU)))) thyU1;

val ctxtU  = Proof_Context.init_global thyU;
val ctermU = Thm.cterm_of ctxtU;
val () = out "QR_PEEL_CONTEXT_READY\n";

(* ---- re-varify everything PEEL needs onto ctxtU ---- *)
val oeq_refl_vU   = varify oeq_refl;
val oeq_subst_vU  = varify oeq_subst;
val oeq_sym_vU    = varify oeq_sym;
val oeq_trans_vU  = varify oeq_trans;
val Suc_cong_vU   = varify Suc_cong;
val add_0_right_vU= varify add_0_right;
val add_Suc_right_vU = varify add_Suc_right;
val mult_1_left_vU= varify mult_1_left;
val mult_assoc_vU = varify mult_assoc;
val nat_induct_vU = varify nat_induct;
val leq_subst_vU  = varify leq_subst_ax;
val lprod_cons_vU = varify lprod_cons_ax;
val upto_suc_vU   = varify upto_suc_ax;
val uprod_0_vU    = uprod_0_ax;       (* Free m -- but axioms come unvarified; varify for safety *)
val uprod_0_vU    = varify uprod_0_ax;
val uprod_Suc_vU  = varify uprod_Suc_ax;
val () = out "QR_PEEL_VARIFY_READY\n";

(* ---- combinators on ctxtU ---- *)
fun oeqRefl_U t = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU t)] oeq_refl_vU);
fun oeq_rw_U (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU aT),(("b",0), ctermU bT)] oeq_subst_vU)
  in inst OF [hab, hPa] end;
fun add0r_U t   = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] add_0_right_vU);
fun addSr_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] add_Suc_right_vU);
fun mult1l_U t  = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] mult_1_left_vU);
fun multassoc_U (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] mult_assoc_vU);
fun mult_cong_l_U (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult pT kT)) end;
fun mult_cong_r_U (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult hT pT)) end;
fun nat_induct_U Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("k",0), ctermU kT)] nat_induct_vU)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;
fun leq_rw_U (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU aT),(("b",0), ctermU bT)] leq_subst_vU)
  in inst OF [hab, hPa] end;
fun lprodCons_U (ht,tt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU ht),(("t",0), ctermU tt)] lprod_cons_vU);
fun uptoSuc_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] upto_suc_vU);
fun uprod0_U t = beta_norm (Drule.infer_instantiate ctxtU [(("m",0), ctermU t)] uprod_0_vU);
fun uprodSuc_U (mt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("k",0), ctermU kt)] uprod_Suc_vU);
(* lprod_cong via leq_subst *)
fun lprod_cong_U (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)))
  in leq_rw_U (Pabs, aT, bT) hab (oeqRefl_U (lprod aT)) end;
val () = out "QR_PEEL_COMB_READY\n";

(* ============================================================================
   PEEL : oeq (lprod (upto (add m k))) (mult (uprod m k) (lprod (upto m)))
          induction on k, m fixed Free.
   ============================================================================ *)
val peel =
  let
    val mF = Free("m", natT)
    val kVar = Free("k_pl", natT)
    val Pabs = Term.lambda kVar
                 (oeq (lprod (uptoF (add mF kVar))) (mult (uprod mF kVar) (lprod (uptoF mF))))
    val base =
      let
        (* add m 0 = m  -> lprod(upto(add m 0)) = lprod(upto m).
           P z = oeq (lprod(upto z)) (lprod(upto m)) ; P m = refl ; rewrite m -> add m 0. *)
        val am0 = add0r_U mF                          (* add m 0 = m *)
        val Pup = Term.lambda (Free("z_b",natT)) (oeq (lprod (uptoF (Free("z_b",natT)))) (lprod (uptoF mF)))
        val reflPm = oeqRefl_U (lprod (uptoF mF))      (* P m : oeq (lprod(upto m))(lprod(upto m)) *)
        val lhsEq = oeq_rw_U (Pup, mF, add mF ZeroC) (oeq_sym_vU OF [am0]) reflPm
        (* lhsEq : oeq (lprod(upto(add m 0))) (lprod(upto m)) *)
        (* RHS: uprod m 0 * lprod(upto m) = 1 * lprod(upto m) = lprod(upto m) *)
        val u0 = uprod0_U mF                          (* uprod m 0 = 1 *)
        val cR = mult_cong_l_U (uprod mF ZeroC, suc ZeroC, lprod (uptoF mF)) u0  (* uprod m 0 * X = 1 * X *)
        val m1 = mult1l_U (lprod (uptoF mF))          (* 1 * X = X *)
        val rhsEq = oeq_trans_vU OF [cR, m1]          (* uprod m 0 * X = X *)
        val rhsEq_s = oeq_sym_vU OF [rhsEq]           (* X = uprod m 0 * X *)
        val res = oeq_trans_vU OF [lhsEq, rhsEq_s]
      in res end
    val step =
      let
        val xF = Free("x_pl", natT)
        val ihP = jT (oeq (lprod (uptoF (add mF xF))) (mult (uprod mF xF) (lprod (uptoF mF))))
        val hIH = Thm.assume (ctermU ihP)
        (* add m (Suc x) = Suc (add m x) *)
        val amsx = addSr_U (mF, xF)                   (* add m (Suc x) = Suc(add m x) *)
        (* lprod(upto(add m (Suc x))) = lprod(upto(Suc(add m x))) *)
        val Pup = Term.lambda (Free("z_s",natT)) (oeq (lprod (uptoF (add mF (suc xF)))) (lprod (uptoF (Free("z_s",natT)))))
        val lhs0 = oeq_rw_U (Pup, add mF (suc xF), suc (add mF xF)) amsx (oeqRefl_U (lprod (uptoF (add mF (suc xF)))))
        (* lhs0 : lprod(upto(add m (Sx))) = lprod(upto(Suc(add m x))) *)
        (* upto(Suc(add m x)) = (Suc(add m x)) :: upto(add m x) *)
        val us = uptoSuc_U (add mF xF)
        val lp_full = lprod_cong_U (uptoF (suc (add mF xF)), lcons (suc (add mF xF)) (uptoF (add mF xF))) us
        val lp_cons = lprodCons_U (suc (add mF xF), uptoF (add mF xF))
           (* lprod(cons (S(add m x)) (upto(add m x))) = (S(add m x)) * lprod(upto(add m x)) *)
        val lhs1 = oeq_trans_vU OF [oeq_trans_vU OF [lhs0, lp_full], lp_cons]
           (* lprod(upto(add m Sx)) = (S(add m x)) * lprod(upto(add m x)) *)
        (* rewrite the inner lprod(upto(add m x)) by IH *)
        val cIH = mult_cong_r_U (suc (add mF xF), lprod (uptoF (add mF xF)), mult (uprod mF xF) (lprod (uptoF mF))) hIH
        val lhs2 = oeq_trans_vU OF [lhs1, cIH]
           (* = (S(add m x)) * (uprod m x * lprod(upto m)) *)
        (* reassoc: (S(add m x)) * (uprod m x * w) = ((S(add m x)) * uprod m x) * w *)
        val assoc = multassoc_U (suc (add mF xF), uprod mF xF, lprod (uptoF mF))
        val assoc_s = oeq_sym_vU OF [assoc]
        val lhs3 = oeq_trans_vU OF [lhs2, assoc_s]
           (* = ((S(add m x)) * uprod m x) * w *)
        (* uprod m (Suc x) = (add m (Suc x)) * uprod m x ; and add m (Suc x) = Suc(add m x) *)
        val uS = uprodSuc_U (mF, xF)                  (* uprod m (Sx) = (add m (Sx)) * uprod m x *)
        (* (add m (Sx)) * uprod m x = (S(add m x)) * uprod m x  via amsx *)
        val cfac = mult_cong_l_U (add mF (suc xF), suc (add mF xF), uprod mF xF) amsx
        val uS2 = oeq_trans_vU OF [uS, cfac]          (* uprod m (Sx) = (S(add m x)) * uprod m x *)
        val uS2_s = oeq_sym_vU OF [uS2]               (* (S(add m x)) * uprod m x = uprod m (Sx) *)
        val cRHS = mult_cong_l_U (mult (suc (add mF xF)) (uprod mF xF), uprod mF (suc xF), lprod (uptoF mF)) uS2_s
           (* ((S(add m x))*uprod m x)*w = uprod m (Sx) * w *)
        val res = oeq_trans_vU OF [lhs3, cRHS]
      in Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU ihP) res) end
    val kF = Free("k_pl", natT)
    val concl = nat_induct_U Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of peel) = 0 then out "OK peel\n" else out "FAIL peel\n";
val () = out ("PEEL prop: " ^ Syntax.string_of_term ctxtU (Thm.prop_of peel) ^ "\n");
val () = out "QR_PEEL_OK\n";
(* ============================================================================
   QR : THE CRUX PARITY LEMMA (additive formulation, NO truncated subtraction).
   For p = 2m+1 and m EVEN (m = add c c), the upper product reflects to w:
        cong p (uprod m m) (lprod (upto m))
   via the pair-up invariant (induction on i, two factors per step):
     INV i := !n. m = (i+i) + n ==> cong p (uprod m (i+i) * lprod(upto n)) (lprod(upto m))
   At i = c (so i+i = m, n = 0): uprod m m * 1 == lprod(upto m).
   Each step pairs (m+S(S 2i))*(m+S 2i) with (S(S n))*(S n) via pair_cong
   (sign-free: two complements), so NO (-1)^m.
   ============================================================================ *)
val () = out "QR_PARITY_BEGIN\n";

(* ---- cong + Forall combinators on ctxtU ---- *)
val cong_refl_vU  = varify cong_refl;
val cong_sym_vU   = varify cong_sym;
val cong_trans_vU = varify cong_trans;
val cong_mult_vU  = varify cong_mult;
val allI_vU       = varify allI_ax;
val allE_vU       = varify allE_ax;
val add_0_vU2     = varify add_0;
val add_Suc_vU2   = varify add_Suc;
val add_comm_vU   = varify add_comm;
val add_assoc_vU  = varify add_assoc;
val mult_comm_vU  = varify mult_comm;
val pair_cong_vU  = varify pair_cong_thm;

fun cong_refl_U (mt,at) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("a",0), ctermU at)] cong_refl_vU);
fun cong_sym_U (mt,at,bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("a",0), ctermU at),(("b",0), ctermU bt)] cong_sym_vU)) h;
fun cong_trans_U (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("a",0), ctermU at),(("b",0), ctermU bt),(("c",0), ctermU ct)] cong_trans_vU)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_mult_U (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("a",0), ctermU at),(("a2",0), ctermU a2t),
         (("b",0), ctermU bt),(("b2",0), ctermU b2t)] cong_mult_vU)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun allI_U Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("P",0), ctermU Pabs)] allI_vU)) hAll;
fun allE_U Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("P",0), ctermU Pabs),(("a",0), ctermU at)] allE_vU)) hF;
fun add0_U t  = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] add_0_vU2);
fun addSuc_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] add_Suc_vU2);
fun addcomm_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] add_comm_vU);
fun addassoc_U (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] add_assoc_vU);
fun multcomm_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] mult_comm_vU);
fun Suc_cong_U h = Suc_cong_vU OF [h];
fun add_cong_l_U (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (add pT kT)) end;
fun add_cong_r_U (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (add hT pT)) end;
fun pair_cong_U (pt,at,apt,bt,bpt) hpa hpb =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("a",0), ctermU at),(("ap",0), ctermU apt),
         (("b",0), ctermU bt),(("bp",0), ctermU bpt)] pair_cong_vU)
  in Thm.implies_elim (Thm.implies_elim inst hpa) hpb end;
val () = out "QR_PARITY_COMB_READY\n";

(* ============================================================================
   Complement equalities for the pair step.
   Given  hp : oeq p (Suc (add m m))           [p = 2m+1]
   and    hm : oeq m (add (add i i) (Suc (Suc n)))   [m = 2i + (n+2)]
   derive E1 : oeq p (add (Suc n) (add m (Suc (Suc (add i i)))))
          E2 : oeq p (add (Suc (Suc n)) (add m (Suc (add i i))))
   Strategy: both RHS reduce to Suc(add m m). Prove by rewriting one occurrence
   of m on the RHS via hm, then pure add_comm/assoc/Suc normalization, comparing
   to Suc(add m m) (also expand the OTHER... actually expand the m INSIDE the big
   add using hm, normalize, and match Suc(add m m) with one m expanded).
   Simpler: show add(Suc n)(add m (S(S 2i))) = Suc(add m m) by:
     = m + (S(S 2i) + S n)               [comm/assoc bring m to front]
     and S(S 2i)+S n = S(S(2i + S n)) = S(S(S(2i+n)))... and m = 2i+S(S n)=S(S(2i+n)),
     so S(S 2i)+S n = S m, giving m + S m = S(add m m). matches.
   Implement via explicit term normalization using oeq rewrites.
   ============================================================================ *)
(* helper: normalize  add a (add b cc) = add b (add a cc)  (swap first two) *)
fun add_swap12_U (aT,bT,ccT) =
  (* a + (b + cc) = b + (a + cc) *)
  let val l = addassoc_U (aT,bT,ccT)            (* (a+b)+cc = a+(b+cc) *)
      val l_s = oeq_sym_vU OF [l]                (* a+(b+cc) = (a+b)+cc *)
      val cab = add_cong_l_U (add aT bT, add bT aT, ccT) (addcomm_U (aT,bT)) (* (a+b)+cc=(b+a)+cc *)
      val r = addassoc_U (bT,aT,ccT)            (* (b+a)+cc = b+(a+cc) *)
  in oeq_trans_vU OF [oeq_trans_vU OF [l_s, cab], r] end;

(* GENERAL: given hXY : oeq (add X Y) (Suc m)  [X+Y = m+1]  and hp : oeq p (Suc(add m m)),
   prove  oeq p (add X (add m Y)).
     add X (add m Y) = add m (add X Y)  [swap12]
                     = add m (Suc m)    [hXY]
                     = Suc (add m m)    [add_Suc_right]
                     = p                [sym hp]. *)
fun compl_from_sum (XT, mT, YT, pT) hXY hp =
  let
    val sw = add_swap12_U (XT, mT, YT)              (* X+(m+Y) = m+(X+Y) *)
    val cS = add_cong_r_U (mT, add XT YT, suc mT) hXY  (* m+(X+Y) = m+(Suc m) *)
    val aSr= addSr_U (mT, mT)                       (* m + Suc m = Suc(m+m) *)
    val chain = oeq_trans_vU OF [oeq_trans_vU OF [sw, cS], aSr]  (* X+(m+Y) = Suc(add m m) *)
    val hp_s = oeq_sym_vU OF [hp]                   (* Suc(add m m) = p *)
    val toP = oeq_trans_vU OF [chain, hp_s]         (* X+(m+Y) = p *)
  in oeq_sym_vU OF [toP] end;                        (* p = X+(m+Y) *)

(* sumE1 : oeq (add (S(S n)) (Suc (add i i))) (Suc m)   from hm : m = add (2i)(S(S n)) *)
fun sumE1_U (iT,mT,nT) hm =
  let val twoi = add iT iT
      val ss = addSr_U (suc (suc nT), twoi)         (* S(Sn) + S 2i = S( S(Sn) + 2i ) *)
      val cm = addcomm_U (suc (suc nT), twoi)       (* S(Sn)+2i = 2i + S(Sn) *)
      val cmS= Suc_cong_U cm                         (* S(S(Sn)+2i) = S(2i+S(Sn)) *)
      val hm_s = oeq_sym_vU OF [hm]                  (* add 2i (S(Sn)) = m *)
      val toSm = Suc_cong_U hm_s                     (* S(2i+S(Sn)) = S m *)
  in oeq_trans_vU OF [oeq_trans_vU OF [ss, cmS], toSm] end;  (* S(Sn)+S2i = Suc m *)

(* sumE2 : oeq (add (S n) (Suc (Suc (add i i)))) (Suc m)  from hm.
     (Sn)+(S(S2i)) = S( (Sn)+(S2i) ) = S(S( (Sn)+2i )) = S(S( 2i+(Sn) ))
     and 2i+(Sn) = S(2i+n) ; m = 2i+(S(Sn)) = S(2i+(Sn)) so S(2i+Sn) = m, giving S(S(2i+Sn))=Suc m. *)
fun sumE2_U (iT,mT,nT) hm =
  let val twoi = add iT iT
      val s1 = addSr_U (suc nT, suc twoi)           (* (Sn)+(S(S2i)) = S( (Sn)+(S2i) ) *)
      val s2 = addSr_U (suc nT, twoi)               (* (Sn)+(S2i) = S( (Sn)+2i ) *)
      val s2S= Suc_cong_U s2                         (* S((Sn)+(S2i)) = S(S((Sn)+2i)) *)
      val left = oeq_trans_vU OF [s1, s2S]           (* (Sn)+(S(S2i)) = S(S((Sn)+2i)) *)
      (* (Sn)+2i = 2i+(Sn) [comm] ; and 2i+(Sn) = S(2i+n) [add_Suc_right]; want relate to m.
         m = 2i+(S(Sn)) = S(2i+(Sn)) [add_Suc_right]. So 2i+(Sn) , then S(2i+Sn) = m. *)
      val cm = addcomm_U (suc nT, twoi)             (* (Sn)+2i = 2i+(Sn) *)
      val cmSS= Suc_cong_U (Suc_cong_U cm)           (* S(S((Sn)+2i)) = S(S(2i+(Sn))) *)
      val mid = oeq_trans_vU OF [left, cmSS]         (* (Sn)+(S(S2i)) = S(S(2i+(Sn))) *)
      val mSr = addSr_U (twoi, suc nT)              (* 2i + S(Sn) = S(2i + Sn) *)
      val hm2 = oeq_trans_vU OF [hm, mSr]            (* m = S(2i+Sn) *)
      val hm2s= oeq_sym_vU OF [hm2]                  (* S(2i+Sn) = m *)
      val toM = Suc_cong_U hm2s                      (* S(S(2i+Sn)) = S m *)
  in oeq_trans_vU OF [mid, toM] end;                  (* (Sn)+(S(S2i)) = Suc m *)

(* compl_eqs : returns (E1, E2)
   E1 : oeq p (add (S(S n)) (add m (Suc (add i i))))         [pairs m+S(2i) with S(S n)]
   E2 : oeq p (add (S n)     (add m (Suc (Suc (add i i)))))  [pairs m+S(S 2i) with S n] *)
fun compl_eqs (iT,mT,nT,pT) hp hm =
  let val twoi = add iT iT
      val e1 = compl_from_sum (suc (suc nT), mT, suc twoi, pT) (sumE1_U (iT,mT,nT) hm) hp
      val e2 = compl_from_sum (suc nT, mT, suc (suc twoi), pT) (sumE2_U (iT,mT,nT) hm) hp
  in (e1, e2) end;

(* smoke: run compl_eqs, print E1/E2 and check 0-hyp-after-discharge *)
val () =
  let val iF=Free("i",natT); val mF=Free("m",natT); val nF=Free("n",natT); val pF=Free("p",natT)
      val hpP = jT (oeq pF (suc (add mF mF))); val hmP = jT (oeq mF (add (add iF iF) (suc (suc nF))))
      val hp = Thm.assume (ctermU hpP); val hm = Thm.assume (ctermU hmP)
      val (e1,e2) = compl_eqs (iF,mF,nF,pF) hp hm
      val d1 = varify (Thm.implies_intr (ctermU hpP) (Thm.implies_intr (ctermU hmP) e1))
  in out ("E1 = " ^ Syntax.string_of_term ctxtU (Thm.prop_of e1) ^ "\n");
     out ("E2 = " ^ Syntax.string_of_term ctxtU (Thm.prop_of e2) ^ "\n");
     out (if length (Thm.hyps_of d1) = 0 then "QR_COMPL_OK\n" else "QR_COMPL_HYPS\n")
  end;

(* ---- cong_of_eq on ctxtU : oeq X Y ==> cong p X Y (capture-safe) ---- *)
fun cong_of_eq_U (pT, X, Y) heq =
  let val zF = Free("z_coeU", natT)
      val Pabs = Term.lambda zF (cong pT X zF)
      val inst = beta_norm (Drule.infer_instantiate ctxtU
            [(("P",0), ctermU Pabs),(("a",0), ctermU X),(("b",0), ctermU Y)] oeq_subst_vU)
      val crefl = cong_refl_U (pT, X)
  in inst OF [heq, crefl] end;

(* mSr / addSr on ctxtU already (addSr_U). Need add rearrange:
   rearr_2i : m = add (S(S(2i))) n  ==>  oeq m (add (2i) (S(S n)))   (for applying IH) *)
fun rearr_to_ih (iT,mT,nT) hm =
  (* hm : m = add (S(S 2i)) n ; want m = add 2i (S(S n)).
     add (S(S 2i)) n = add 2i (add (S(S 0)?...)) -- easier: 
     S(S 2i) + n = S(S(2i+n)) [add_Suc twice on the LEFT arg... add_Suc: (S a)+b = S(a+b)]
     and 2i + S(S n) = S(S(2i+n)) [add_Suc_right twice]. Both = S(S(2i+n)). *)
  let val twoi = add iT iT
      val l1 = addSuc_U (suc twoi, nT)            (* (S(S2i))+n = S( (S2i)+n ) *)
      val l2 = addSuc_U (twoi, nT)                (* (S2i)+n = S(2i+n) *)
      val l2S= Suc_cong_U l2
      val left = oeq_trans_vU OF [l1, l2S]         (* (S(S2i))+n = S(S(2i+n)) *)
      val r1 = addSr_U (twoi, suc nT)             (* 2i + S(Sn) = S(2i + Sn) *)
      val r2 = addSr_U (twoi, nT)                 (* 2i + Sn = S(2i+n) *)
      val r2S= Suc_cong_U r2
      val right = oeq_trans_vU OF [r1, r2S]        (* 2i + S(Sn) = S(S(2i+n)) *)
      val right_s = oeq_sym_vU OF [right]          (* S(S(2i+n)) = 2i+S(Sn) *)
      val hm2 = oeq_trans_vU OF [hm, left]         (* m = S(S(2i+n)) *)
  in oeq_trans_vU OF [hm2, right_s] end;            (* m = 2i + S(Sn) *)

val () = out "QR_PARITY_STEP_HELPERS_OK\n";

(* impI / mp / Imp helpers on ctxtU *)
val impI_vU = varify impI_ax;
val mp_vU   = varify mp_ax;
fun impI_U (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At),(("B",0), ctermU Bt)] impI_vU)
  in Thm.implies_elim inst hImpThm end;
fun mp_U (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At),(("B",0), ctermU Bt)] mp_vU)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
(* mult assoc-based reassoc helpers *)
fun mult_cong_l_U (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult pT kT)) end;
fun mult_cong_r_U (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult hT pT)) end;
val () = out "QR_PARITY_IMP_HELPERS_OK\n";

(* ============================================================================
   PARITY_CRUX (full): oeq p (Suc(add m m)) ==> oeq m (add c c)
                       ==> cong p (uprod m m) (lprod (upto m))
   ============================================================================ *)
val parity_crux =
  let
    val pF = Free("p", natT); val mF = Free("m", natT); val cF = Free("c", natT)
    val hpP = jT (oeq pF (suc (add mF mF))); val hp = Thm.assume (ctermU hpP)
    val hmcP = jT (oeq mF (add cF cF)); val hmc = Thm.assume (ctermU hmcP)

    fun lhsAt iT nT = mult (uprod mF (add iT iT)) (lprod (uptoF nT))
    fun bodyAt iT nT = mkImp (oeq mF (add (add iT iT) nT)) (cong pF (lhsAt iT nT) (lprod (uptoF mF)))
    fun forallBody iT = Term.lambda (Free("n_pf", natT)) (bodyAt iT (Free("n_pf", natT)))
    val iVar = Free("i_pf", natT)
    val Pabs = Term.lambda iVar (mkForall (forallBody iVar))

    (* ---------- BASE i=0 ---------- *)
    val base =
      let
        val nF = Free("n_pb", natT)
        val hypT = oeq mF (add (add ZeroC ZeroC) nF)
        val hh   = Thm.assume (ctermU (jT hypT))
        val a00 = add0_U ZeroC
        val Pr1 = Term.lambda (Free("z_b1",natT)) (oeq mF (add (Free("z_b1",natT)) nF))
        val hh1 = oeq_rw_U (Pr1, add ZeroC ZeroC, ZeroC) a00 hh
        val a0n = add0_U nF
        val m_n = oeq_trans_vU OF [hh1, a0n]           (* m = n *)
        val u0a = oeq_rw_U (Term.lambda (Free("z_b2",natT)) (oeq (uprod mF (Free("z_b2",natT))) (uprod mF ZeroC)),
                            ZeroC, add ZeroC ZeroC) (oeq_sym_vU OF [a00]) (oeqRefl_U (uprod mF ZeroC))
        val u0 = uprod0_U mF
        val uA = oeq_trans_vU OF [u0a, u0]             (* uprod m (0+0) = 1 *)
        val cL = mult_cong_l_U (uprod mF (add ZeroC ZeroC), suc ZeroC, lprod (uptoF nF)) uA
        val m1 = mult1l_U (lprod (uptoF nF))
        val lhsEq = oeq_trans_vU OF [cL, m1]           (* LHS = lprod(upto n) *)
        val Pz = Term.lambda (Free("z_b4",natT)) (oeq (lprod (uptoF nF)) (lprod (uptoF (Free("z_b4",natT)))))
        val n_m = oeq_sym_vU OF [m_n]
        val ln_lm = oeq_rw_U (Pz, nF, mF) n_m (oeqRefl_U (lprod (uptoF nF)))
        val lhsEq2 = oeq_trans_vU OF [lhsEq, ln_lm]    (* LHS = lprod(upto m) *)
        val congB = cong_of_eq_U (pF, lhsAt ZeroC nF, lprod (uptoF mF)) lhsEq2
        val imp = impI_U (hypT, cong pF (lhsAt ZeroC nF) (lprod (uptoF mF)))
                    (Thm.implies_intr (ctermU (jT hypT)) congB)
      in allI_U (forallBody ZeroC) (Thm.forall_intr (ctermU nF) imp) end
    val () = out "QR_PARITY_BASE_OK\n"

    (* ---------- STEP i -> Suc i ---------- *)
    val step =
      let
        val xF = Free("i_ps", natT)
        val ihP = jT (mkForall (forallBody xF))
        val hIH = Thm.assume (ctermU ihP)
        val nF = Free("n_ps", natT)
        val twoSi = add (suc xF) (suc xF)
        val hypT = oeq mF (add twoSi nF)
        val hh   = Thm.assume (ctermU (jT hypT))
        (* m = (S x + S x) + n.  S x + S x = S(S(x+x)) = S(S 2i).  rearr to ih form. *)
        val l1 = addSuc_U (xF, suc xF)                (* (S x) + (S x) = S(x + (S x)) *)
        val l2 = addSr_U (xF, xF)                     (* x + (S x) = S(x+x) *)
        val l2S= Suc_cong_U l2                         (* S(x + S x) = S(S(x+x)) *)
        val twoSi_norm = oeq_trans_vU OF [l1, l2S]    (* (S x)+(S x) = S(S(x+x)) *)
        (* hh -> m = S(S(x+x)) + n via rewriting twoSi *)
        val Phh = Term.lambda (Free("z_h",natT)) (oeq mF (add (Free("z_h",natT)) nF))
        val hh2 = oeq_rw_U (Phh, twoSi, suc (suc (add xF xF))) twoSi_norm hh  (* m = S(S(2i)) + n *)
        val () = out ("MK hh2 = " ^ Syntax.string_of_term ctxtU (Thm.prop_of hh2) ^ "\n")
        (* rearr to m = 2i + S(S n) for IH *)
        val hmIH = rearr_to_ih (xF, mF, nF) hh2       (* m = (x+x) + S(S n) *)
        val () = out ("MK hmIH = " ^ Syntax.string_of_term ctxtU (Thm.prop_of hmIH) ^ "\n")
        (* apply IH at S(S n) *)
        val congIH = mp_U (oeq mF (add (add xF xF) (suc (suc nF))),
                            cong pF (lhsAt xF (suc (suc nF))) (lprod (uptoF mF)))
                          (allE_U (forallBody xF) (suc (suc nF)) hIH) hmIH
        val () = out ("MK congIH = " ^ Syntax.string_of_term ctxtU (Thm.prop_of congIH) ^ "\n")
        (* congIH : cong p (uprod m (x+x) * lprod(upto (S(S n)))) (lprod(upto m)) *)
        (* complement eqs -- compl_eqs/sumE*_U expect hm : m = add (2i)(S(S n)) = hmIH *)
        val (e1, e2) = compl_eqs (xF, mF, nF, pF) hp hmIH
        val () = out "MK compl_eqs ok\n"
        (* pair_cong : cong p ((m+S 2i)*(m+S(S 2i))) ((S(S n))*(S n)) *)
        val twoi = add xF xF
        val pairCong = pair_cong_U (pF, suc (suc nF), add mF (suc twoi),
                                        suc nF, add mF (suc (suc twoi))) e1 e2
        (* pairCong : cong p (mult (add m (S 2i)) (add m (S(S 2i)))) (mult (S(S n)) (S n)) *)
        val () = out ("PAIRCONG = " ^ Syntax.string_of_term ctxtU (Thm.prop_of pairCong) ^ "\n")

        (* abbreviations *)
        val A1 = add mF (suc twoi)            (* m + S 2i      *)
        val A2 = add mF (suc (suc twoi))      (* m + S(S 2i)   *)
        val B1 = suc (suc nF)                 (* S(S n)        *)
        val B2 = suc nF                       (* S n           *)
        val U2 = uprod mF twoi                (* uprod m 2i    *)
        val LN = lprod (uptoF nF)             (* lprod(upto n) *)
        val C  = mult U2 LN                   (* the common tail C *)

        (* ----- newLHS_eq : oeq (lhsAt (Suc i) n) (mult (mult A1 A2) C) -----
           lhsAt (Suc i) n = uprod m ((S i)+(S i)) * LN.
           (S i)+(S i) -> S(S 2i) [twoSi_norm] ; uprod m (S(S 2i)) = A2 * (A1 * U2). *)
        val Pexp = Term.lambda (Free("z_e",natT)) (oeq (uprod mF (add (suc xF)(suc xF))) (uprod mF (Free("z_e",natT))))
        val uExp = oeq_rw_U (Pexp, add (suc xF)(suc xF), suc (suc twoi)) twoSi_norm
                     (oeqRefl_U (uprod mF (add (suc xF)(suc xF))))
           (* uprod m ((Si)+(Si)) = uprod m (S(S 2i)) *)
        val uS2 = uprodSuc_U (mF, suc twoi)          (* uprod m (S(S 2i)) = A2 * uprod m (S 2i) *)
        val uS1 = uprodSuc_U (mF, twoi)              (* uprod m (S 2i) = A1 * U2 *)
        val uS1c= mult_cong_r_U (A2, uprod mF (suc twoi), mult A1 U2) uS1  (* A2 * uprod m (S 2i) = A2 * (A1 * U2) *)
        val uFull = oeq_trans_vU OF [oeq_trans_vU OF [uExp, uS2], uS1c]
           (* uprod m ((Si)+(Si)) = A2 * (A1 * U2) *)
        (* lhsAt (Suc i) n = uprod m ((Si)+(Si)) * LN = (A2*(A1*U2)) * LN *)
        val nl1 = mult_cong_l_U (uprod mF (add (suc xF)(suc xF)), mult A2 (mult A1 U2), LN) uFull
           (* lhsAt (Suc i) n = (A2*(A1*U2)) * LN *)
        (* reassoc (A2*(A1*U2))*LN -> want (A1*A2)*C  where C = U2*LN.
           (A2*(A1*U2))*LN = A2*((A1*U2)*LN)  [assoc]
                           = A2*(A1*(U2*LN))  [assoc inner]
                           = A2*(A1*C)
                           = (A2*A1)*C        [assoc]
                           = (A1*A2)*C        [comm A1 A2] *)
        val r1 = multassoc_U (A2, mult A1 U2, LN)             (* (A2*(A1*U2))*LN = A2*((A1*U2)*LN) *)
        val r2 = multassoc_U (A1, U2, LN)                     (* (A1*U2)*LN = A1*(U2*LN)=A1*C *)
        val r2c= mult_cong_r_U (A2, mult (mult A1 U2) LN, mult A1 C) r2  (* A2*((A1*U2)*LN)=A2*(A1*C) *)
        val r3 = multassoc_U (A2, A1, C)                      (* (A2*A1)*C = A2*(A1*C) *)
        val r3s= oeq_sym_vU OF [r3]                            (* A2*(A1*C) = (A2*A1)*C *)
        val r4 = multcomm_U (A2, A1)                          (* A2*A1 = A1*A2 *)
        val r4c= mult_cong_l_U (mult A2 A1, mult A1 A2, C) r4  (* (A2*A1)*C = (A1*A2)*C *)
        val reassocNL = oeq_trans_vU OF [oeq_trans_vU OF [oeq_trans_vU OF [r1, r2c], r3s], r4c]
           (* (A2*(A1*U2))*LN = (A1*A2)*C *)
        val newLHS_eq = oeq_trans_vU OF [nl1, reassocNL]
           (* lhsAt (Suc i) n = (A1*A2)*C *)

        (* ----- IHside_eq : oeq (lhsAt i (S(S n))) (mult (mult B1 B2) C) -----
           lhsAt i (S(S n)) = U2 * lprod(upto (S(S n))).
           lprod(upto(S(S n))) = B1 * lprod(upto(S n)) = B1*(B2*LN). *)
        val us1 = uptoSuc_U (suc nF)                 (* upto(S(S n)) = (S(S n)) :: upto(S n) *)
        val lpc1 = lprodCons_U (suc (suc nF), uptoF (suc nF))  (* lprod((S(Sn))::upto(Sn)) = B1 * lprod(upto(Sn)) *)
        val lpcong1 = lprod_cong_U (uptoF (suc (suc nF)), lcons (suc (suc nF)) (uptoF (suc nF))) us1
           (* lprod(upto(S(Sn))) = lprod((S(Sn))::upto(Sn)) *)
        val lpA = oeq_trans_vU OF [lpcong1, lpc1]    (* lprod(upto(S(Sn))) = B1 * lprod(upto(Sn)) *)
        val us2 = uptoSuc_U nF                        (* upto(S n) = (S n) :: upto n *)
        val lpc2 = lprodCons_U (suc nF, uptoF nF)     (* lprod((Sn)::upto n) = B2 * LN *)
        val lpcong2 = lprod_cong_U (uptoF (suc nF), lcons (suc nF) (uptoF nF)) us2
        val lpB = oeq_trans_vU OF [lpcong2, lpc2]     (* lprod(upto(S n)) = B2 * LN *)
        val lpBc= mult_cong_r_U (B1, lprod (uptoF (suc nF)), mult B2 LN) lpB  (* B1*lprod(upto(Sn)) = B1*(B2*LN) *)
        val lpFull = oeq_trans_vU OF [lpA, lpBc]      (* lprod(upto(S(Sn))) = B1*(B2*LN) *)
        (* lhsAt i (S(S n)) = U2 * lprod(upto(S(Sn))) = U2 * (B1*(B2*LN)) *)
        val ih1 = mult_cong_r_U (U2, lprod (uptoF (suc (suc nF))), mult B1 (mult B2 LN)) lpFull
           (* lhsAt i (S(Sn)) = U2 * (B1*(B2*LN)) *)
        (* reassoc U2*(B1*(B2*LN)) -> (B1*B2)*C
           U2*(B1*(B2*LN)) = U2*((B1*B2)*LN)  [inner assoc back]
                           = (U2*(B1*B2))*LN  [assoc]   -- messy; do via comm:
           Simpler: U2*(B1*(B2*LN)) = (B1*B2)*(U2*LN) ? Use commutativity chain.
           Path: U2*(B1*(B2*LN))
              = U2*((B1*B2)*LN)         [B1*(B2*LN)=(B1*B2)*LN : assoc back]
              = (B1*B2)*LN * U2 ??  ... use comm to pull (B1*B2) out.
           Cleanest: target (B1*B2)*C = (B1*B2)*(U2*LN).
              (B1*B2)*(U2*LN) = ((B1*B2)*U2)*LN [assoc]
                              = (U2*(B1*B2))*LN [comm]
                              = U2*((B1*B2)*LN) [assoc]
                              = U2*(B1*(B2*LN)) [inner assoc]  -- exactly ih1's RHS, reversed.
           So prove RHS->LHS then sym. *)
        val q1 = multassoc_U (mult B1 B2, U2, LN)            (* ((B1*B2)*U2)*LN = (B1*B2)*(U2*LN) *)
        val q1s= oeq_sym_vU OF [q1]                           (* (B1*B2)*C = ((B1*B2)*U2)*LN *)
        val q2 = multcomm_U (mult B1 B2, U2)                 (* (B1*B2)*U2 = U2*(B1*B2) *)
        val q2c= mult_cong_l_U (mult (mult B1 B2) U2, mult U2 (mult B1 B2), LN) q2 (* ((B1*B2)*U2)*LN = (U2*(B1*B2))*LN *)
        val q3 = multassoc_U (U2, mult B1 B2, LN)            (* (U2*(B1*B2))*LN = U2*((B1*B2)*LN) *)
        val q4 = multassoc_U (B1, B2, LN)                    (* (B1*B2)*LN = B1*(B2*LN) *)
        val q4c= mult_cong_r_U (U2, mult (mult B1 B2) LN, mult B1 (mult B2 LN)) q4 (* U2*((B1*B2)*LN)=U2*(B1*(B2*LN)) *)
        val rhsToIh = oeq_trans_vU OF [oeq_trans_vU OF [oeq_trans_vU OF [q1s, q2c], q3], q4c]
           (* (B1*B2)*C = U2*(B1*(B2*LN)) *)
        val ihToRhs = oeq_sym_vU OF [rhsToIh]                 (* U2*(B1*(B2*LN)) = (B1*B2)*C *)
        val IHside_eq = oeq_trans_vU OF [ih1, ihToRhs]        (* lhsAt i (S(Sn)) = (B1*B2)*C *)

        (* ----- the step congruence -----
           pairCong : cong p (A1*A2) (B1*B2).  cong_mult (p,a,a2,b,b2):
             cong p a a2 ==> cong p b b2 ==> cong p (a*b)(a2*b2).
           a=A1*A2, a2=B1*B2, b=C, b2=C  ->  cong p ((A1*A2)*C) ((B1*B2)*C). *)
        val creflC = cong_refl_U (pF, C)
        val congPC = cong_mult_U (pF, mult A1 A2, mult B1 B2, C, C) pairCong creflC
           (* cong p ((A1*A2)*C) ((B1*B2)*C) *)
        (* bridge to newLHS / IHside via cong_of_eq + cong_trans:
           newLHS = (A1*A2)*C  [newLHS_eq] ; IHside = (B1*B2)*C  [IHside_eq] *)
        val nlc = cong_of_eq_U (pF, lhsAt (suc xF) nF, mult (mult A1 A2) C) newLHS_eq
           (* cong p (lhsAt (Si) n) ((A1*A2)*C) *)
        val ihc = cong_of_eq_U (pF, lhsAt xF (suc (suc nF)), mult (mult B1 B2) C) IHside_eq
           (* cong p (lhsAt i (S(Sn))) ((B1*B2)*C) *)
        val ihc_sym = cong_sym_U (pF, lhsAt xF (suc (suc nF)), mult (mult B1 B2) C) ihc
           (* cong p ((B1*B2)*C) (lhsAt i (S(Sn))) *)
        (* chain: lhsAt(Si)n -> (A1*A2)*C -> (B1*B2)*C -> lhsAt i (S(Sn)) -> lprod(upto m) *)
        val t1 = cong_trans_U (pF, lhsAt (suc xF) nF, mult (mult A1 A2) C, mult (mult B1 B2) C) nlc congPC
        val t2 = cong_trans_U (pF, lhsAt (suc xF) nF, mult (mult B1 B2) C, lhsAt xF (suc (suc nF))) t1 ihc_sym
        val stepCong = cong_trans_U (pF, lhsAt (suc xF) nF, lhsAt xF (suc (suc nF)), lprod (uptoF mF)) t2 congIH
           (* cong p (lhsAt (Suc i) n) (lprod(upto m)) *)
        val () = out "QR_PARITY_STEP_NORMALIZED_OK\n"
        (* discharge the hypothesis (m = (Si)+(Si)+n) and the Forall n *)
        val concl = cong pF (lhsAt (suc xF) nF) (lprod (uptoF mF))
        val imp = impI_U (hypT, concl) (Thm.implies_intr (ctermU (jT hypT)) stepCong)
        val forallStep = allI_U (forallBody (suc xF)) (Thm.forall_intr (ctermU nF) imp)
      in Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU ihP) forallStep) end
    val () = out "QR_PARITY_STEP_OK\n"

    (* ---------- run the induction at i := c ---------- *)
    val concl_c = nat_induct_U Pabs cF base step   (* Forall n. (m=(c+c)+n) ==> cong p (uprod m (c+c) * lprod(upto n)) (lprod(upto m)) *)
    (* instantiate n := 0 ; m = (c+c)+0 needs hmc (m=c+c) + add_0_right *)
    val ac0 = add0r_U (add cF cF)                  (* (c+c)+0 = c+c *)
    val hm_eq = oeq_trans_vU OF [hmc, oeq_sym_vU OF [ac0]]  (* m = (c+c)+0 *)
    val instImp = allE_U (forallBody cF) ZeroC concl_c     (* (m=(c+c)+0) ==> cong p (uprod m (c+c) * lprod(upto 0)) (lprod(upto m)) *)
    val congC = mp_U (oeq mF (add (add cF cF) ZeroC),
                      cong pF (lhsAt cF ZeroC) (lprod (uptoF mF))) instImp hm_eq
       (* cong p (uprod m (c+c) * lprod(upto 0)) (lprod(upto m)) *)
    (* simplify LHS: uprod m (c+c) -> uprod m m (via hmc sym), lprod(upto 0)=1, *1 drop *)
    (* uprod m (c+c) = uprod m m : rewrite (c+c) -> m via sym hmc *)
    val Pue = Term.lambda (Free("z_ue",natT)) (cong pF (mult (uprod mF (Free("z_ue",natT))) (lprod (uptoF ZeroC))) (lprod (uptoF mF)))
    val hmc_s = oeq_sym_vU OF [hmc]                 (* (c+c) = m ... wait hmc: m=c+c, sym: c+c=m *)
    val congC2 = oeq_rw_U (Pue, add cF cF, mF) hmc_s congC
       (* cong p (uprod m m * lprod(upto 0)) (lprod(upto m)) *)
    (* lprod(upto 0) = 1 *)
    val u0 = varify upto_zero_ax                     (* upto 0 = lnil (leq) *)
    val lp0 = lprod_cong_U (uptoF ZeroC, lnilC) u0  (* lprod(upto 0) = lprod lnil *)
    val lpnil = varify lprod_nil_ax
    val lpnilU = beta_norm lpnil                     (* oeq (lprod lnil) (Suc Zero) *)
    val lp0one = oeq_trans_vU OF [lp0, lpnilU]       (* lprod(upto 0) = 1 *)
    (* rewrite lprod(upto 0) -> 1 in congC2 *)
    val Plp = Term.lambda (Free("z_lp",natT)) (cong pF (mult (uprod mF mF) (Free("z_lp",natT))) (lprod (uptoF mF)))
    val congC3 = oeq_rw_U (Plp, lprod (uptoF ZeroC), suc ZeroC) lp0one congC2
       (* cong p (uprod m m * 1) (lprod(upto m)) *)
    (* uprod m m * 1 = uprod m m *)
    val m1r = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU (uprod mF mF))] (varify mult_1_right))
       (* oeq (uprod m m * 1) (uprod m m) *)
    val Pm1 = Term.lambda (Free("z_m1",natT)) (cong pF (Free("z_m1",natT)) (lprod (uptoF mF)))
    val congFinal = oeq_rw_U (Pm1, mult (uprod mF mF) (suc ZeroC), uprod mF mF) m1r congC3
       (* cong p (uprod m m) (lprod(upto m)) *)
    val d2 = Thm.implies_intr (ctermU hmcP) congFinal
    val d1 = Thm.implies_intr (ctermU hpP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of parity_crux) = 0 then out "OK parity_crux\n" else out "FAIL parity_crux\n";
val () = out ("PARITY_CRUX prop: " ^ Syntax.string_of_term ctxtU (Thm.prop_of parity_crux) ^ "\n");
val () = out "QR_PARITY_PROVED\n";
(* ============================================================================
   QR FINALE : -1 is a quadratic residue mod p, for prime p == 1 (mod 4).
     qr_minus1 : prime2 p ==> oeq (sub p 1) (add (add k k)(add k k))
                 ==> Ex x. cong p (mult x x) (sub p 1)
   ("p == 1 mod 4" encoded as p-1 = 4k.)  Witness x = w = lprod(upto ((p-1)/2)).
   ============================================================================ *)
val () = out "QR_FINAL_BEGIN\n";

(* ---- exE on ctxtU ---- *)
val exE_vU = varify exE_ax;
fun exE_U (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermU hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermU wF) (Thm.implies_intr (ctermU hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtU
                      [(("P",0), ctermU Pabs),(("Q",0), ctermU goalC)] exE_vU)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
val exI_vU = varify exI_ax;
fun exI_U Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU at)] exI_vU)
  in Thm.implies_elim inst hbody end;

(* accessors *)
fun wilson_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] wilson)) hPrime;
fun peel_U (mt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("k_pl",0), ctermU kt)] peel);
fun parity_crux_U (pt,mt,ct) hp hmc =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("m",0), ctermU mt),(("c",0), ctermU ct)] parity_crux)
  in Thm.implies_elim (Thm.implies_elim inst hp) hmc end;

(* cong on ctxtU : refl/sym/trans/mult/of_eq already defined.  wilson is a thm on
   thyW (subtheory of thyU); varify it onto ctxtU. *)
val wilson_vU = varify wilson;
fun wilson_U pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt)] wilson_vU)) hPrime;

(* prime2 1<p destructor on ctxtU *)
val conjunct1_vU = varify conjunct1_ax;
fun conjunct1_U (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("A",0), ctermU At),(("B",0), ctermU Bt)] conjunct1_vU)) h;
fun prime2_gt1_U pt hpr = conjunct1_U (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hpr;

val pos_pred_vU = varify pos_pred;
val sub_suc_one_vU = varify sub_suc_one;

(* p_eq_Suc_pred : prime2 p ==> oeq p (Suc (sub p 1)) *)
val p_eq_Suc_pred =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermU hPrimeP)
    val hp1 = prime2_gt1_U pF hPrime
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU [(("p",0), ctermU pF)] pos_pred_vU)) hp1
    val goalC = oeq pF (suc (sub pF (suc ZeroC)))
    fun body q (hq:thm) =
      let
        val sso = beta_norm (Drule.infer_instantiate ctxtU [(("q",0), ctermU q)] sub_suc_one_vU)
        val hq_s = oeq_sym_vU OF [hq]
        val Psub = Term.lambda (Free("z_sp",natT)) (oeq (sub (Free("z_sp",natT)) (suc ZeroC)) q)
        val subPq = oeq_rw_U (Psub, suc q, pF) hq_s sso
        val subPq_s = oeq_sym_vU OF [subPq]
        val Sub = Suc_cong_U subPq_s
        val res = oeq_trans_vU OF [hq, Sub]
      in res end
    val res = exE_U (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_sp" body
  in varify (Thm.implies_intr (ctermU hPrimeP) res) end;
val () = if length (Thm.hyps_of p_eq_Suc_pred) = 0 then out "OK p_eq_Suc_pred\n" else out "FAIL p_eq_Suc_pred\n";
fun p_eq_Suc_pred_U pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt)] p_eq_Suc_pred)) hPrime;
val () = out "QR_FINAL_PSUC_OK\n";

(* ============================================================================
   qr_minus1
   ============================================================================ *)
val qr_minus1 =
  let
    val pF = Free("p", natT); val kF = Free("k", natT)
    val one = suc ZeroC
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermU hPrimeP)
    (* p-1 = 4k = (k+k)+(k+k) ; let m = k+k *)
    val mTerm = add kF kF
    val h4kP = jT (oeq (sub pF one) (add mTerm mTerm)); val h4k = Thm.assume (ctermU h4kP)
    val w = lprod (uptoF mTerm)

    (* Wilson : cong p (lprod(upto(sub p 1))) (sub p 1) *)
    val congWil = wilson_U pF hPrime
    (* rewrite sub p 1 -> add m m inside the FIRST argument (upto): congWil becomes
       cong p (lprod(upto(add m m))) (sub p 1)  -- only rewrite the upto-occurrence. *)
    val Pw1 = Term.lambda (Free("z_w1",natT)) (cong pF (lprod (uptoF (Free("z_w1",natT)))) (sub pF one))
    val congWil2 = oeq_rw_U (Pw1, sub pF one, add mTerm mTerm) h4k congWil
       (* cong p (lprod(upto(add m m))) (sub p 1) *)

    (* PEEL at (m, m) : lprod(upto(add m m)) = uprod m m * w *)
    val peelMM = peel_U (mTerm, mTerm)   (* oeq (lprod(upto(add m m))) (uprod m m * lprod(upto m)) *)
    (* parity_crux : need p = Suc(add m m) and m = add c c (c=k).
       p = Suc(sub p 1) [p_eq_Suc_pred] ; sub p 1 = add m m [h4k] => p = Suc(add m m). *)
    val pSucPred = p_eq_Suc_pred_U pF hPrime       (* p = Suc(sub p 1) *)
    val SubMM = Suc_cong_U h4k                       (* Suc(sub p 1) = Suc(add m m) *)
    val pEqSucMM = oeq_trans_vU OF [pSucPred, SubMM] (* p = Suc(add m m) *)
    val hmc = oeqRefl_U mTerm                        (* m = add k k : need oeq (add k k)(add k k)?? *)
    (* parity_crux wants hmc : oeq m (add c c) with m=mTerm=add k k, c=k -> oeq (add k k)(add k k) = refl *)
    val parC = parity_crux_U (pF, mTerm, kF) pEqSucMM (oeqRefl_U mTerm)
       (* cong p (uprod m m) w *)
    (* cong p (uprod m m * w) (w * w) via cong_mult parC (cong_refl w) *)
    val creflW = cong_refl_U (pF, w)
    val congUWWW = cong_mult_U (pF, uprod mTerm mTerm, w, w, w) parC creflW
       (* cong p (uprod m m * w) (w * w) *)
    (* lprod(upto(add m m)) = uprod m m * w  [peelMM] => cong p (lprod(upto(add m m))) (uprod m m * w) *)
    val congPeel = cong_of_eq_U (pF, lprod (uptoF (add mTerm mTerm)), mult (uprod mTerm mTerm) w) peelMM
    (* chain: cong p (lprod(upto(add m m))) (w*w) *)
    val congToWW = cong_trans_U (pF, lprod (uptoF (add mTerm mTerm)), mult (uprod mTerm mTerm) w, mult w w)
                     congPeel congUWWW
    (* Wilson gave cong p (lprod(upto(add m m))) (sub p 1). sym it, then trans with congToWW:
       cong p (w*w) (lprod(upto(add m m))) then ... actually:
       want cong p (w*w) (sub p 1):  sym congToWW -> cong p (w*w) (lprod(upto(add m m)))
            then trans with congWil2 (cong p (lprod(upto(add m m))) (sub p 1)). *)
    val congWWtoLp = cong_sym_U (pF, lprod (uptoF (add mTerm mTerm)), mult w w) congToWW
       (* cong p (w*w) (lprod(upto(add m m))) *)
    val congWWsub = cong_trans_U (pF, mult w w, lprod (uptoF (add mTerm mTerm)), sub pF one)
                      congWWtoLp congWil2
       (* cong p (w*w) (sub p 1) *)
    (* Ex x. cong p (mult x x) (sub p 1) , witness x = w *)
    val Pex = Term.lambda (Free("x_qr", natT)) (cong pF (mult (Free("x_qr",natT)) (Free("x_qr",natT))) (sub pF one))
    val exX = exI_U Pex w congWWsub
    val d2 = Thm.implies_intr (ctermU h4kP) exX
    val d1 = Thm.implies_intr (ctermU hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of qr_minus1) = 0 then out "OK qr_minus1\n" else out "FAIL qr_minus1\n";
val () = out ("QR_MINUS1 prop: " ^ Syntax.string_of_term ctxtU (Thm.prop_of qr_minus1) ^ "\n");

(* ---- validation: aconv intended + soundness probes ---- *)
val pV = Var(("p",0),natT); val kV = Var(("k",0),natT); val oneV = suc ZeroC;
val mV = add kV kV;
val qr_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
      jT (mkEx (Term.lambda (Free("x_qr",natT)) (cong pV (mult (Free("x_qr",natT))(Free("x_qr",natT))) (sub pV oneV))))));
val r_qr = (length (Thm.hyps_of qr_minus1) = 0) andalso ((Thm.prop_of qr_minus1) aconv qr_intended);
val () = if r_qr then out "OK qr_minus1 aconv intended\n" else out "FAIL qr_minus1 aconv\n";
(* probe: needs prime hyp *)
val qr_BOGUS_noprime =
  Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
    jT (mkEx (Term.lambda (Free("x_qr",natT)) (cong pV (mult (Free("x_qr",natT))(Free("x_qr",natT))) (sub pV oneV)))));
val probe_prime = not ((Thm.prop_of qr_minus1) aconv qr_BOGUS_noprime);
val () = if probe_prime then out "PROBE_OK qr_minus1 keeps prime hyp\n" else out "PROBE_FAIL qr_minus1\n";
(* probe: needs the 1-mod-4 hyp *)
val qr_BOGUS_no4k =
  Logic.mk_implies (jT (prime2 pV),
    jT (mkEx (Term.lambda (Free("x_qr",natT)) (cong pV (mult (Free("x_qr",natT))(Free("x_qr",natT))) (sub pV oneV)))));
val probe_4k = not ((Thm.prop_of qr_minus1) aconv qr_BOGUS_no4k);
val () = if probe_4k then out "PROBE_OK qr_minus1 keeps p==1mod4 hyp\n" else out "PROBE_FAIL qr_minus1 4k\n";

val () =
  if r_qr andalso probe_prime andalso probe_4k
  then out "QR_MINUS1_OK\n" else out "QR_MINUS1_FAILED\n";
val () = out "BASE_OK\n";
(* ============================================================================
   QR PAIR-UP ASSEMBLY (seat: pairup).
   Goal: assemble, EXPLICITLY via the foundation's pair-up parity lemma, the
   First-Supplement / Lagrange half of quadratic reciprocity:

     wsq : prime2 p ==> oeq (sub p 1) (add (add k k)(add k k))
           ==> cong p (mult w w) (sub p 1)              [w = lprod(upto (add k k))]
     qr  : prime2 p ==> oeq (sub p 1) (add (add k k)(add k k))
           ==> Ex x. cong p (mult x x) (sub p 1)

   i.e. for a prime p == 1 (mod 4)  (p-1 = 4k),  ((p-1)/2)! squared == -1 (mod p),
   so -1 is a quadratic residue mod p, with explicit witness x = w = ((p-1)/2)!.

   Built entirely on the foundation (`/tmp/qr_base_delta.sml`) which exposes, on
   the uprod-extended context ctxtU:
     - wilson_U     : Wilson's theorem (lprod(upto(p-1)) == p-1 == -1)
     - peel_U       : lprod(upto(add m k)) = uprod m k * lprod(upto m)   (SPLIT)
     - parity_crux_U: for p=2m+1, m EVEN (m=c+c), uprod m m == lprod(upto m)
                      (the SIGN-FREE PAIR-UP parity lemma; w == upper product)
     - p_eq_Suc_pred_U : prime2 p ==> p = Suc(sub p 1)
     - cong_* / oeq_* combinators on ctxtU.
   The assembly is THE pair-up argument written out:
     (p-1)! = lprod(upto(p-1))                         [Wilson statement subject]
            = lprod(upto(add m m))                     [p-1 = 4k = m+m, m=k+k]
            = uprod m m * w                            [PEEL at (m,m); w=lprod(upto m)]
            == w * w                                   [parity_crux: uprod m m == w]
     and  (p-1)! == p-1                                [WILSON]
     hence  w * w == p-1 == -1  (mod p).
   ============================================================================ *)
val () = out "NEG1QR_PAIRUP_BEGIN\n";

(* ----------------------------------------------------------------------------
   wsq : prime2 p ==> oeq (sub p 1) (add (add k k)(add k k))
                  ==> cong p (mult w w) (sub p 1)      [w = lprod(upto (add k k))]
   ---------------------------------------------------------------------------- *)
val wsq =
  let
    val pF  = Free("p", natT)
    val kF  = Free("k", natT)
    val one = suc ZeroC
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermU hPrimeP)
    (* m = k+k  (so m is EVEN with c = k);  p-1 = 4k = (k+k)+(k+k) = m+m. *)
    val mTerm = add kF kF
    val h4kP  = jT (oeq (sub pF one) (add mTerm mTerm))
    val h4k   = Thm.assume (ctermU h4kP)
    val w     = lprod (uptoF mTerm)                 (* w = ((p-1)/2)! = lprod(upto m) *)

    (* WILSON : cong p (lprod(upto(sub p 1))) (sub p 1)   [ (p-1)! == p-1 ] *)
    val congWil = wilson_U pF hPrime
    (* rewrite the (upto)-occurrence of (sub p 1) to (add m m):
       cong p (lprod(upto(add m m))) (sub p 1) *)
    val Pw1 = Term.lambda (Free("z_w1",natT))
                (cong pF (lprod (uptoF (Free("z_w1",natT)))) (sub pF one))
    val congWil2 = oeq_rw_U (Pw1, sub pF one, add mTerm mTerm) h4k congWil
       (* congWil2 : cong p (lprod(upto(add m m))) (sub p 1) *)

    (* PEEL at (m,m) : lprod(upto(add m m)) = uprod m m * w   (the SPLIT) *)
    val peelMM = peel_U (mTerm, mTerm)
       (* oeq (lprod(upto(add m m))) (mult (uprod m m) w) *)

    (* PARITY (the pair-up crux) : uprod m m == lprod(upto m) = w
       Needs p = Suc(add m m)  and  m = add c c (c = k, so refl). *)
    val pSucPred = p_eq_Suc_pred_U pF hPrime         (* p = Suc(sub p 1) *)
    val SubMM    = Suc_cong_U h4k                     (* Suc(sub p 1) = Suc(add m m) *)
    val pEqSucMM = oeq_trans_vU OF [pSucPred, SubMM]  (* p = Suc(add m m) *)
    val parC     = parity_crux_U (pF, mTerm, kF) pEqSucMM (oeqRefl_U mTerm)
       (* parC : cong p (uprod m m) w *)

    (* cong p (uprod m m * w) (w * w) via cong_mult parC (cong_refl w) *)
    val creflW   = cong_refl_U (pF, w)
    val congUWWW = cong_mult_U (pF, uprod mTerm mTerm, w, w, w) parC creflW
       (* cong p (uprod m m * w) (w * w) *)

    (* PEEL as a cong : cong p (lprod(upto(add m m))) (uprod m m * w) *)
    val congPeel = cong_of_eq_U (pF, lprod (uptoF (add mTerm mTerm)),
                                     mult (uprod mTerm mTerm) w) peelMM
    (* chain to w*w : cong p (lprod(upto(add m m))) (w*w) *)
    val congToWW = cong_trans_U (pF, lprod (uptoF (add mTerm mTerm)),
                                     mult (uprod mTerm mTerm) w, mult w w)
                     congPeel congUWWW
    (* flip + glue Wilson : w*w == lprod(upto(add m m)) == (p-1)  =>  w*w == p-1 *)
    val congWWtoLp = cong_sym_U (pF, lprod (uptoF (add mTerm mTerm)), mult w w) congToWW
       (* cong p (w*w) (lprod(upto(add m m))) *)
    val congWWsub  = cong_trans_U (pF, mult w w, lprod (uptoF (add mTerm mTerm)), sub pF one)
                       congWWtoLp congWil2
       (* cong p (mult w w) (sub p 1) *)

    val d2 = Thm.implies_intr (ctermU h4kP) congWWsub
    val d1 = Thm.implies_intr (ctermU hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of wsq) = 0 then out "OK wsq (0-hyp)\n" else out "FAIL wsq has hyps\n";
val () = out ("WSQ prop: " ^ Syntax.string_of_term ctxtU (Thm.prop_of wsq) ^ "\n");

(* ---- aconv-check wsq against its intended statement ---- *)
val pV   = Var(("p",0), natT);
val kV   = Var(("k",0), natT);
val oneV = suc ZeroC;
val mV   = add kV kV;
val wV   = lprod (uptoF mV);
val wsq_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
      jT (cong pV (mult wV wV) (sub pV oneV))));
val r_wsq = (length (Thm.hyps_of wsq) = 0)
            andalso ((Thm.prop_of wsq) aconv wsq_intended);
val () = if r_wsq
         then out "OK wsq aconv intended (0-hyp): prime p ==> p-1=4k ==> cong p (w*w) (p-1)\n"
         else (out ("FAIL wsq aconv\n  got      = "^Syntax.string_of_term ctxtU (Thm.prop_of wsq)^"\n"
                    ^"  intended = "^Syntax.string_of_term ctxtU wsq_intended^"\n"));

(* ---- soundness probes on wsq ---- *)
(* probe 1: wsq genuinely needs the prime hypothesis. *)
val wsq_BOGUS_noprime =
  Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
    jT (cong pV (mult wV wV) (sub pV oneV)));
val probe_wsq_prime = not ((Thm.prop_of wsq) aconv wsq_BOGUS_noprime);
val () = if probe_wsq_prime then out "PROBE_OK wsq keeps the prime hypothesis\n"
         else out "PROBE_FAIL wsq dropped the prime hypothesis\n";
(* probe 2: wsq genuinely needs the p==1 (mod 4) hypothesis. *)
val wsq_BOGUS_no4k =
  Logic.mk_implies (jT (prime2 pV),
    jT (cong pV (mult wV wV) (sub pV oneV)));
val probe_wsq_4k = not ((Thm.prop_of wsq) aconv wsq_BOGUS_no4k);
val () = if probe_wsq_4k then out "PROBE_OK wsq keeps the p==1(mod 4) hypothesis\n"
         else out "PROBE_FAIL wsq dropped the p==1(mod 4) hypothesis\n";
(* probe 3: wsq residue is (p-1) = -1, NOT 0. *)
val wsq_BOGUS_zero =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
      jT (cong pV (mult wV wV) ZeroC)));
val probe_wsq_zero = not ((Thm.prop_of wsq) aconv wsq_BOGUS_zero);
val () = if probe_wsq_zero then out "PROBE_OK wsq residue is (p-1)=-1, not 0\n"
         else out "PROBE_FAIL wsq residue collapsed to 0\n";

val () =
  if r_wsq andalso probe_wsq_prime andalso probe_wsq_4k andalso probe_wsq_zero
  then out "NEG1QR_WSQ_OK\n"
  else out "NEG1QR_WSQ_FAILED\n";

(* ----------------------------------------------------------------------------
   qr : prime2 p ==> oeq (sub p 1) (add (add k k)(add k k))
                 ==> Ex x. cong p (mult x x) (sub p 1)
   Existential introduction on wsq, witness x = w = lprod(upto (add k k)).
   ---------------------------------------------------------------------------- *)
val qr =
  let
    val pF  = Free("p", natT)
    val kF  = Free("k", natT)
    val one = suc ZeroC
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermU hPrimeP)
    val mTerm = add kF kF
    val h4kP  = jT (oeq (sub pF one) (add mTerm mTerm))
    val h4k   = Thm.assume (ctermU h4kP)
    val w     = lprod (uptoF mTerm)
    (* re-run wsq under the same assumptions (apply the proved wsq theorem) *)
    val congWWsub =
      let val inst = beta_norm (Drule.infer_instantiate ctxtU
            [(("p",0), ctermU pF),(("k",0), ctermU kF)] wsq)
      in Thm.implies_elim (Thm.implies_elim inst hPrime) h4k end
       (* cong p (mult w w) (sub p 1) *)
    val Pex = Term.lambda (Free("x_qr", natT))
                (cong pF (mult (Free("x_qr",natT)) (Free("x_qr",natT))) (sub pF one))
    val exX = exI_U Pex w congWWsub
    val d2  = Thm.implies_intr (ctermU h4kP) exX
    val d1  = Thm.implies_intr (ctermU hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of qr) = 0 then out "OK qr (0-hyp)\n" else out "FAIL qr has hyps\n";
val () = out ("QR prop: " ^ Syntax.string_of_term ctxtU (Thm.prop_of qr) ^ "\n");

(* ---- aconv-check qr against its intended statement ---- *)
val qr_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
      jT (mkEx (Term.lambda (Free("x_qr",natT))
            (cong pV (mult (Free("x_qr",natT))(Free("x_qr",natT))) (sub pV oneV))))));
val r_qr = (length (Thm.hyps_of qr) = 0)
           andalso ((Thm.prop_of qr) aconv qr_intended);
val () = if r_qr
         then out "OK qr aconv intended (0-hyp): prime p ==> p-1=4k ==> Ex x. cong p (x*x) (p-1)\n"
         else (out ("FAIL qr aconv\n  got      = "^Syntax.string_of_term ctxtU (Thm.prop_of qr)^"\n"
                    ^"  intended = "^Syntax.string_of_term ctxtU qr_intended^"\n"));

(* ---- soundness probes on qr ---- *)
(* probe 1: qr genuinely needs the prime hypothesis. *)
val qr_BOGUS_noprime =
  Logic.mk_implies (jT (oeq (sub pV oneV) (add mV mV)),
    jT (mkEx (Term.lambda (Free("x_qr",natT))
          (cong pV (mult (Free("x_qr",natT))(Free("x_qr",natT))) (sub pV oneV)))));
val probe_qr_prime = not ((Thm.prop_of qr) aconv qr_BOGUS_noprime);
val () = if probe_qr_prime then out "PROBE_OK qr keeps the prime hypothesis\n"
         else out "PROBE_FAIL qr dropped the prime hypothesis\n";
(* probe 2: qr genuinely needs the p==1 (mod 4) hypothesis. *)
val qr_BOGUS_no4k =
  Logic.mk_implies (jT (prime2 pV),
    jT (mkEx (Term.lambda (Free("x_qr",natT))
          (cong pV (mult (Free("x_qr",natT))(Free("x_qr",natT))) (sub pV oneV)))));
val probe_qr_4k = not ((Thm.prop_of qr) aconv qr_BOGUS_no4k);
val () = if probe_qr_4k then out "PROBE_OK qr keeps the p==1(mod 4) hypothesis\n"
         else out "PROBE_FAIL qr dropped the p==1(mod 4) hypothesis\n";

val () =
  if r_qr andalso probe_qr_prime andalso probe_qr_4k
  then out "NEG1QR_OK\n"
  else out "NEG1QR_FAILED\n";

(* ---- combined gate ---- *)
val () =
  if r_wsq andalso probe_wsq_prime andalso probe_wsq_4k andalso probe_wsq_zero
     andalso r_qr andalso probe_qr_prime andalso probe_qr_4k
  then out "NEG1QR_ALL_OK\n"
  else out "NEG1QR_ALL_FAILED\n";
