
(* ############################################################################
   ####  LATTICE-POINT SYMMETRY  +  QUADRATIC RECIPROCITY LAW  (fleet F3) ######
   APPENDED to (qr_f1_toolbox.sml ++ qr_f2_appendix.sml ++ qr_f2b_appendix.sml
                ++ qr_f2c_appendix.sml).
   The base ends at QR_F2C_ALL_OK / EIS_LEMMA_OK on ctxtU/ctermU/thyU.

   Banked on ctxtU (0-hyp + aconv) :
     eisenstein_lemma : prime2 p ==> parity p=1 ==> prime2 q ==> parity q=1 ==>
        ~(dvd p q) ==> (sub p 1 = m+m) ==>
        cong p (pow q m)(pow (sub p 1)(sumf (%k. rdiv(q*k) p) m))
     cnt P n / cnt_0 / cnt_Suc_t / cnt_Suc_f ; sumf f n / sumf_0 / sumf_Suc ;
     rdiv / rmod / div_mod_eq / rmod_lt ; le/lt order + le_or_lt ; euclid_lemma ;
     prime2_div / prime_not_dvd_mult ; not_dvd_in_range ; sum_cong / cnt_le / cnt_cong.

   Stages (each a GATED _OK marker ; graceful floor) :
     (FC) floor_as_count : 0<p ==> ~(dvd p B) ==> le (rdiv B p) n ==>
              cnt (%y. lt (mult p y) B) n = rdiv B p
     (ND) no_diagonal : prime2 p ==> prime2 q ==> ~(p=q) ==> 1<=k ==> k<=m ==>
              1<=y ==> y<=m2 ==> (p-1=m+m) ==> (q-1=m2+m2) ==>
              ~(oeq (mult p y)(mult q k))
     (CC) compl_count : cnt(%y. lt (mult p y) B) n + cnt(%y. lt B (mult p y)) n = n
              [when no point sits on B : %y. ~(oeq (mult p y) B)]
     (FU) fubini_swap : sum_k cnt_y(P k y) m2 = sum_y cnt_k(P k y) m  [rectangle double count]
     (LS) lattice_symmetry : sum (%k. rdiv(q*k) p) m + sum (%j. rdiv(p*j) q) m2 = m*m2
     (QR) qr_law : parity(sum floor_qp m + sum floor_pq m2) = parity(m*m2) TOGETHER WITH
              the eisenstein characterization of each symbol = the reciprocity law.
   ############################################################################ *)
val () = out "F3_BEGIN\n";

(* ----------------------------------------------------------------------------
   varify the remaining base lemmas onto ctxtU.
   ---------------------------------------------------------------------------- *)
val sum_cong_U_thm  = varifyU sum_cong;       (* (!!k. le k n ==> f k = g k) ==> sumf f n = sumf g n *)
val cnt_le_U_thm    = varifyU cnt_le;         (* le (cnt P n)(Suc n) *)
val cnt_cong_U_thm  = varifyU cnt_cong;       (* pred-equiv ==> cnt P n = cnt Q n *)
val mult_le_mono_U  = varifyU mult_le_mono;   (* le j k ==> le (mult c j)(mult c k) *)
val le_suc_mono_U   = varifyU le_suc_mono;    (* le m n ==> le (Suc m)(Suc n) *)
val rdiv_zero_U     = varifyU rdiv_zero;      (* lt 0 p ==> rdiv 0 p = 0 *)
val prime_not_dvd_mult_U = varifyU prime_not_dvd_mult;  (* prime2 p ==> ~dvd p a ==> ~dvd p k ==> ~dvd p (a*k) *)
val euclid_lemma_U  = varifyU euclid_lemma;   (* prime2 p ==> dvd p (a*b) ==> dvd p a \/ dvd p b *)
val le_total_U2     = varifyU le_total;
val le_add_mono_U   = varifyU le_add_mono;    (* le a b ==> le (add a c)(add b c) *)
val () = out "F3_VARIFY_DONE\n";

fun le_add_mono_at_U (aT, bT, cT) hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU aT),(("b",0), ctermU bT),(("c",0), ctermU cT)] le_add_mono_U)) hle;
(* le_add_mono_l_U : le a b ==> le (add c a)(add c b)  via comm of the right-version *)
fun le_add_mono_l_U (cT, aT, bT) hle =
  let
    val r = le_add_mono_at_U (aT, bT, cT) hle;   (* le (add a c)(add b c) *)
    val c1 = addcomm_U (aT, cT);                  (* (a+c)=(c+a) *)
    val c2 = addcomm_U (bT, cT);                  (* (b+c)=(c+b) *)
    val r1 = oeq_rw_U (Term.lambda (Free("zl1", natT)) (le (Free("zl1", natT)) (add bT cT)), add aT cT, add cT aT) c1 r;
    val r2 = oeq_rw_U (Term.lambda (Free("zl2", natT)) (le (add cT aT) (Free("zl2", natT))), add bT cT, add cT bT) c2 r1;
  in r2 end;

(* ground instantiators on ctxtU *)
fun cntLe_U (Pt, nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("P",0), ctermU Pt),(("n",0), ctermU nt)] cnt_le_U_thm);
fun multLeMono_U (cT, jT_, kT) hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("c",0), ctermU cT),(("j",0), ctermU jT_),(("k",0), ctermU kT)] mult_le_mono_U)) hle;
fun leSucMono_U (mt,nt) hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] le_suc_mono_U)) hle;
fun rdivZero_U pt hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt)] rdiv_zero_U)) hpos;
fun primeNotDvdMult_U (pt,at,kt) hPr hNa hNk =
  Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt),(("a",0), ctermU at),(("k",0), ctermU kt)] prime_not_dvd_mult_U)) hPr) hNa) hNk;
fun euclid_U (pt,at,bt) hPr hDvd =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt),(("a",0), ctermU at),(("b",0), ctermU bt)] euclid_lemma_U)) hPr) hDvd;

(* sum_cong on ctxtU : congProof : (!!k. le k n ==> f k = g k) -> sumf f n = sumf g n *)
fun sum_cong_U (fAbs, gAbs, nt) congProof =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("f",0), ctermU fAbs),(("g",0), ctermU gAbs),(("n",0), ctermU nt)] sum_cong_U_thm)
  in Thm.implies_elim inst congProof end;

(* cnt_cong on ctxtU : congProofFwd : (!!k. P(Suc k) ==> Q(Suc k)),
                       congProofBwd : (!!k. Q(Suc k) ==> P(Suc k)) -> cnt P n = cnt Q n *)
fun cnt_cong_U (Pabs, Qabs, nt) fwd bwd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("Q",0), ctermU Qabs),(("n",0), ctermU nt)] cnt_cong_U_thm)
  in Thm.implies_elim (Thm.implies_elim inst fwd) bwd end;

(* extra arithmetic instantiators *)
fun multSuc_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] mult_Suc_U);   (* mult (Suc m) n = add n (mult m n) *)
val mult_Suc_right_U = varifyU mult_Suc_right;   (* oeq (mult n (Suc m))(add n (mult n m)) *)
fun multSucR_U (nt,mt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("n",0), ctermU nt),(("m",0), ctermU mt)] mult_Suc_right_U);  (* mult n (Suc m) = add n (mult n m) *)
fun multcomm_U2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] mult_comm_U);
fun mult0r_U2 t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] mult_0_right_U);

val () = out "F3_INSTANTIATORS_READY\n";

(* prime2 div elim on ctxtU : prime2 p ==> dvd d p ==> Disj (oeq d 1)(oeq d p) *)
val prime2_div_U = varifyU (
  let
    val pF = Free("p", natT); val dF = Free("d", natT);
    val hPr = Thm.assume (ctermU (jT (prime2 pF)));
    val hDvd = Thm.assume (ctermU (jT (dvd dF pF)));
    val faThm = conjunct2_U_at (lt (suc ZeroC) pF, mkForall (ppAbs pF)) hPr;
    val impAt = allE_U_at (ppAbs pF) dF faThm;
    val res = mp_U_at (dvd dF pF, mkDisj (oeq dF (suc ZeroC))(oeq dF pF)) impAt hDvd;
    val d2 = Thm.implies_intr (ctermU (jT (dvd dF pF))) res;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in d1 end);
fun prime2_div_atU (pt, dt) hPr hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("d",0), ctermU dt)] prime2_div_U)
  in Thm.implies_elim (Thm.implies_elim inst hPr) hDvd end;
val () = out "F3_PRIME2DIV_READY\n";

(* ############################################################################
   (FC)  floor_as_count
   For 0<p, p does NOT divide B, and le (rdiv B p) n :
       cnt (%y. lt (mult p y) B) n = rdiv B p.
   Proof : the predicate (%y. lt (mult p y) B) is EQUIVALENT on 1..n to
   (%y. le y (rdiv B p)) [the threshold map], then cnt of the threshold equals
   the threshold when le thresh n.
   ############################################################################ *)
val () = out "FC_BEGIN\n";

(* ---- (FC.a) the bridge : 0<p ==> ~(dvd p B) ==> ( lt (p*y) B  <->  le y (rdiv B p) ) ----
   Forward  : lt (p*y) B ==> le y Q     (Q = rdiv B p)
   Backward : le y Q ==> lt (p*y) B
   uses B = p*Q + R, R<p, R>0 (from ~dvd). *)

(* helper : le a b ==> le (Suc a) b \/ oeq a b ... we actually use le_or_lt + arithmetic.
   We build le y Q  <->  lt (p*y) B  by the two implications. *)

(* lt (p*Q) B from R>0 :  B = p*Q + R, and p*Q < p*Q + R because R = Suc r0.
   ~(dvd p B) gives R<>0. *)

(* The cleanest path : prove  lt (p*y) B  <->  le y Q  via le_or_lt (y) (Q):
     case le y Q : p*y <= p*Q (mult_le_mono) ; p*Q < B (since R>0) ; so p*y < B.
     case lt Q y i.e. le (Suc Q) y : p*(Suc Q) <= p*y ; B < p*(Suc Q) (since R<p) ; so B < p*y, hence ~(p*y < B). *)

(* We need : R<>0  i.e.  lt 0 R.  From ~(dvd p B) : if R=0 then B = p*Q so dvd p B. *)
fun R_pos_of_ndvd (pt, Bt) hpos hNdvd =
  (* hpos : lt 0 p ; hNdvd : ~(dvd p B) ; conclude lt 0 (rmod B p) *)
  let
    val Q = rdiv Bt pt; val R = rmod Bt pt;
    val divEq = div_mod_eq_U_at (Bt, pt) hpos;   (* oeq B (add (mult p Q) R) *)
    (* ~(oeq R 0) : if R=0 then B = p*Q so dvd p B, contradiction. *)
    val cZ =
      let val hR0 = Thm.assume (ctermU (jT (oeq R ZeroC)))
          val rwR = oeq_rw_U (Term.lambda (Free("z_rp", natT)) (oeq Bt (add (mult pt Q) (Free("z_rp", natT)))),
                      R, ZeroC) hR0 divEq;       (* oeq B (add (mult p Q) 0) *)
          val a0 = add0r_U (mult pt Q);          (* (p*Q + 0) = p*Q *)
          val Beq = oeq_trans_U OF [rwR, a0];    (* oeq B (mult p Q) *)
          val dAbs = Abs("k", natT, oeq Bt (mult pt (Bound 0)));
          val dvdPB = exI_U_at (dAbs, Q) Beq;    (* dvd p B *)
          val ff = mp_U_at (dvd pt Bt, oFalseC) hNdvd dvdPB;  (* oFalse *)
      in ff end;
    val nR0 = impI_U_at (oeq R ZeroC, oFalseC) (Thm.implies_intr (ctermU (jT (oeq R ZeroC))) cZ);  (* ~(oeq R 0) *)
    (* le 0 R *)
    val le0R = let val a0R = add0_U R                  (* (0+R)=R *)
                   val laR = le_add_U_at (ZeroC, R)    (* le 0 (0+R) *)
               in oeq_rw_U (Term.lambda (Free("z_le", natT)) (le ZeroC (Free("z_le", natT))), add ZeroC R, R) a0R laR end;
    (* neg (oeq 0 R) from neg (oeq R 0) by sym *)
    val neq0R =
      let val heq = Thm.assume (ctermU (jT (oeq ZeroC R)))
          val sm = oeq_sym_U OF [heq]   (* oeq R 0 *)
          val ff = mp_U_at (oeq R ZeroC, oFalseC) nR0 sm
      in impI_U_at (oeq ZeroC R, oFalseC) (Thm.implies_intr (ctermU (jT (oeq ZeroC R))) ff) end;
  in le_neq_lt_U_at (ZeroC, R) le0R neq0R end   (* lt 0 R *)
val () = out "FC_RPOS_READY\n";

(* le_antisym on ctxtU *)
val le_antisym_U = varifyU le_antisym;
fun le_antisym_atU (mT, nT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mT),(("n",0), ctermU nT)] le_antisym_U)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* le_zero_U : le t 0 ==> oeq t 0 *)
fun le_zero_U tT hle =
  let
    val Pabs = Abs("p", natT, oeq ZeroC (add tT (Bound 0)));
    fun body w (hw:thm) =     (* hw : oeq 0 (add t w) *)
      let val sm = oeq_sym_U OF [hw]      (* oeq (add t w) 0 *)
      in add_eq_zero_left_U_at (tT, w) sm end;  (* oeq t 0 *)
  in exE_U_at (Pabs, oeq tT ZeroC) hle "w_lz0" body end;

(* lt-to-le-Suc :  lt a b  IS  le (Suc a) b   (definitional ; lt a b = le (suc a) b) *)
(* le_of_lt_suc_U : lt t (Suc x) ==> le t x  (via lt_suc_cases) *)
val lt_suc_cases_U = varifyU lt_suc_cases;   (* lt m (Suc n) ==> Disj (lt m n)(oeq m n) *)
fun lt_suc_cases_atU (mT, nT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mT),(("n",0), ctermU nT)] lt_suc_cases_U)) h;
val le_refl_U3 = varifyU le_refl;
fun le_refl_atU3 t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] le_refl_U3);
fun le_of_lt_suc_U (tT, xT) h =   (* h : lt t (Suc x) -> le t x *)
  let
    val dis = lt_suc_cases_atU (tT, xT) h;   (* Disj (lt t x)(oeq t x) *)
    val cLt =
      let val hlt = Thm.assume (ctermU (jT (lt tT xT)))   (* le (Suc t) x *)
          val lts = le_self_suc_U tT                       (* le t (Suc t) *)
          val res = le_trans_U_at (tT, suc tT, xT) lts hlt (* le t x *)
      in Thm.implies_intr (ctermU (jT (lt tT xT))) res end;
    val cEq =
      let val heq = Thm.assume (ctermU (jT (oeq tT xT)))
          val refl = le_refl_atU3 tT                        (* le t t *)
          val res = oeq_rw_U (Term.lambda (Free("z_los", natT)) (le tT (Free("z_los", natT))), tT, xT) heq refl
      in Thm.implies_intr (ctermU (jT (oeq tT xT))) res end;
  in disjE_U_at (lt tT xT, oeq tT xT, le tT xT) dis cLt cEq end;

(* ============================================================================
   count-all : le n t ==> cnt (%y. le y t) n = n
   (every index 1..n is below-or-equal the threshold t)
   ============================================================================ *)
fun thrAbs t = let val yy = Free("y_thr_fr", natT) in Term.lambda yy (le yy t) end;  (* %y. le y t (capture-safe) *)
val () = out "FC_THRABS_READY\n";

(* count_all as a genuine induction lemma, schematic in t and n after varify : *)
val count_all_lemma =
  let
    val tF = Free("t_ca", natT);
    val P = thrAbs tF;
    val zF = Free("z_ca", natT);
    (* predicate for induction on n : %n. le n t --> cnt P n = n  (object impl) *)
    val Pind = Term.lambda zF (mkImp (le zF tF) (oeq (cnt P zF) zF));
    val nF = Free("n_ca", natT);
    (* BASE n=0 : le 0 t --> cnt P 0 = 0 *)
    val base =
      let
        val h0 = Thm.assume (ctermU (jT (le ZeroC tF)));
        val c0 = cnt0_U P;                       (* cnt P 0 = 0 *)
        val body = c0;                           (* oeq (cnt P 0) 0 *)
      in impI_U_at (le ZeroC tF, oeq (cnt P ZeroC) ZeroC)
            (Thm.implies_intr (ctermU (jT (le ZeroC tF))) body) end;
    (* STEP : IH (le x t --> cnt P x = x) ; show le (Suc x) t --> cnt P (Suc x) = Suc x *)
    val xF = Free("x_ca", natT);
    val ihC = mkImp (le xF tF) (oeq (cnt P xF) xF);
    val IH  = Thm.assume (ctermU (jT ihC));
    val step =
      let
        val hSx = Thm.assume (ctermU (jT (le (suc xF) tF)));    (* le (Suc x) t *)
        (* predicate at Suc x : le (Suc x) t -- HOLDS *)
        val hPred = hSx;                                        (* le (Suc x) t = P (Suc x) by beta *)
        val ceq = cntSucT_U (P, xF) hPred;                      (* cnt P (Suc x) = Suc (cnt P x) *)
        (* le x t from le (Suc x) t : le x (Suc x) ; le_trans *)
        val lexSx = le_self_suc_U xF;                           (* le x (Suc x) *)
        val lext = le_trans_U_at (xF, suc xF, tF) lexSx hSx;    (* le x t *)
        val ihApp = mp_U_at (le xF tF, oeq (cnt P xF) xF) IH lext;  (* cnt P x = x *)
        (* cnt P (Suc x) = Suc(cnt P x) = Suc x *)
        val sucCnt = Succong_U ihApp;                          (* Suc(cnt P x) = Suc x *)
        val res = oeq_trans_U OF [ceq, sucCnt];                (* cnt P (Suc x) = Suc x *)
      in impI_U_at (le (suc xF) tF, oeq (cnt P (suc xF)) (suc xF))
            (Thm.implies_intr (ctermU (jT (le (suc xF) tF))) res) end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihC)) step);
    val run = nat_induct_U_run Pind nF base stepF;   (* le n t --> cnt P n = n  for the Free n *)
  in varify run end;   (* schematic in ?t_ca ?n_ca : le ?n ?t --> cnt(%y.le y ?t) ?n = ?n *)
val () = out "FC_COUNTALL_READY\n";

(* count_all_at (t, n) hle : hle : le n t -> oeq (cnt (thrAbs t) n) n *)
fun count_all_at (tT, nT) hle =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtU
          [(("t_ca",0), ctermU tT),(("n_ca",0), ctermU nT)] count_all_lemma);
    (* inst : jT (mkImp (le n t)(oeq (cnt (thrAbs t) n) n)) *)
  in mp_U_at (le nT tT, oeq (cnt (thrAbs tT) nT) nT) inst hle end;

(* ============================================================================
   count_thresh : le t n ==> cnt (%y. le y t) n = t
   (the threshold count : exactly t indices in 1..n are <= t)
   By induction on n with general t.  Uses count_all for the t=Suc n branch.
   ============================================================================ *)
val count_thresh_lemma =
  let
    val tF = Free("t_ct", natT);
    val P = thrAbs tF;
    val zF = Free("z_ct", natT);
    val Pind = Term.lambda zF (mkImp (le tF zF) (oeq (cnt P zF) tF));
    val nF = Free("n_ct", natT);
    (* BASE n=0 : le t 0 --> cnt P 0 = t.  le t 0 => t=0 ; cnt P 0 = 0 = t *)
    val base =
      let
        val h0 = Thm.assume (ctermU (jT (le tF ZeroC)));
        val t0 = le_zero_U tF h0;                  (* oeq t 0 *)
        val c0 = cnt0_U P;                         (* cnt P 0 = 0 *)
        val res = oeq_trans_U OF [c0, oeq_sym_U OF [t0]];  (* cnt P 0 = t *)
      in impI_U_at (le tF ZeroC, oeq (cnt P ZeroC) tF)
            (Thm.implies_intr (ctermU (jT (le tF ZeroC))) res) end;
    (* STEP : IH (le t x --> cnt P x = t) ; show le t (Suc x) --> cnt P (Suc x) = t *)
    val xF = Free("x_ct", natT);
    val ihC = mkImp (le tF xF) (oeq (cnt P xF) tF);
    val IH  = Thm.assume (ctermU (jT ihC));
    val step =
      let
        val hSx = Thm.assume (ctermU (jT (le tF (suc xF))));   (* le t (Suc x) *)
        (* case-split on  le (Suc x) t   vs   lt t (Suc x)  (= le (Suc t)(Suc x) = le t x) *)
        val tri = le_or_lt_U (suc xF, tF);   (* Disj (le (Suc x) t)(lt t (Suc x)) *)
        val goalS = oeq (cnt P (suc xF)) tF;
        (* CASE A : le (Suc x) t -> with le t (Suc x) -> t = Suc x (le_antisym) *)
        val cA =
          let
            val hA = Thm.assume (ctermU (jT (le (suc xF) tF)));   (* le (Suc x) t *)
            val tEq = le_antisym_atU (tF, suc xF) hSx hA;         (* oeq t (Suc x) *)
            (* predicate at Suc x : le (Suc x) t -- HOLDS (= hA) *)
            val ceq = cntSucT_U (P, xF) hA;                        (* cnt P (Suc x) = Suc(cnt P x) *)
            (* count_all at (t, x) with le x t :  le x (Suc x)=le x t? need le x t.
               from t = Suc x : le x t  iff le x (Suc x) which holds. *)
            val lxSx = le_self_suc_U xF;                          (* le x (Suc x) *)
            val lxt  = oeq_rw_U (Term.lambda (Free("zz_ct", natT)) (le xF (Free("zz_ct", natT))),
                          suc xF, tF) (oeq_sym_U OF [tEq]) lxSx;   (* le x t *)
            val caX = count_all_at (tF, xF) lxt;                  (* cnt P x = x *)
            val sucCnt = Succong_U caX;                           (* Suc(cnt P x) = Suc x *)
            val res1 = oeq_trans_U OF [ceq, sucCnt];              (* cnt P (Suc x) = Suc x *)
            val res = oeq_trans_U OF [res1, oeq_sym_U OF [tEq]];  (* cnt P (Suc x) = t *)
          in Thm.implies_intr (ctermU (jT (le (suc xF) tF))) res end;
        (* CASE B : lt t (Suc x) = le (Suc t)(Suc x).  pred at Suc x is FALSE : ~(le (Suc x) t). *)
        val cB =
          let
            val hB = Thm.assume (ctermU (jT (lt tF (suc xF))));   (* le (Suc t)(Suc x) *)
            (* le t x : from lt t (Suc x) via lt_suc_cases. *)
            val letx = le_of_lt_suc_U (tF, xF) hB;    (* le t x *)
            val notP =
              let
                val hP = Thm.assume (ctermU (jT (le (suc xF) tF)));   (* le (Suc x) t *)
                val le_Sx_x = le_trans_U_at (suc xF, tF, xF) hP letx; (* le (Suc x) x = lt x x *)
                val ff = lt_irrefl_U_at xF le_Sx_x;                   (* oFalse *)
              in impI_U_at (le (suc xF) tF, oFalseC)
                    (Thm.implies_intr (ctermU (jT (le (suc xF) tF))) ff) end;  (* ~(le (Suc x) t) *)
            val ceq = cntSucF_U (P, xF) notP;        (* cnt P (Suc x) = cnt P x *)
            val ihApp = mp_U_at (le tF xF, oeq (cnt P xF) tF) IH letx;  (* cnt P x = t *)
            val res = oeq_trans_U OF [ceq, ihApp];   (* cnt P (Suc x) = t *)
          in Thm.implies_intr (ctermU (jT (lt tF (suc xF)))) res end;
        val concl = disjE_U_at (le (suc xF) tF, lt tF (suc xF), goalS) tri cA cB;
      in impI_U_at (le tF (suc xF), oeq (cnt P (suc xF)) tF)
            (Thm.implies_intr (ctermU (jT (le tF (suc xF)))) concl) end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihC)) step);
    val run = nat_induct_U_run Pind nF base stepF;
  in varify run end;
val () = out "FC_COUNTTHRESH_READY\n";

fun count_thresh_at (tT, nT) hle =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtU
          [(("t_ct",0), ctermU tT),(("n_ct",0), ctermU nT)] count_thresh_lemma);
  in mp_U_at (le tT nT, oeq (cnt (thrAbs tT) nT) tT) inst hle end;

(* ============================================================================
   (FC.bridge)  for 0<p, ~(dvd p B) :   lt (mult p y) B  <->  le y (rdiv B p)
   ============================================================================ *)
(* bridge_bwd : le y Q ==> lt (p*y) B   (Q=rdiv B p, R=rmod B p, R>0) *)
fun bridge_bwd (pt, Bt) hpos hNdvd yT hle =
  let
    val Q = rdiv Bt pt; val R = rmod Bt pt;
    val divEq = div_mod_eq_U_at (Bt, pt) hpos;   (* oeq B (add (mult p Q) R) *)
    val Rpos  = R_pos_of_ndvd (pt, Bt) hpos hNdvd;  (* lt 0 R = le (Suc 0) R *)
    (* p*y <= p*Q  (mult_le_mono, le y Q) *)
    val lepy = multLeMono_U (pt, yT, Q) hle;        (* le (p*y)(p*Q) *)
    (* p*Q < B : B = p*Q + R, R>0 => p*Q < p*Q + R = B.
       lt (p*Q)(p*Q + R) : le (Suc(p*Q))(p*Q+R).  R = Suc r0 (from R>0=le(Suc0)R).
       Use : le (Suc(p*Q)) (add (p*Q) R)  since R>=1.  Build witness. *)
    (* lt (p*Q) B  via : oeq B (p*Q + R) and le (Suc(p*Q))(p*Q+R). *)
    val pQR = add (mult pt Q) R;
    (* le (Suc(p*Q))(p*Q + R) : need (p*Q+R) = Suc(p*Q) + w for some w.
       R = Suc r0 ; from Rpos = le (Suc 0) R = Ex w. R = Suc 0 + w. destruct. *)
    val ltpQB =
      let
        val Pabs = Abs("w", natT, oeq R (add (suc ZeroC) (Bound 0)));
        fun body w (hw:thm) =   (* hw : oeq R (add (Suc 0) w) = oeq R (Suc(0+w)) ; R = Suc w' essentially *)
          let
            (* R = (Suc 0) + w = Suc(0 + w) = Suc w *)
            val aS = addSuc_U (ZeroC, w);        (* (Suc 0 + w) = Suc(0+w) *)
            val a0 = add0_U w;                   (* (0+w)=w *)
            val sa0 = Succong_U a0;              (* Suc(0+w)=Suc w *)
            val Req = oeq_trans_U OF [oeq_trans_U OF [hw, aS], sa0];  (* R = Suc w *)
            (* p*Q + R = p*Q + Suc w = Suc(p*Q + w) = Suc(p*Q) + w  -- want (p*Q+R) = Suc(p*Q) + w *)
            val rwR = oeq_rw_U (Term.lambda (Free("zb", natT)) (oeq (add (mult pt Q) R) (add (mult pt Q) (Free("zb", natT)))),
                        R, suc w) Req (oeqRefl_U (add (mult pt Q) R));  (* (p*Q+R) = (p*Q + Suc w) *)
            val aSr = addSr_U (mult pt Q, w);    (* (p*Q + Suc w) = Suc(p*Q + w) *)
            val aSl = addSuc_U (mult pt Q, w);   (* (Suc(p*Q) + w) = Suc(p*Q + w) *)
            val chain = oeq_trans_U OF [oeq_trans_U OF [rwR, aSr], oeq_sym_U OF [aSl]];
                        (* (p*Q + R) = (Suc(p*Q) + w) *)
            (* le (Suc(p*Q))(p*Q+R) via le_intro_U (Suc(p*Q), p*Q+R, w) *)
            val lewit = le_intro_U (suc (mult pt Q), add (mult pt Q) R, w) chain;  (* le (Suc(p*Q))(p*Q+R) *)
            (* rewrite (p*Q + R) -> B by sym divEq *)
            val ltB = oeq_rw_U (Term.lambda (Free("zc", natT)) (le (suc (mult pt Q)) (Free("zc", natT))),
                        pQR, Bt) (oeq_sym_U OF [divEq]) lewit;   (* le (Suc(p*Q)) B = lt (p*Q) B *)
          in ltB end;
      in exE_U_at (Pabs, lt (mult pt Q) Bt) Rpos "w_rpos" body end;   (* lt (p*Q) B *)
    (* p*y <= p*Q < B  => p*y < B : le (p*y)(p*Q) and lt (p*Q) B = le (Suc(p*Q)) B.
       le (p*y)(p*Q) -> le (Suc(p*y))(Suc(p*Q)) ; le (Suc(p*Q)) B ; le_trans -> le (Suc(p*y)) B = lt (p*y) B. *)
    val leSpy = leSucMono_U (mult pt yT, mult pt Q) lepy;   (* le (Suc(p*y))(Suc(p*Q)) *)
    (* lt (p*Q) B = le (Suc(p*Q)) B ; need le (Suc(p*y)) B.
       le (Suc(p*y))(Suc(p*Q)) and le (Suc(p*Q)) B ... but ltpQB is le (Suc(p*Q)) B. compose. *)
    val res = le_trans_U_at (suc (mult pt yT), suc (mult pt Q), Bt) leSpy ltpQB;  (* le (Suc(p*y)) B = lt (p*y) B *)
  in res end;
val () = out "FC_BRIDGE_BWD_READY\n";

(* bridge_fwd : lt (p*y) B ==> le y Q   (Q=rdiv B p, R<p) *)
fun bridge_fwd (pt, Bt) hpos hNdvd yT hlt =
  let
    val Q = rdiv Bt pt; val R = rmod Bt pt;
    val divEq = div_mod_eq_U_at (Bt, pt) hpos;   (* oeq B (add (mult p Q) R) *)
    val Rltp  = rmod_lt_U_at (Bt, pt) hpos;       (* lt R p = le (Suc R) p *)
    (* le_or_lt y Q : Disj (le y Q)(lt Q y) *)
    val tri = le_or_lt_U (yT, Q);
    val cA = Thm.implies_intr (ctermU (jT (le yT Q))) (Thm.assume (ctermU (jT (le yT Q))));  (* le y Q -> le y Q *)
    val cB =
      let
        val hQy = Thm.assume (ctermU (jT (lt Q yT)));    (* le (Suc Q) y *)
        (* p*(Suc Q) <= p*y *)
        val lepSQy = multLeMono_U (pt, suc Q, yT) hQy;   (* le (p*(Suc Q))(p*y) *)
        (* B < p*(Suc Q) : B = p*Q+R, R<p => p*Q+R < p*Q+p = p*(Suc Q).
           lt B (p*(Suc Q)) = le (Suc B)(p*(Suc Q)).
           p*(Suc Q) = p*Q + p (mult_Suc gives p*(Suc Q) = p + p*Q ; comm). *)
        val pSQ_pPpQ = multSucR_U (pt, Q);   (* oeq (mult p (Suc Q)) (add p (mult p Q)) *)
        (* lt B (p*(Suc Q)) : le (Suc B)(p*(Suc Q)).  B = p*Q + R, Suc R <= p (Rltp).
           Suc B = Suc(p*Q + R) = p*Q + Suc R (add_Suc_right).  le (p*Q + Suc R)(p*Q + p)? 
           via le_add_mono on (Suc R <= p) added on left p*Q. then = add p (p*Q) by comm = p*(Suc Q). *)
        (* Suc B = Suc(p*Q + R) ; rewrite B -> (p*Q + R) first *)
        val SucB_eq1 = Succong_U divEq;          (* Suc B = Suc(p*Q + R) *)
        val aSr = addSr_U (mult pt Q, R);        (* (p*Q + Suc R) = Suc(p*Q + R) *)
        val SucB_eq = oeq_trans_U OF [SucB_eq1, oeq_sym_U OF [aSr]];  (* Suc B = (p*Q + Suc R) *)
        (* le (p*Q + Suc R)(p*Q + p) via le_add_mono_left : from le (Suc R) p add p*Q on left.
           use add_le_mono_l : le a b ==> le (add c a)(add c b). search/derive via le_add_mono.
           We have le_add_mono : le a b ==> le (add a c)(add b c) (RIGHT add).  Use comm. *)
        val leSRp = Rltp;                         (* le (Suc R) p *)
        val le_add = le_add_mono_l_U (mult pt Q, suc R, pt) leSRp;  (* le (p*Q + Suc R)(p*Q + p) *)
        (* (p*Q + p) = (p + p*Q) = p*(Suc Q) *)
        val cpQp = addcomm_U (mult pt Q, pt);     (* (p*Q + p) = (p + p*Q) *)
        val toMSucQ = oeq_trans_U OF [cpQp, oeq_sym_U OF [pSQ_pPpQ]];  (* (p*Q + p) = p*(Suc Q) *)
        val le2 = oeq_rw_U (Term.lambda (Free("zm", natT)) (le (add (mult pt Q)(suc R)) (Free("zm", natT))),
                    add (mult pt Q) pt, mult pt (suc Q)) toMSucQ le_add;   (* le (p*Q + Suc R)(p*(Suc Q)) *)
        val leSucB = oeq_rw_U (Term.lambda (Free("zn", natT)) (le (Free("zn", natT)) (mult pt (suc Q))),
                    add (mult pt Q)(suc R), suc Bt) (oeq_sym_U OF [SucB_eq]) le2;   (* le (Suc B)(p*(Suc Q)) = lt B (p*(Suc Q)) *)
        (* now lt B (p*(Suc Q)) and le (p*(Suc Q))(p*y) -> lt B (p*y) = le (Suc B)(p*y) *)
        val ltBpy = le_trans_U_at (suc Bt, mult pt (suc Q), mult pt yT) leSucB lepSQy;  (* le (Suc B)(p*y) = lt B (p*y) *)
        (* but hlt : lt (p*y) B = le (Suc(p*y)) B.  lt B (p*y) and lt (p*y) B -> contradiction.
           le (Suc B)(p*y) and le (Suc(p*y)) B : le (Suc(p*y)) B -> le (p*y) B (drop? no).
           lt (p*y) B = le (Suc(p*y)) B ; lt B (p*y) = le (Suc B)(p*y).
           le (Suc(p*y)) B and le B ... we have le (Suc B)(p*y). 
           From le (Suc(p*y)) B : le (p*y) B via le_self_suc trans? le (p*y)(Suc(p*y)) and le(Suc(p*y))B -> le (p*y) B.
           Then le (Suc B)(p*y) and le (p*y) B -> le (Suc B) B = lt B B -> oFalse. *)
        val le_py_Spy = le_self_suc_U (mult pt yT);          (* le (p*y)(Suc(p*y)) *)
        val le_py_B = le_trans_U_at (mult pt yT, suc (mult pt yT), Bt) le_py_Spy hlt;  (* le (p*y) B *)
        val le_SB_B = le_trans_U_at (suc Bt, mult pt yT, Bt) ltBpy le_py_B;   (* le (Suc B) B = lt B B *)
        val ff = lt_irrefl_U_at Bt le_SB_B;                  (* oFalse *)
        val anyGoal = oFalse_elim_U_at (le yT Q);            (* oFalse -> le y Q *)
        val res = Thm.implies_elim anyGoal ff;               (* le y Q *)
      in Thm.implies_intr (ctermU (jT (lt Q yT))) res end;
  in disjE_U_at (le yT Q, lt Q yT, le yT Q) tri cA cB end;
val () = out "FC_BRIDGE_FWD_READY\n";

(* ============================================================================
   (FC)  floor_as_count :
     0<p ==> ~(dvd p B) ==> le (rdiv B p) n ==>
        cnt (%y. lt (mult p y) B) n = rdiv B p
   ============================================================================ *)
fun ltPredAbs (pt, Bt) = let val yy = Free("y_lt_fr", natT) in Term.lambda yy (lt (mult pt yy) Bt) end;  (* %y. lt (p*y) B (capture-safe) *)
val floor_as_count =
  let
    val pF = Free("p_fc", natT); val BF = Free("B_fc", natT); val nF = Free("n_fc", natT);
    val Q = rdiv BF pF;
    val hpos  = Thm.assume (ctermU (jT (lt ZeroC pF)));
    val hNdvd = Thm.assume (ctermU (jT (neg (dvd pF BF))));
    val hBnd  = Thm.assume (ctermU (jT (le Q nF)));
    val Plt = ltPredAbs (pF, BF);       (* %y. lt (p*y) B *)
    val Qth = thrAbs Q;                  (* %y. le y Q *)
    (* cnt_cong : cnt Plt n = cnt Qth n  via bridge fwd/bwd at Suc k *)
    val kF = Free("k_fc", natT);
    (* fwd : !!k. Imp (Plt(Suc k))(Qth(Suc k))  [OBJECT impl, as cnt_cong expects] *)
    val fwd =
      let
        val hP = Thm.assume (ctermU (jT (lt (mult pF (suc kF)) BF)));    (* = Plt(Suc k) *)
        val res = bridge_fwd (pF, BF) hpos hNdvd (suc kF) hP;            (* le (Suc k) Q = Qth(Suc k) *)
        val obj = impI_U_at (lt (mult pF (suc kF)) BF, le (suc kF) Q)
                    (Thm.implies_intr (ctermU (jT (lt (mult pF (suc kF)) BF))) res);  (* Imp (Plt(Suc k))(Qth(Suc k)) *)
      in Thm.forall_intr (ctermU kF) obj end;
    (* bwd : !!k. Imp (Qth(Suc k))(Plt(Suc k)) *)
    val bwd =
      let
        val hQ = Thm.assume (ctermU (jT (le (suc kF) Q)));              (* = Qth(Suc k) *)
        val res = bridge_bwd (pF, BF) hpos hNdvd (suc kF) hQ;           (* lt (p*(Suc k)) B = Plt(Suc k) *)
        val obj = impI_U_at (le (suc kF) Q, lt (mult pF (suc kF)) BF)
                    (Thm.implies_intr (ctermU (jT (le (suc kF) Q))) res);  (* Imp (Qth(Suc k))(Plt(Suc k)) *)
      in Thm.forall_intr (ctermU kF) obj end;
    val cntEq = cnt_cong_U (Plt, Qth, nF) fwd bwd;     (* cnt Plt n = cnt Qth n *)
    val cthr  = count_thresh_at (Q, nF) hBnd;          (* cnt Qth n = Q *)
    val res0  = oeq_trans_U OF [cntEq, cthr];          (* cnt Plt n = Q *)
    val d3 = Thm.implies_intr (ctermU (jT (le Q nF))) res0;
    val d2 = Thm.implies_intr (ctermU (jT (neg (dvd pF BF)))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (lt ZeroC pF))) d2;
  in varify d1 end;
val () = out "FC_RAW_DONE\n";

(* validate FC *)
val pV_fc = Var(("p_fc",0),natT); val BV_fc = Var(("B_fc",0),natT); val nV_fc = Var(("n_fc",0),natT);
val i_floor_as_count =
  Logic.mk_implies (jT (lt ZeroC pV_fc),
    Logic.mk_implies (jT (neg (dvd pV_fc BV_fc)),
      Logic.mk_implies (jT (le (rdiv BV_fc pV_fc) nV_fc),
        jT (oeq (cnt (ltPredAbs (pV_fc, BV_fc)) nV_fc) (rdiv BV_fc pV_fc)))));
val r_floor_as_count = checkF2c ("floor_as_count", floor_as_count, i_floor_as_count);
val () = if r_floor_as_count then out "FLOOR_AS_COUNT_OK\n" else out "FLOOR_AS_COUNT_FAILED\n";

fun floor_as_count_at (pt, Bt, nt) hpos hNdvd hBnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p_fc",0), ctermU pt),(("B_fc",0), ctermU Bt),(("n_fc",0), ctermU nt)] floor_as_count)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hpos) hNdvd) hBnd end;
val () = out "FC_END\n";

(* ############################################################################
   (ND)  no_diagonal :  no lattice point on the line p*y = q*k.
   ############################################################################ *)
val () = out "ND_BEGIN\n";

val prime_not_dvd_pos_lt_U = varifyU prime_not_dvd_pos_lt;  (* dvd p r ==> lt 0 r ==> lt r p ==> oFalse *)
fun prime_not_dvd_pos_lt_atU (pt, rt) hdvd hpos hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("r",0), ctermU rt)] prime_not_dvd_pos_lt_U)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hdvd) hpos) hlt end;

(* lt_m_p_U : prime2 p ==> oeq (sub p 1)(add m m) ==> lt m p *)
fun lt_m_p_U p m hPrime hOdd =
  let
    val opp = one_plus_pm1_U p hPrime;           (* (1 + (p-1)) = p *)
    (* p = 1 + (p-1) = 1 + (m+m) = Suc(m+m) *)
    val r1 = add_cong_r_U (suc ZeroC, sub p oneC, add m m) hOdd;  (* (1 + (p-1)) = (1 + (m+m)) *)
    val pEq1 = oeq_trans_U OF [oeq_sym_U OF [opp], r1];           (* p = (1 + (m+m)) *)
    val aS = addSuc_U (ZeroC, add m m);          (* (Suc 0 + (m+m)) = Suc(0 + (m+m)) *)
    val a0 = add0_U (add m m);                   (* (0 + (m+m)) = (m+m) *)
    val pEq = oeq_trans_U OF [oeq_trans_U OF [pEq1, aS], Succong_U a0];  (* p = Suc(m+m) *)
    (* lt m p = le (Suc m) p : p = Suc(m+m) = (Suc m) + m  [addSuc rev] *)
    val aSm = addSuc_U (m, m);                    (* (Suc m + m) = Suc(m + m) *)
    val pAdd = oeq_trans_U OF [pEq, oeq_sym_U OF [aSm]];  (* p = (Suc m + m) *)
  in le_intro_U (suc m, p, m) pAdd end;          (* le (Suc m) p = lt m p *)

(* lt_in_range_U : prime2 p ==> (p-1=m+m) ==> le (Suc 0) k ==> le k m ==> lt k p *)
fun lt_in_range_U (p, m, k) hPrime hOdd h1k hkm =
  let
    val ltmp = lt_m_p_U p m hPrime hOdd;         (* lt m p = le (Suc m) p *)
    val leSkSm = leSucMono_U (k, m) hkm;         (* le (Suc k)(Suc m) *)
    val ltkp = le_trans_U_at (suc k, suc m, p) leSkSm ltmp;  (* le (Suc k) p = lt k p *)
  in ltkp end;

(* not_dvd_in_range_U : prime2 p ==> (p-1=m+m) ==> le 1 k ==> le k m ==> ~(dvd p k) *)
fun not_dvd_in_range_U (p, m, k) hPrime hOdd h1k hkm =
  let
    val ltkp = lt_in_range_U (p, m, k) hPrime hOdd h1k hkm;  (* lt k p *)
    val lt0k = h1k;                              (* le (Suc 0) k = lt 0 k *)
    val hdvd = Thm.assume (ctermU (jT (dvd p k)));
    val ff = prime_not_dvd_pos_lt_atU (p, k) hdvd lt0k ltkp;  (* oFalse *)
  in impI_U_at (dvd p k, oFalseC) (Thm.implies_intr (ctermU (jT (dvd p k))) ff) end;

(* not_dvd_distinct_primes_U : prime2 p ==> prime2 q ==> ~(oeq p q) ==> ~(dvd p q)
   (p prime, q prime, p<>q => p does not divide q : p|q => p=1 or p=q ; p>1 ; so p=q, contra) *)
fun not_dvd_distinct_primes_U (p, q) hPp hPq hNe =
  let
    val hdvd = Thm.assume (ctermU (jT (dvd p q)));
    val dis = prime2_div_atU (q, p) hPq hdvd;     (* Disj (oeq p 1)(oeq p q) *)
    val goalF = oFalseC;
    val cA =
      let
        val h1 = Thm.assume (ctermU (jT (oeq p (suc ZeroC))));   (* p = 1 *)
        (* prime2 p gives lt 1 p = le 2 p ; with p=1 -> le 2 1 -> lt 1 1 -> oFalse.
           Use prime2_gt1_U p hPp : le (Suc(Suc 0)) p ; rewrite p->1 ; le 2 1 = le (Suc 1)(1) = lt 1 1 ? 
           le (Suc(Suc 0)) (Suc 0) -> need contradiction. *)
        val gt1 = prime2_gt1_U p hPp;             (* le (Suc(Suc 0)) p *)
        val le21 = oeq_rw_U (Term.lambda (Free("z_nd1", natT)) (le (suc (suc ZeroC)) (Free("z_nd1", natT))), p, suc ZeroC) h1 gt1;  (* le 2 1 = le (Suc 1) 1 = lt 1 1 *)
        val ff = lt_irrefl_U_at (suc ZeroC) le21;  (* oFalse *)
      in Thm.implies_intr (ctermU (jT (oeq p (suc ZeroC)))) ff end;
    val cB =
      let
        val h2 = Thm.assume (ctermU (jT (oeq p q)));   (* p = q *)
        val ff = mp_U_at (oeq p q, oFalseC) hNe h2;     (* oFalse *)
      in Thm.implies_intr (ctermU (jT (oeq p q))) ff end;
    val ff = disjE_U_at (oeq p (suc ZeroC), oeq p q, goalF) dis cA cB;
  in impI_U_at (dvd p q, oFalseC) (Thm.implies_intr (ctermU (jT (dvd p q))) ff) end;
val () = out "ND_HELPERS_READY\n";

(* ---- ND theorem : prime2 p ==> prime2 q ==> ~(oeq p q) ==> le 1 k ==> le k m ==>
                      le 1 y ==> le y m2 ==> (p-1=m+m) ==> (q-1=m2+m2) ==>
                      ~(oeq (mult p y)(mult q k))  ---- *)
val no_diagonal =
  let
    val pF=Free("p_nd",natT); val qF=Free("q_nd",natT); val mF=Free("m_nd",natT);
    val m2F=Free("m2_nd",natT); val kF=Free("k_nd",natT); val yF=Free("y_nd",natT);
    val hPp=Thm.assume(ctermU(jT(prime2 pF)));
    val hPq=Thm.assume(ctermU(jT(prime2 qF)));
    val hNe=Thm.assume(ctermU(jT(neg(oeq pF qF))));
    val h1k=Thm.assume(ctermU(jT(le (suc ZeroC) kF)));
    val hkm=Thm.assume(ctermU(jT(le kF mF)));
    val h1y=Thm.assume(ctermU(jT(le (suc ZeroC) yF)));
    val hym2=Thm.assume(ctermU(jT(le yF m2F)));
    val hOp=Thm.assume(ctermU(jT(oeq(sub pF oneC)(add mF mF))));
    val hOq=Thm.assume(ctermU(jT(oeq(sub qF oneC)(add m2F m2F))));
    (* assume oeq (p*y)(q*k) -> dvd p (q*k) (witness y, since p*y = q*k) -> euclid -> dvd p q or dvd p k *)
    val hEq = Thm.assume (ctermU (jT (oeq (mult pF yF)(mult qF kF))));   (* p*y = q*k *)
    (* dvd p (q*k) : Ex z. (q*k) = p*z ; z = y : (q*k) = p*y by sym hEq *)
    val dvdAbs = Abs("z", natT, oeq (mult qF kF) (mult pF (Bound 0)));
    val dvdQK = exI_U_at (dvdAbs, yF) (oeq_sym_U OF [hEq]);   (* dvd p (q*k) *)
    val eu = euclid_U (pF, qF, kF) hPp dvdQK;                 (* Disj (dvd p q)(dvd p k) *)
    val nDvdQ = not_dvd_distinct_primes_U (pF, qF) hPp hPq hNe;  (* ~(dvd p q) *)
    val nDvdK = not_dvd_in_range_U (pF, mF, kF) hPp hOp h1k hkm; (* ~(dvd p k) *)
    val cA =
      let val hA = Thm.assume (ctermU (jT (dvd pF qF)))
          val ff = mp_U_at (dvd pF qF, oFalseC) nDvdQ hA
      in Thm.implies_intr (ctermU (jT (dvd pF qF))) ff end;
    val cB =
      let val hB = Thm.assume (ctermU (jT (dvd pF kF)))
          val ff = mp_U_at (dvd pF kF, oFalseC) nDvdK hB
      in Thm.implies_intr (ctermU (jT (dvd pF kF))) ff end;
    val ff = disjE_U_at (dvd pF qF, dvd pF kF, oFalseC) eu cA cB;
    val ndEq = impI_U_at (oeq (mult pF yF)(mult qF kF), oFalseC)
                 (Thm.implies_intr (ctermU (jT (oeq (mult pF yF)(mult qF kF)))) ff);  (* ~(oeq (p*y)(q*k)) *)
    val d9 = Thm.implies_intr (ctermU (jT (oeq(sub qF oneC)(add m2F m2F)))) ndEq;
    val d8 = Thm.implies_intr (ctermU (jT (oeq(sub pF oneC)(add mF mF)))) d9;
    val d7 = Thm.implies_intr (ctermU (jT (le yF m2F))) d8;
    val d6 = Thm.implies_intr (ctermU (jT (le (suc ZeroC) yF))) d7;
    val d5 = Thm.implies_intr (ctermU (jT (le kF mF))) d6;
    val d4 = Thm.implies_intr (ctermU (jT (le (suc ZeroC) kF))) d5;
    val d3 = Thm.implies_intr (ctermU (jT (neg(oeq pF qF)))) d4;
    val d2 = Thm.implies_intr (ctermU (jT (prime2 qF))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val () = out "ND_RAW_DONE\n";

val pV_nd=Var(("p_nd",0),natT); val qV_nd=Var(("q_nd",0),natT); val mV_nd=Var(("m_nd",0),natT);
val m2V_nd=Var(("m2_nd",0),natT); val kV_nd=Var(("k_nd",0),natT); val yV_nd=Var(("y_nd",0),natT);
val i_no_diagonal =
  Logic.mk_implies (jT (prime2 pV_nd),
   Logic.mk_implies (jT (prime2 qV_nd),
    Logic.mk_implies (jT (neg(oeq pV_nd qV_nd)),
     Logic.mk_implies (jT (le (suc ZeroC) kV_nd),
      Logic.mk_implies (jT (le kV_nd mV_nd),
       Logic.mk_implies (jT (le (suc ZeroC) yV_nd),
        Logic.mk_implies (jT (le yV_nd m2V_nd),
         Logic.mk_implies (jT (oeq(sub pV_nd oneC)(add mV_nd mV_nd)),
          Logic.mk_implies (jT (oeq(sub qV_nd oneC)(add m2V_nd m2V_nd)),
            jT (neg(oeq(mult pV_nd yV_nd)(mult qV_nd kV_nd))))))))))));
val r_no_diagonal = checkF2c ("no_diagonal", no_diagonal, i_no_diagonal);
val () = if r_no_diagonal then out "NO_DIAGONAL_OK\n" else out "NO_DIAGONAL_FAILED\n";
fun no_diagonal_at (pt,qt,mt,m2t,kt,yt) hPp hPq hNe h1k hkm h1y hym2 hOp hOq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p_nd",0), ctermU pt),(("q_nd",0), ctermU qt),(("m_nd",0), ctermU mt),
         (("m2_nd",0), ctermU m2t),(("k_nd",0), ctermU kt),(("y_nd",0), ctermU yt)] no_diagonal)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
       (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPp) hPq) hNe) h1k) hkm) h1y) hym2) hOp) hOq end;
val () = out "ND_END\n";

(* ############################################################################
   (CC)  complementary count :
   given no point on the line (~(oeq (p*(Suc k)) B) for indices up to n) :
       cnt (%y. lt (p*y) B) n + cnt (%y. lt B (p*y)) n = n.
   By induction on j (<= n), no-diagonal supplied per-index.
   ############################################################################ *)
val () = out "CC_BEGIN\n";

fun aboveAbs (pt, Bt) = let val yy = Free("y_ab_fr", natT) in Term.lambda yy (lt Bt (mult pt yy)) end;  (* %y. lt B (p*y) *)
(* belowAbs = ltPredAbs (p, B) : %y. lt (p*y) B *)

(* lt_asym_U : lt a b ==> lt b a ==> oFalse *)
fun lt_asym_U (aT, bT) hab hba =
  let
    (* lt a b = le (Suc a) b ; lt b a = le (Suc b) a.  le (Suc a) b and le b (Suc b)? 
       Simpler : le (Suc a) b and le (Suc b) a -> le (Suc a) a (trans via b) ... 
       le (Suc a) b ; from lt b a = le (Suc b) a get le b a (le_of? ) ; 
       Use : lt a b = le (Suc a) b ; le (Suc b) a (=lt b a). le (Suc a) b, le b (Suc b) trans-> ...
       Direct : le (Suc a) b and le (Suc b) a.  le (Suc a) b -> le (Suc a) b ;
       chain le (Suc b) a and le a (Suc a) -> le (Suc b)(Suc a) ; with le (Suc a) b -> le (Suc a) b...
       Cleanest : le (Suc a) b ; le (Suc b) a.  le_trans (Suc a) b a? need le b a.
       le b a from le (Suc b) a : le b (Suc b) trans le (Suc b) a -> le b a. *)
    val leb_Sb = le_self_suc_U bT;                      (* le b (Suc b) *)
    val le_b_a = le_trans_U_at (bT, suc bT, aT) leb_Sb hba;  (* le b a *)
    val le_Sa_a = le_trans_U_at (suc aT, bT, aT) hab le_b_a; (* le (Suc a) a = lt a a *)
  in lt_irrefl_U_at aT le_Sa_a end;

val cnt_complement =
  let
    val pF=Free("p_cc",natT); val BF=Free("B_cc",natT); val nF=Free("n_cc",natT);
    val below = ltPredAbs (pF, BF);   (* %y. lt (p*y) B *)
    val above = aboveAbs (pF, BF);    (* %y. lt B (p*y) *)
    (* global no-diagonal hyp : !!k. Imp (le (Suc k) n)(~(oeq (p*(Suc k)) B)) -- object impl form *)
    val kHF = Free("k_ccg", natT);
    val ndHypProp = mkForall (Term.lambda kHF (mkImp (le (suc kHF) nF)
                       (neg (oeq (mult pF (suc kHF)) BF))));   (* OBJECT forall+imp *)
    val ndAll = Thm.assume (ctermU (jT ndHypProp));
    (* induction on j : Pj = Imp (le j n)(oeq (add (cnt below j)(cnt above j)) j) *)
    val zF = Free("z_cc", natT);
    val Pind = Term.lambda zF (mkImp (le zF nF)
                  (oeq (add (cnt below zF)(cnt above zF)) zF));
    val jF = Free("j_cc", natT);
    (* BASE j=0 : le 0 n --> add (cnt below 0)(cnt above 0) = 0 *)
    val base =
      let
        val cb0 = cnt0_U below;   (* cnt below 0 = 0 *)
        val ca0 = cnt0_U above;   (* cnt above 0 = 0 *)
        (* add 0 0 = 0 *)
        val a00 = add0_U ZeroC;   (* (0+0)=0 *)
        val l1 = oeq_rw_U (Term.lambda (Free("zc1", natT)) (oeq (add (Free("zc1", natT))(cnt above ZeroC)) ZeroC),
                    ZeroC, cnt below ZeroC) (oeq_sym_U OF [cb0]) (oeq_rw_U (Term.lambda (Free("zc2", natT)) (oeq (add ZeroC (Free("zc2", natT))) ZeroC),
                       ZeroC, cnt above ZeroC) (oeq_sym_U OF [ca0]) a00);
        (* l1 : oeq (add (cnt below 0)(cnt above 0)) 0 *)
      in impI_U_at (le ZeroC nF, oeq (add (cnt below ZeroC)(cnt above ZeroC)) ZeroC)
            (Thm.implies_intr (ctermU (jT (le ZeroC nF))) l1) end;
    (* STEP : IH (le x n --> sum x = x) ; show le (Suc x) n --> sum (Suc x) = Suc x *)
    val xF = Free("x_cc", natT);
    val ihC = mkImp (le xF nF)(oeq (add (cnt below xF)(cnt above xF)) xF);
    val IH = Thm.assume (ctermU (jT ihC));
    val step =
      let
        val hSxn = Thm.assume (ctermU (jT (le (suc xF) nF)));   (* le (Suc x) n *)
        (* le x n from le (Suc x) n *)
        val lexSx = le_self_suc_U xF;
        val lexn = le_trans_U_at (xF, suc xF, nF) lexSx hSxn;   (* le x n *)
        val ihApp = mp_U_at (le xF nF, oeq (add (cnt below xF)(cnt above xF)) xF) IH lexn;  (* sum x = x *)
        (* no-diagonal at x : ~(oeq (p*(Suc x)) B) *)
        val ndImp = allE_U_at (Term.lambda kHF (mkImp (le (suc kHF) nF)(neg (oeq (mult pF (suc kHF)) BF)))) xF ndAll;
                    (* Imp (le (Suc x) n)(~(oeq (p*(Suc x)) B)) *)
        val ndAtx = mp_U_at (le (suc xF) nF, neg (oeq (mult pF (suc xF)) BF)) ndImp hSxn;  (* ~(oeq (p*(Suc x)) B) *)
        (* trichotomy : le_or_lt (p*(Suc x)) B : Disj (le (p*Sx) B)(lt B (p*Sx)) *)
        val pSx = mult pF (suc xF);
        val tri = le_or_lt_U (pSx, BF);     (* Disj (le (p*Sx) B)(lt B (p*Sx)) *)
        val goalS = oeq (add (cnt below (suc xF))(cnt above (suc xF))) (suc xF);
        (* CASE BELOW : le (p*Sx) B -> with ~eq -> lt (p*Sx) B *)
        val cBelow =
          let
            val hle = Thm.assume (ctermU (jT (le pSx BF)));     (* le (p*Sx) B *)
            val hlt = le_neq_lt_U_at (pSx, BF) hle ndAtx;        (* lt (p*Sx) B = below(Suc x) *)
            (* above(Suc x) FALSE : ~(lt B (p*Sx)) *)
            val notAbove =
              let val ha = Thm.assume (ctermU (jT (lt BF pSx)))
                  val ff = lt_asym_U (pSx, BF) hlt ha
              in impI_U_at (lt BF pSx, oFalseC) (Thm.implies_intr (ctermU (jT (lt BF pSx))) ff) end;
            val cbSuc = cntSucT_U (below, xF) hlt;       (* cnt below (Suc x) = Suc(cnt below x) *)
            val caSuc = cntSucF_U (above, xF) notAbove;  (* cnt above (Suc x) = cnt above x *)
            (* sum (Suc x) = Suc(cnt below x) + cnt above x = Suc(cnt below x + cnt above x) = Suc x *)
            val rwb = oeq_rw_U (Term.lambda (Free("za1", natT)) (oeq (add (Free("za1", natT))(cnt above (suc xF))) (suc xF)),
                        suc (cnt below xF), cnt below (suc xF)) (oeq_sym_U OF [cbSuc])
                        (oeq_rw_U (Term.lambda (Free("za2", natT)) (oeq (add (suc (cnt below xF)) (Free("za2", natT))) (suc xF)),
                           cnt above xF, cnt above (suc xF)) (oeq_sym_U OF [caSuc])
                           (* prove : oeq (add (Suc(cnt below x))(cnt above x)) (Suc x) *)
                           (let
                              val aSl = addSuc_U (cnt below xF, cnt above xF);  (* (Suc(cb x) + ca x) = Suc(cb x + ca x) *)
                              val sucIH = Succong_U ihApp;     (* Suc(cb x + ca x) = Suc x *)
                            in oeq_trans_U OF [aSl, sucIH] end));
          in Thm.implies_intr (ctermU (jT (le pSx BF))) rwb end;
        (* CASE ABOVE : lt B (p*Sx) *)
        val cAbove =
          let
            val hlt = Thm.assume (ctermU (jT (lt BF pSx)));    (* lt B (p*Sx) = above(Suc x) *)
            val notBelow =
              let val hb = Thm.assume (ctermU (jT (lt pSx BF)))
                  val ff = lt_asym_U (BF, pSx) hlt hb
              in impI_U_at (lt pSx BF, oFalseC) (Thm.implies_intr (ctermU (jT (lt pSx BF))) ff) end;
            val cbSuc = cntSucF_U (below, xF) notBelow;   (* cnt below (Suc x) = cnt below x *)
            val caSuc = cntSucT_U (above, xF) hlt;        (* cnt above (Suc x) = Suc(cnt above x) *)
            (* sum (Suc x) = cnt below x + Suc(cnt above x) = Suc(cnt below x + cnt above x) = Suc x *)
            val rwa = oeq_rw_U (Term.lambda (Free("zb1", natT)) (oeq (add (Free("zb1", natT))(cnt above (suc xF))) (suc xF)),
                        cnt below xF, cnt below (suc xF)) (oeq_sym_U OF [cbSuc])
                        (oeq_rw_U (Term.lambda (Free("zb2", natT)) (oeq (add (cnt below xF) (Free("zb2", natT))) (suc xF)),
                           suc (cnt above xF), cnt above (suc xF)) (oeq_sym_U OF [caSuc])
                           (let
                              val aSr2 = addSr_U (cnt below xF, cnt above xF);  (* (cb x + Suc(ca x)) = Suc(cb x + ca x) *)
                              val sucIH = Succong_U ihApp;
                            in oeq_trans_U OF [aSr2, sucIH] end));
          in Thm.implies_intr (ctermU (jT (lt BF pSx))) rwa end;
        val concl = disjE_U_at (le pSx BF, lt BF pSx, goalS) tri cBelow cAbove;
      in impI_U_at (le (suc xF) nF, goalS)
            (Thm.implies_intr (ctermU (jT (le (suc xF) nF))) concl) end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihC)) step);
    val run = nat_induct_U_run Pind jF base stepF;   (* run : Imp (le jF n)(sum jF = jF), jF free *)
    (* substitute jF := nF (via a fresh oeq rewrite) is hard for Frees ; instead instantiate
       n itself : run holds for the SPECIFIC nF (closed over).  We want it at j := n.
       Approach : the running var jF is free ; rewrite jF -> nF is not via oeq (they are distinct frees).
       So : re-build by instantiating the induction at j := n.  But nat_induct gives the Free jF.
       Cleanest : prove the closed statement  ndHyp ==> sum n = n  by instantiating run at jF:=n.
       Since jF is a genuine Free, we use Thm.generalize / Drule.infer_instantiate after varify. *)
    val discharged = Thm.implies_intr (ctermU (jT ndHypProp)) run;  (* ndHyp ==> Imp(le jF n)(sum jF = jF) *)
    val gen = varify discharged;   (* schematic in ?p_cc ?B_cc ?n_cc ?j_cc *)
    (* instantiate ?j_cc := ?n_cc so the running var becomes n *)
    val nVcc = Var(("n_cc",0), natT);
    val atN = beta_norm (Drule.infer_instantiate ctxtU [(("j_cc",0), ctermU nVcc)] gen);
                (* ?p ?B ?n : ndHyp ==> Imp (le n n)(sum n = n) *)
  in atN end;
val () = out "CC_RUN_DONE\n";

(* cnt_complement instantiator + finalizer :
   given hND : jT (object-forall : !!k. le (Suc k) n --> ~(oeq (p*(Suc k)) B)),
   produce  oeq (add (cnt below n)(cnt above n)) n. *)
fun cnt_complement_at (pt, Bt, nt) hMetaND =   (* hMetaND : !!k. Imp (le (Suc k) n)(~(oeq (p*(Suc k)) B))  [meta] *)
  let
    val below = ltPredAbs (pt, Bt); val above = aboveAbs (pt, Bt);
    val kk = Free("k_cca", natT);
    val ndPabs = Term.lambda kk (mkImp (le (suc kk) nt)(neg (oeq (mult pt (suc kk)) Bt)));
    val hND = allI_U_at ndPabs hMetaND;   (* Forall(lambda k. Imp(...)(...)) = jT ndHyp *)
    val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p_cc",0), ctermU pt),(("B_cc",0), ctermU Bt),(("n_cc",0), ctermU nt)] cnt_complement);
        (* inst : jT ndHyp ==> jT (Imp (le n n)(oeq (add (cnt below n)(cnt above n)) n)) *)
    val impPart = Thm.implies_elim inst hND;   (* jT (Imp (le n n)(...)) *)
    val refl = le_refl_U_at nt;                (* le n n *)
    val res = mp_U_at (le nt nt, oeq (add (cnt below nt)(cnt above nt)) nt) impPart refl;
  in res end;   (* oeq (add (cnt below n)(cnt above n)) n *)
val () = out "CC_HELPERS_READY\n";

(* sanity-validate CC : check cnt_complement is 0-hyp + the right schematic shape *)
val pV_cc = Var(("p_cc",0),natT); val BV_cc = Var(("B_cc",0),natT); val nV_cc2 = Var(("n_cc",0),natT);
val belowV = ltPredAbs (pV_cc, BV_cc); val aboveV = aboveAbs (pV_cc, BV_cc);
val kHV = Free("k_ccg", natT);
val ndHypV = mkForall (Term.lambda kHV (mkImp (le (suc kHV) nV_cc2)(neg (oeq (mult pV_cc (suc kHV)) BV_cc))));
val i_cnt_complement =
  Logic.mk_implies (jT ndHypV,
    jT (mkImp (le nV_cc2 nV_cc2)(oeq (add (cnt belowV nV_cc2)(cnt aboveV nV_cc2)) nV_cc2)));
val r_cnt_complement = checkF2c ("cnt_complement", cnt_complement, i_cnt_complement);
val () = if r_cnt_complement then out "COMPL_COUNT_OK\n" else out "COMPL_COUNT_FAILED\n";
val () = out "CC_END\n";

(* ############################################################################
   (FU)  Fubini double-count swap (THE analytic crux).
   For a binary predicate R k y with the y=0 row empty (~(R k 0) for all k) :
       sumf (%k. cnt (%y. R k y) b) a
         = add (cnt (%y. R 0 y) b) (sumf (%y. cnt (%k. R k y) a) b)
   i.e. column-sum = (k=0 column) + row-sum.
   Proved via the peeling lemma (induction on b) + outer induction on a.
   R is supplied as an SML body-builder rbody : (kterm,yterm) -> term.
   ############################################################################ *)
val () = out "FU_BEGIN\n";

val sum_const_U = varifyU sum_const;   (* sumf (%i.c) n = mult c (Suc n) *)
fun sum_const_at_U (ct, nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("c",0), ctermU ct),(("n",0), ctermU nt)] sum_const_U);

(* sum_zero_U : sumf (%i. 0) n = 0  (special case ; derive from sum_const with c=0) *)
fun sum_zero_at_U nt =
  let
    val sc = sum_const_at_U (ZeroC, nt);     (* sumf (%i.0) n = mult 0 (Suc n) *)
    val m0 = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU (suc nt))] (varifyU mult_0));  (* mult 0 (Suc n) = 0 *)
  in oeq_trans_U OF [sc, m0] end;

(* the FU swap as a function of R (rbody : (kterm,yterm)->term).
   Returns a THM (closed, with the no-row-0 hyp discharged as a meta-implication on the
   universal object hyp) — actually we'll prove it with rbody concrete (the above pred). *)

(* concrete predicate : R k y = lt (mult q k)(mult p y)  (the ABOVE / q-line predicate).
   y=0 row : R k 0 = lt (mult q k)(mult p 0) = lt (mult q k) 0 = FALSE (le (Suc(q*k)) 0 impossible). *)
(* colPred k = %y. lt (q*k)(p*y) ; rowPred y = %k. lt (q*k)(p*y) *)
fun colPredA (qF,pF) kt = let val yy = Free("y_col_fr", natT) in Term.lambda yy (lt (mult qF kt)(mult pF yy)) end;
fun rowPredA (qF,pF) yt = let val kk = Free("k_row_fr", natT) in Term.lambda kk (lt (mult qF kk)(mult pF yt)) end;

(* ~(R k 0) : ~(lt (q*k) 0) i.e. ~(le (Suc(q*k)) 0).  le (Suc z) 0 -> 0 = Suc z + w -> Suc(..)=0 -> oFalse. *)
fun not_lt_zero_U zt =   (* ~(lt z 0) : lt z 0 = le (Suc z) 0 *)
  let
    val hlt = Thm.assume (ctermU (jT (lt zt ZeroC)));   (* le (Suc z) 0 *)
    val z0 = le_zero_U (suc zt) hlt;                     (* oeq (Suc z) 0 *)
    val ff = Suc_neq_Zero_U_at zt z0;                    (* oFalse : Suc z = 0 contradiction *)
  in impI_U_at (lt zt ZeroC, oFalseC) (Thm.implies_intr (ctermU (jT (lt zt ZeroC))) ff) end;

(* peeling lemma : for fixed a, by induction on b :
     sumf (%y. cnt (rowPredA y)(Suc a)) b = add (sumf (%y. cnt (rowPredA y) a) b)(cnt (colPredA (Suc a)) b)
   (one more column (k=Suc a) adds, per row y, 1 iff R(Suc a) y ; total = cnt(colA(Suc a)) b). *)
val fu_peel =
  let
    val qF=Free("q_fu",natT); val pF=Free("p_fu",natT); val aF=Free("a_fu",natT);
    val rowP = rowPredA (qF,pF);    (* y |-> (%k. lt (q*k)(p*y)) *)
    val colSa = colPredA (qF,pF) (suc aF);   (* %y. lt (q*(Suc a))(p*y) *)
    (* rowSumAt c y = cnt (rowP y) c *)
    fun rowSummand c = let val yy = Free("yps_fr", natT) in Term.lambda yy (cnt (rowP yy) c) end;
    val lhsSum = fn b => sumf (rowSummand (suc aF)) b;
    val rhsSum = fn b => sumf (rowSummand aF) b;
    (* ~(R (Suc a) 0) : ~(lt (q*(Suc a)) 0) *)
    val nR0 = not_lt_zero_U (mult qF (suc aF));
    val zF = Free("z_fup", natT);
    val Pind = Term.lambda zF (oeq (lhsSum zF) (add (rhsSum zF) (cnt colSa zF)));
    val bF = Free("b_fu", natT);
    (* BASE b=0 *)
    val base =
      let
        val l0 = sumf0_U (rowSummand (suc aF));   (* sumf (rowSummand(Suc a)) 0 = cnt (rowP 0)(Suc a) *)
        val r0 = sumf0_U (rowSummand aF);         (* sumf (rowSummand a) 0 = cnt (rowP 0) a *)
        val cc0 = cnt0_U colSa;                   (* cnt colSa 0 = 0 *)
        (* cnt (rowP 0)(Suc a) = cnt (rowP 0) a  since ~(rowP 0 (Suc a)) = ~(R (Suc a) 0) = nR0 *)
        (* rowP 0 (Suc a) = lt (q*(Suc a))(p*0).  not_lt_zero gives ~(lt (q*(Suc a)) 0) ; but here it's
           lt (q*(Suc a))(p*0).  p*0 = 0.  Need ~(rowP 0 (Suc a)). rowP 0 = %k. lt(q*k)(p*0).
           rowP 0 (Suc a) = lt (q*(Suc a))(p*0).  rewrite p*0 -> 0 : mult0r. *)
        val p0 = mult0r_U2 pF;                    (* (p*0) = 0 *)
        val nRowP0 =   (* ~(lt (q*(Suc a))(p*0)) from nR0 (~(lt (q*(Suc a)) 0)) by rewriting 0->p*0 *)
          let val body = oeq_rw_U (Term.lambda (Free("zr0", natT)) (neg (lt (mult qF (suc aF)) (Free("zr0", natT)))),
                            ZeroC, mult pF ZeroC) (oeq_sym_U OF [p0]) nR0
          in body end;   (* ~(lt (q*(Suc a))(p*0)) = ~(rowP 0 (Suc a)) *)
        val cf = cntSucF_U (rowP ZeroC, aF) nRowP0;   (* cnt (rowP 0)(Suc a) = cnt (rowP 0) a *)
        (* assemble : lhs0 = cnt(rowP0)(Suc a) = cnt(rowP0) a = rhs0 ; rhs0 + 0 = rhs0 *)
        val lhsEq = oeq_trans_U OF [l0, cf];          (* sumf lhs 0 = cnt(rowP0) a *)
        val rhsBuild =   (* add (sumf rhs 0)(cnt colSa 0) = cnt(rowP0) a *)
          let
            val rw1 = oeq_rw_U (Term.lambda (Free("zb1f", natT)) (oeq (add (Free("zb1f", natT))(cnt colSa ZeroC)) (cnt (rowP ZeroC) aF)),
                        cnt (rowP ZeroC) aF, sumf (rowSummand aF) ZeroC) (oeq_sym_U OF [r0])
                        (oeq_rw_U (Term.lambda (Free("zb2f", natT)) (oeq (add (cnt (rowP ZeroC) aF) (Free("zb2f", natT))) (cnt (rowP ZeroC) aF)),
                           ZeroC, cnt colSa ZeroC) (oeq_sym_U OF [cc0])
                           (add0r_U (cnt (rowP ZeroC) aF)));  (* (cnt(rowP0)a + 0) = cnt(rowP0)a *)
          in rw1 end;   (* add (sumf rhs 0)(cnt colSa 0) = cnt(rowP0) a *)
        (* goal : oeq (sumf lhs 0)(add (sumf rhs 0)(cnt colSa 0)) *)
        val goal0 = oeq_trans_U OF [lhsEq, oeq_sym_U OF [rhsBuild]];
      in goal0 end;
    (* STEP b -> Suc b *)
    val xF = Free("x_fu", natT);
    val ihP = oeq (lhsSum xF)(add (rhsSum xF)(cnt colSa xF));
    val IH = Thm.assume (ctermU (jT ihP));
    val step =
      let
        val Sx = suc xF;
        (* LHS(Suc x) = sumf lhs x + cnt (rowP (Suc x))(Suc a) *)
        val lSuc = sumfSuc_U (rowSummand (suc aF), xF);  (* sumf lhs (Suc x) = add (sumf lhs x)(cnt (rowP(Suc x))(Suc a)) *)
        (* RHS(Suc x) = add (sumf rhs (Suc x))(cnt colSa (Suc x))
                       = add (add (sumf rhs x)(cnt (rowP(Suc x)) a))(cnt colSa (Suc x)) *)
        val rSuc = sumfSuc_U (rowSummand aF, xF);        (* sumf rhs (Suc x) = add (sumf rhs x)(cnt (rowP(Suc x)) a) *)
        (* case on R(Suc a)(Suc x) : same prop for both rowP(Suc x)(Suc a) and colSa(Suc x). *)
        val em = ex_middle_U_at (lt (mult qF (suc aF))(mult pF Sx));   (* Disj (R(Sa)(Sx)) (~..) *)
        val goalS = oeq (lhsSum Sx)(add (rhsSum Sx)(cnt colSa Sx));
        (* common : rowP(Suc x)(Suc a) = lt(q*(Suc a))(p*(Suc x)) ; colSa(Suc x) = lt(q*(Suc a))(p*(Suc x)). SAME. *)
        val Rprop = lt (mult qF (suc aF))(mult pF Sx);
        val A = sumf (rowSummand aF) xF; val C = cnt colSa xF; val D = cnt (rowP Sx) aF;
        val Erow = cnt (rowP Sx)(suc aF);   (* the new LHS column term = cnt(rowP Sx)(Suc a) *)
        (* lhsSum Sx = add (lhsSum x) Erow [lSuc] ; rewrite lhsSum x -> add A C [IH] : *)
        val lhsBase = oeq_trans_U OF [lSuc, add_cong_l_U (lhsSum xF, add A C, Erow) IH];
                      (* lhsSum Sx = add (add A C) Erow *)
        (* rhsSum Sx = add A D [rSuc] ; so add (rhsSum Sx)(cnt colSa Sx) = add (add A D)(cnt colSa Sx) : *)
        val rhsBase = add_cong_l_U (rhsSum Sx, add A D, cnt colSa Sx) rSuc;
                      (* add (rhsSum Sx)(cnt colSa Sx) = add (add A D)(cnt colSa Sx) *)
        val cT =
          let
            val hR = Thm.assume (ctermU (jT Rprop));
            val crsa = cntSucT_U (rowP Sx, aF) hR;     (* Erow = Suc D *)
            val ccsa = cntSucT_U (colSa, xF) hR;       (* cnt colSa Sx = Suc C *)
            (* lhsSum Sx = add (add A C) Erow = add (add A C)(Suc D) *)
            val lhsX = oeq_trans_U OF [lhsBase, add_cong_r_U (add A C, Erow, suc D) crsa];
            (* add(rhsSum Sx)(cnt colSa Sx) = add (add A D)(cnt colSa Sx) = add (add A D)(Suc C) *)
            val rhsX = oeq_trans_U OF [rhsBase, add_cong_r_U (add A D, cnt colSa Sx, suc C) ccsa];
            (* arith : (A+C)+Suc D = (A+D)+Suc C *)
            val arith =
              let
                val l_aSr = addSr_U (add A C, D);    (* ((A+C)+Suc D) = Suc((A+C)+D) *)
                val r_aSr = addSr_U (add A D, C);    (* ((A+D)+Suc C) = Suc((A+D)+C) *)
                val la = addassoc_U (A, C, D);       (* (A+C)+D = A+(C+D) *)
                val ra = addassoc_U (A, D, C);       (* (A+D)+C = A+(D+C) *)
                val cdc = addcomm_U (C, D);          (* (C+D)=(D+C) *)
                val acd = add_cong_r_U (A, add C D, add D C) cdc;  (* A+(C+D) = A+(D+C) *)
                val inner = oeq_trans_U OF [oeq_trans_U OF [la, acd], oeq_sym_U OF [ra]];  (* (A+C)+D = (A+D)+C *)
                val sucInner = Succong_U inner;      (* Suc((A+C)+D) = Suc((A+D)+C) *)
              in oeq_trans_U OF [oeq_trans_U OF [l_aSr, sucInner], oeq_sym_U OF [r_aSr]] end;
            val res = oeq_trans_U OF [oeq_trans_U OF [lhsX, arith], oeq_sym_U OF [rhsX]];
          in Thm.implies_intr (ctermU (jT Rprop)) res end;
        val cF2 =
          let
            val hNR = Thm.assume (ctermU (jT (neg Rprop)));
            val crsa = cntSucF_U (rowP Sx, aF) hNR;   (* Erow = D *)
            val ccsa = cntSucF_U (colSa, xF) hNR;     (* cnt colSa Sx = C *)
            val lhsX = oeq_trans_U OF [lhsBase, add_cong_r_U (add A C, Erow, D) crsa];   (* lhsSum Sx = add (add A C) D *)
            val rhsX = oeq_trans_U OF [rhsBase, add_cong_r_U (add A D, cnt colSa Sx, C) ccsa];  (* = add (add A D) C *)
            (* arith : (A+C)+D = (A+D)+C *)
            val arith =
              let
                val la = addassoc_U (A, C, D); val ra = addassoc_U (A, D, C);
                val cdc = addcomm_U (C, D);
                val acd = add_cong_r_U (A, add C D, add D C) cdc;
              in oeq_trans_U OF [oeq_trans_U OF [la, acd], oeq_sym_U OF [ra]] end;
            val res = oeq_trans_U OF [oeq_trans_U OF [lhsX, arith], oeq_sym_U OF [rhsX]];
          in Thm.implies_intr (ctermU (jT (neg Rprop))) res end;
        val concl = disjE_U_at (Rprop, neg Rprop, goalS) em cT cF2;
      in concl end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihP)) step);
    val run = nat_induct_U_run Pind bF base stepF;
  in varify run end;
val () = out "FU_PEEL_DONE\n";

(* the FU swap : induction on a, using fu_peel for the step.
     sumf (%k. cnt (colPredA k) b) a = add (cnt (colPredA 0) b)(sumf (%y. cnt (rowPredA y) a) b) *)
fun fu_peel_at (qt,pt,at,bt) =
  beta_norm (Drule.infer_instantiate ctxtU
    [(("q_fu",0), ctermU qt),(("p_fu",0), ctermU pt),(("a_fu",0), ctermU at),(("b_fu",0), ctermU bt)] fu_peel);

val fu_swap =
  let
    val qF=Free("q_fs",natT); val pF=Free("p_fs",natT); val bF=Free("b_fs",natT);
    val colP = colPredA (qF,pF);   (* k |-> %y. lt(q*k)(p*y) *)
    val rowP = rowPredA (qF,pF);   (* y |-> %k. lt(q*k)(p*y) *)
    fun colSummand a = let val kk = Free("kcs_fr", natT) in Term.lambda kk (cnt (colP kk) a) end;
    fun rowSummand a = let val yy = Free("yps_fr", natT) in Term.lambda yy (cnt (rowP yy) a) end;
    val Scol = fn a => sumf (let val kk = Free("kcs2_fr", natT) in Term.lambda kk (cnt (colP kk) bF) end) a;
    val Srow = fn a => sumf (rowSummand a) bF;
    val col0 = cnt (colP ZeroC) bF;
    val zF = Free("z_fs", natT);
    val Pind = Term.lambda zF (oeq (Scol zF) (add col0 (Srow zF)));
    val aF = Free("a_fs", natT);
    (* BASE a=0 *)
    val base =
      let
        val sc0 = sumf0_U (let val kk = Free("kcs2_fr", natT) in Term.lambda kk (cnt (colP kk) bF) end);
                  (* Scol 0 = cnt (colP 0) b = col0 *)
        (* Srow 0 = sumf (%y. cnt(rowP y) 0) b = 0 : via sum_cong to %y.0 then sum_zero *)
        val rowS0 = rowSummand ZeroC;   (* %y. cnt (rowP y) 0 *)
        val zeroAbs = let val yy = Free("yz_fr", natT) in Term.lambda yy ZeroC end;  (* %y. 0 *)
        (* pointwise : !!y. le y b ==> cnt (rowP y) 0 = 0 *)
        val yF = Free("y_fs0", natT);
        val congProof =
          let val body = cnt0_U (rowP yF)   (* cnt (rowP y) 0 = 0 *)
          in Thm.forall_intr (ctermU yF)
                (Thm.implies_intr (ctermU (jT (le yF bF))) body) end;
        val srEq = sum_cong_U (rowS0, zeroAbs, bF) congProof;   (* sumf (rowS0) b = sumf (%y.0) b *)
        val sz = sum_zero_at_U bF;                              (* sumf (%y.0) b = 0 *)
        val srow0_eq0 = oeq_trans_U OF [srEq, sz];              (* Srow 0 = 0 *)
        (* goal : Scol 0 = add col0 (Srow 0) ; Scol 0 = col0 ; add col0 (Srow0) = add col0 0 = col0 *)
        val rhs = oeq_rw_U (Term.lambda (Free("zbf", natT)) (oeq (add col0 (Free("zbf", natT))) col0),
                    ZeroC, Srow ZeroC) (oeq_sym_U OF [srow0_eq0]) (add0r_U col0);
                  (* add col0 (Srow 0) = col0 *)
        val res = oeq_trans_U OF [sc0, oeq_sym_U OF [rhs]];     (* Scol 0 = add col0 (Srow 0) *)
      in res end;
    (* STEP a -> Suc a *)
    val xF = Free("x_fs", natT);
    val ihP = oeq (Scol xF)(add col0 (Srow xF));
    val IH = Thm.assume (ctermU (jT ihP));
    val step =
      let
        val Sx = suc xF;
        (* Scol(Suc x) = Scol x + cnt (colP (Suc x)) b *)
        val scSuc = sumfSuc_U (let val kk = Free("kcs2_fr", natT) in Term.lambda kk (cnt (colP kk) bF) end, xF);
                    (* Scol (Suc x) = add (Scol x)(cnt (colP (Suc x)) b) *)
        (* fu_peel at (q,p,x,b) : Srow(Suc x) = add (Srow x)(cnt (colP (Suc x)) b) *)
        val peel = fu_peel_at (qF,pF,xF,bF);
                    (* sumf (%y. cnt(rowP y)(Suc x)) b = add (sumf(%y. cnt(rowP y) x) b)(cnt (colPredA(Suc x)) b) *)
        val ccol = cnt (colP Sx) bF;
        (* Scol(Suc x) = add (Scol x) ccol [scSuc] ; rewrite Scol x -> add col0 (Srow x) [IH] *)
        val l1 = oeq_trans_U OF [scSuc, add_cong_l_U (Scol xF, add col0 (Srow xF), ccol) IH];
                  (* Scol(Suc x) = add (add col0 (Srow x)) ccol *)
        (* RHS goal : add col0 (Srow (Suc x)) = add col0 (add (Srow x) ccol)  [by peel, add_cong_r] *)
        val rhsGoal = add_cong_r_U (col0, Srow Sx, add (Srow xF) ccol) peel;
                  (* add col0 (Srow(Suc x)) = add col0 (add (Srow x) ccol) *)
        (* assoc : add (add col0 (Srow x)) ccol = add col0 (add (Srow x) ccol) *)
        val asc = addassoc_U (col0, Srow xF, ccol);   (* (col0 + Srow x) + ccol = col0 + (Srow x + ccol) *)
        val res = oeq_trans_U OF [oeq_trans_U OF [l1, asc], oeq_sym_U OF [rhsGoal]];
                  (* Scol(Suc x) = add col0 (Srow(Suc x)) *)
      in res end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihP)) step);
    val run = nat_induct_U_run Pind aF base stepF;
  in varify run end;
val () = out "FU_SWAP_DONE\n";

(* validate FU *)
val qV_fs=Var(("q_fs",0),natT); val pV_fs=Var(("p_fs",0),natT); val bV_fs=Var(("b_fs",0),natT);
val aV_fs=Var(("a_fs",0),natT);
val colPV = colPredA (qV_fs,pV_fs); val rowPV = rowPredA (qV_fs,pV_fs);
val ScolV = sumf (let val kk = Free("kcs2_fr", natT) in Term.lambda kk (cnt (colPV kk) bV_fs) end) aV_fs;
val SrowV = sumf (let val yy = Free("yps_fr", natT) in Term.lambda yy (cnt (rowPV yy) aV_fs) end) bV_fs;
val i_fu_swap = jT (oeq ScolV (add (cnt (colPV ZeroC) bV_fs) SrowV));
val r_fu_swap = checkF2c ("fu_swap", fu_swap, i_fu_swap);
val () = if r_fu_swap then out "FUBINI_OK\n" else out "FUBINI_FAILED\n";
val () = out "FU_END\n";

(* ############################################################################
   (LS)  lattice symmetry :
     sumf (%k. rdiv(q*k) p) m + sumf (%j. rdiv(p*j) q) m2 = mult m m2
   for distinct odd primes p,q with (p-1=m+m),(q-1=m2+m2).
   Assembles FC (both ways) + CC (summed) + FU (the swap) + sum algebra.
   ############################################################################ *)
val () = out "LS_BEGIN\n";

(* cnt_full : (!!k. P(Suc k)) ==> cnt P n = n  (all positive indices satisfy P) *)
val cnt_full_lemma =
  let
    val PF = Free("P_cf", predNatT);
    val zF = Free("z_cf", natT);
    val Pind = Term.lambda zF (oeq (cnt PF zF) zF);
    val nF = Free("n_cf", natT);
    val kHF = Free("k_cfh", natT);
    val hAllProp = mkForall (Term.lambda kHF (PF $ (suc kHF)));   (* object forall : !!k. P(Suc k) *)
    val hAll = Thm.assume (ctermU (jT hAllProp));
    val base = let val c0 = cnt0_U PF in c0 end;   (* cnt P 0 = 0 *)
    val xF = Free("x_cf", natT);
    val ihP = oeq (cnt PF xF) xF;
    val IH = Thm.assume (ctermU (jT ihP));
    val step =
      let
        val hPSx = allE_U_at (Term.lambda kHF (PF $ (suc kHF))) xF hAll;  (* P(Suc x) *)
        val ceq = cntSucT_U (PF, xF) hPSx;     (* cnt P (Suc x) = Suc(cnt P x) *)
        val res = oeq_trans_U OF [ceq, Succong_U IH];   (* = Suc x *)
      in res end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihP)) step);
    val run = nat_induct_U_run Pind nF base stepF;
    val discharged = Thm.implies_intr (ctermU (jT hAllProp)) run;  (* hAll ==> cnt P n = n *)
  in varify discharged end;
fun cnt_full_at (Pt, nt) hMetaAll =   (* hMetaAll : !!k. (P (Suc k))  [meta] *)
  let
    val kk = Free("k_cfa", natT);
    val objAll = allI_U_at (Term.lambda kk (Pt $ (suc kk))) hMetaAll;   (* Forall(lambda k. P(Suc k)) *)
    val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P_cf",0), ctermU Pt),(("n_cf",0), ctermU nt)] cnt_full_lemma)
  in Thm.implies_elim inst objAll end;
val () = out "LS_CNTFULL_READY\n";

(* cnt_empty : (!!k. ~(P(Suc k))) ==> cnt P n = 0 *)
val cnt_empty_lemma =
  let
    val PF = Free("P_ce", predNatT);
    val zF = Free("z_ce", natT);
    val Pind = Term.lambda zF (oeq (cnt PF zF) ZeroC);
    val nF = Free("n_ce", natT);
    val kHF = Free("k_ceh", natT);
    val hAllProp = mkForall (Term.lambda kHF (neg (PF $ (suc kHF))));   (* !!k. ~(P(Suc k)) *)
    val hAll = Thm.assume (ctermU (jT hAllProp));
    val base = cnt0_U PF;   (* cnt P 0 = 0 *)
    val xF = Free("x_ce", natT);
    val ihP = oeq (cnt PF xF) ZeroC;
    val IH = Thm.assume (ctermU (jT ihP));
    val step =
      let
        val hNPSx = allE_U_at (Term.lambda kHF (neg (PF $ (suc kHF)))) xF hAll;  (* ~(P(Suc x)) *)
        val ceq = cntSucF_U (PF, xF) hNPSx;     (* cnt P (Suc x) = cnt P x *)
        val res = oeq_trans_U OF [ceq, IH];     (* = 0 *)
      in res end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU (jT ihP)) step);
    val run = nat_induct_U_run Pind nF base stepF;
    val discharged = Thm.implies_intr (ctermU (jT hAllProp)) run;
  in varify discharged end;
fun cnt_empty_at (Pt, nt) hMetaAll =   (* hMetaAll : !!k. ~(P(Suc k))  [meta] *)
  let
    val kk = Free("k_cea", natT);
    val objAll = allI_U_at (Term.lambda kk (neg (Pt $ (suc kk)))) hMetaAll;   (* Forall(lambda k. ~(P(Suc k))) *)
    val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P_ce",0), ctermU Pt),(("n_ce",0), ctermU nt)] cnt_empty_lemma)
  in Thm.implies_elim inst objAll end;
val () = out "LS_CNTEMPTY_READY\n";

val disj_zero_or_suc_U = varifyU disj_zero_or_suc;
fun dzos_U t = beta_norm (Drule.infer_instantiate ctxtU [(("p",0), ctermU t)] disj_zero_or_suc_U);
val () = out "LS_HELPERS_READY\n";

val lattice_symmetry =
  let
    val pF=Free("p_ls",natT); val qF=Free("q_ls",natT); val mF=Free("m_ls",natT); val m2F=Free("m2_ls",natT);
    val hPp=Thm.assume(ctermU(jT(prime2 pF)));
    val hPq=Thm.assume(ctermU(jT(prime2 qF)));
    val hNe=Thm.assume(ctermU(jT(neg(oeq pF qF))));
    val hOp=Thm.assume(ctermU(jT(oeq(sub pF oneC)(add mF mF))));
    val hOq=Thm.assume(ctermU(jT(oeq(sub qF oneC)(add m2F m2F))));
    val lt0p = lt0_of_prime_U pF hPp;   (* lt 0 p *)
    val lt0q = lt0_of_prime_U qF hPq;   (* lt 0 q *)
    val nNe_q = let val h = Thm.assume (ctermU (jT (oeq qF pF)))
                in impI_U_at (oeq qF pF, oFalseC) (Thm.implies_intr (ctermU (jT (oeq qF pF)))
                     (mp_U_at (oeq pF qF, oFalseC) hNe (oeq_sym_U OF [h]))) end;  (* ~(oeq q p) *)
    val nDvd_pq = not_dvd_distinct_primes_U (pF, qF) hPp hPq hNe;   (* ~(dvd p q) *)
    val nDvd_qp = not_dvd_distinct_primes_U (qF, pF) hPq hPp nNe_q; (* ~(dvd q p) *)

    (* predicate builders *)
    fun BQ kt = ltPredAbs (pF, mult qF kt);          (* %y. lt (p*y)(q*k) *)
    fun AQ kt = aboveAbs (pF, mult qF kt);           (* %y. lt (q*k)(p*y) = colPredA(q,p) k *)
    val colP = colPredA (qF,pF);                     (* k |-> %y. lt(q*k)(p*y) *)
    val rowP = rowPredA (qF,pF);                     (* j |-> %k. lt(q*k)(p*j) *)

    (* ---- bounds : le (rdiv(q*k)p) m2  for k in 1..m ; le (rdiv(p*j)q) m  for j in 1..m2 ----
       From q*k < q*p (k<p) and ... actually we need floor(q*k/p) <= m2.
       q*k <= q*m (k<=m).  floor(q*k/p) <= floor(q*m/p).  Hard to bound directly.
       Simpler bound used by FC : le (rdiv B p) n.  We get le (rdiv(q*k)p) m2 from :
         q*k = p*floor + r, r<p ; p*floor <= q*k <= q*m ; floor <= q*m/p.
       This bound is itself nontrivial.  GRACEFUL: we use the count_thresh route :
       cnt(BQ k) m2 = rdiv(q*k)p REQUIRES le (rdiv(q*k)p) m2.  Establish the bound:
         floor(q*k/p) <= m2  <=>  p*(Suc m2) > q*k.  p*(Suc m2) = p*(Suc m2).
         q*k <= q*m (k<=m) ; q = Suc(m2+m2) ; p = Suc(m+m).
         p*(Suc m2) vs q*m :  (Suc(m+m))*(Suc m2)  vs (Suc(m2+m2))*m.
         This is the crux bound.  We instead derive le (rdiv(q*k)p) m2 from FC's contrapositive
         via the count being <= m2 : cnt(BQ k) m2 <= ... no.  Use the DIRECT bound lemma below. *)

    (* bound lemma : 0<p ==> le (rdiv B p) n  when  lt B (mult p (Suc n))  (B < p*(Suc n)).
       Because B = p*Q + R, R<p ; if Q > n i.e. Q >= Suc n then p*Q >= p*(Suc n) > B >= p*Q, contra. *)
    fun rdiv_bound (pt, Bt, nt) hpos hBlt =   (* hBlt : lt B (mult p (Suc n)) -> le (rdiv B p) n *)
      let
        val Q = rdiv Bt pt; val R = rmod Bt pt;
        val divEq = div_mod_eq_U_at (Bt, pt) hpos;   (* B = p*Q + R *)
        (* le_or_lt Q n : Disj (le Q n)(lt n Q) ; case lt n Q -> Suc n <= Q -> p*(Suc n) <= p*Q <= B contra hBlt *)
        val tri = le_or_lt_U (Q, nt);
        val cA = Thm.implies_intr (ctermU (jT (le Q nt))) (Thm.assume (ctermU (jT (le Q nt))));
        val cB =
          let
            val hlt = Thm.assume (ctermU (jT (lt nt Q)));   (* le (Suc n) Q *)
            val lep = multLeMono_U (pt, suc nt, Q) hlt;     (* le (p*(Suc n))(p*Q) *)
            (* p*Q <= B : B = p*Q + R, p*Q <= p*Q + R = B *)
            val lepQB = let val la = le_add_U_at (mult pt Q, R)   (* le (p*Q)(p*Q + R) *)
                        in oeq_rw_U (Term.lambda (Free("zbd", natT)) (le (mult pt Q) (Free("zbd", natT))),
                             add (mult pt Q) R, Bt) (oeq_sym_U OF [divEq]) la end;  (* le (p*Q) B *)
            val lepnB = le_trans_U_at (mult pt (suc nt), mult pt Q, Bt) lep lepQB;  (* le (p*(Suc n)) B *)
            (* hBlt : lt B (p*(Suc n)) = le (Suc B)(p*(Suc n)). le (p*(Suc n)) B and le B (Suc B) -> le (p*(Sn)) (Suc B);
               combine le (Suc B)(p*(Sn)) and le (p*(Sn))(Suc B) -> ... use lt_asym style.
               lt B (p*(Sn)) and le (p*(Sn)) B -> contradiction. *)
            val le_B_SB = le_self_suc_U Bt;     (* le B (Suc B) *)
            (* lepnB : le (p*(Sn)) B ; hBlt : le (Suc B)(p*(Sn)).  le (Suc B)(p*(Sn)) and le (p*(Sn)) B -> le (Suc B) B = lt B B *)
            val le_SB_B = le_trans_U_at (suc Bt, mult pt (suc nt), Bt) hBlt lepnB;  (* le (Suc B) B *)
            val ff = lt_irrefl_U_at Bt le_SB_B;
            val res = Thm.implies_elim (oFalse_elim_U_at (le Q nt)) ff;
          in Thm.implies_intr (ctermU (jT (lt nt Q))) res end;
      in disjE_U_at (le Q nt, lt nt Q, le Q nt) tri cA cB end;
    val () = out "LS_RDIVBOUND_READY\n";

    (* p = Suc(m+m), q = Suc(m2+m2) *)
    val pSucEq =   (* p = Suc(m+m) *)
      let val opp = one_plus_pm1_U pF hPp;   (* (1+(p-1)) = p *)
          val r1 = add_cong_r_U (suc ZeroC, sub pF oneC, add mF mF) hOp;  (* (1+(p-1))=(1+(m+m)) *)
          val e1 = oeq_trans_U OF [oeq_sym_U OF [opp], r1];   (* p = (1+(m+m)) *)
          val aS = addSuc_U (ZeroC, add mF mF); val a0 = add0_U (add mF mF);
      in oeq_trans_U OF [oeq_trans_U OF [e1, aS], Succong_U a0] end;   (* p = Suc(m+m) *)
    val qSucEq =   (* q = Suc(m2+m2) *)
      let val opp = one_plus_pm1_U qF hPq;
          val r1 = add_cong_r_U (suc ZeroC, sub qF oneC, add m2F m2F) hOq;
          val e1 = oeq_trans_U OF [oeq_sym_U OF [opp], r1];
          val aS = addSuc_U (ZeroC, add m2F m2F); val a0 = add0_U (add m2F m2F);
      in oeq_trans_U OF [oeq_trans_U OF [e1, aS], Succong_U a0] end;   (* q = Suc(m2+m2) *)

    (* identity : add (mult q m) m2 = add (mult p m2) m   (both = m + m2 + 2*m*m2) *)
    (* q*m = (Suc(m2+m2))*m = add m (mult (m2+m2) m) [mult_Suc, q=Suc(m2+m2)] *)
    fun expand_qx (qq, m2m2, xx) hqeq =   (* hqeq : qq = Suc(m2m2) ; returns oeq (mult qq xx)(add xx (mult m2m2 xx)) *)
      let
        val rw = oeq_rw_U (Term.lambda (Free("zeq", natT)) (oeq (mult qq xx)(mult (Free("zeq", natT)) xx)), qq, suc m2m2) hqeq (oeqRefl_U (mult qq xx));
                 (* mult qq xx = mult (Suc m2m2) xx *)
        val ms = multSuc_U (m2m2, xx);   (* mult (Suc m2m2) xx = add xx (mult m2m2 xx) *)
      in oeq_trans_U OF [rw, ms] end;
    val ls_ident =
      let
        (* q*m = add m (mult (m2+m2) m) ; p*m2 = add m2 (mult (m+m) m2) *)
        val qmE = expand_qx (qF, add m2F m2F, mF) qSucEq;   (* q*m = add m ((m2+m2)*m) *)
        val pm2E = expand_qx (pF, add mF mF, m2F) pSucEq;   (* p*m2 = add m2 ((m+m)*m2) *)
        (* (m2+m2)*m = m2*m + m2*m ; (m+m)*m2 = m*m2 + m*m2 ; m2*m = m*m2 *)
        val d1 = rdist_U (m2F, m2F, mF);    (* (m2+m2)*m = (m2*m + m2*m) *)
        val d2 = rdist_U (mF, mF, m2F);     (* (m+m)*m2 = (m*m2 + m*m2) *)
        val mc = multcomm_U2 (m2F, mF);     (* m2*m = m*m2 *)
        (* q*m + m2 = add (add m ((m2+m2)*m)) m2 = add (add m (m2*m+m2*m)) m2 *)
        (* p*m2 + m = add (add m2 ((m+m)*m2)) m = add (add m2 (m*m2+m*m2)) m *)
        (* show both = add (add (add m m2)(m*m2)) (m*m2) via comm/assoc. *)
        val MM = mult mF m2F;
        (* LHS target value : add (mult q m) m2 *)
        (* step LHS: mult q m -> add m (m2*m+m2*m) -> add m (MM+MM) *)
        val qm_v1 = oeq_trans_U OF [qmE, add_cong_r_U (mF, mult (add m2F m2F) mF, add (mult m2F mF)(mult m2F mF)) d1];
                    (* q*m = add m (m2*m + m2*m) *)
        val qm_v2 = oeq_trans_U OF [qm_v1, add_cong_r_U (mF, add (mult m2F mF)(mult m2F mF), add MM MM)
                       (let val c1 = add_cong_l_U (mult m2F mF, MM, mult m2F mF) mc
                            val c2 = add_cong_r_U (MM, mult m2F mF, MM) mc
                        in oeq_trans_U OF [c1, c2] end)];
                    (* q*m = add m (MM + MM) *)
        val pm2_v1 = oeq_trans_U OF [pm2E, add_cong_r_U (m2F, mult (add mF mF) m2F, add MM MM) d2];
                    (* p*m2 = add m2 (MM + MM) *)
        (* now q*m + m2 = add (add m (MM+MM)) m2 ; p*m2 + m = add (add m2 (MM+MM)) m
           both should equal add (add m m2)(MM+MM) up to comm. *)
        val lhs1 = add_cong_l_U (mult qF mF, add mF (add MM MM), m2F) qm_v2;  (* (q*m + m2) = (add m (MM+MM)) + m2 *)
        val rhs1 = add_cong_l_U (mult pF m2F, add m2F (add MM MM), mF) pm2_v1; (* (p*m2 + m) = (add m2 (MM+MM)) + m *)
        (* (add m (MM+MM)) + m2 = add m (add (MM+MM) m2) [assoc] = add m (add m2 (MM+MM)) [comm] = (add m m2)+(MM+MM)... *)
        val ea = addassoc_U (mF, add MM MM, m2F);   (* (m + (MM+MM)) + m2 = m + ((MM+MM) + m2) *)
        val ec = addcomm_U (add MM MM, m2F);        (* (MM+MM)+m2 = m2 + (MM+MM) *)
        val eac = add_cong_r_U (mF, add (add MM MM) m2F, add m2F (add MM MM)) ec;  (* m+((MM+MM)+m2) = m+(m2+(MM+MM)) *)
        val ea2 = addassoc_U (mF, m2F, add MM MM);  (* (m+m2)+(MM+MM) = m+(m2+(MM+MM)) *)
        val lhs_norm = oeq_trans_U OF [oeq_trans_U OF [oeq_trans_U OF [lhs1, ea], eac], oeq_sym_U OF [ea2]];
                       (* (q*m + m2) = (m+m2)+(MM+MM) *)
        (* RHS: (add m2 (MM+MM)) + m = m2 + ((MM+MM)+m) [assoc] = m2 + (m + (MM+MM)) [comm inner] ... 
           = (m2+m)+(MM+MM) = (m+m2)+(MM+MM) *)
        val fa = addassoc_U (m2F, add MM MM, mF);   (* (m2+(MM+MM))+m = m2+((MM+MM)+m) *)
        val fc = addcomm_U (add MM MM, mF);         (* (MM+MM)+m = m+(MM+MM) *)
        val fac = add_cong_r_U (m2F, add (add MM MM) mF, add mF (add MM MM)) fc;  (* m2+((MM+MM)+m)=m2+(m+(MM+MM)) *)
        val fa2 = addassoc_U (m2F, mF, add MM MM);  (* (m2+m)+(MM+MM) = m2+(m+(MM+MM)) *)
        val m2m_comm = addcomm_U (m2F, mF);         (* (m2+m)=(m+m2) *)
        val m2m_cong = add_cong_l_U (add m2F mF, add mF m2F, add MM MM) m2m_comm;  (* (m2+m)+(MM+MM)=(m+m2)+(MM+MM) *)
        val rhs_norm = oeq_trans_U OF [oeq_trans_U OF [oeq_trans_U OF [oeq_trans_U OF [rhs1, fa], fac], oeq_sym_U OF [fa2]], m2m_cong];
                       (* (p*m2 + m) = (m+m2)+(MM+MM) *)
      in oeq_trans_U OF [lhs_norm, oeq_sym_U OF [rhs_norm]] end;   (* (q*m + m2) = (p*m2 + m) *)
    val () = out "LS_IDENT_READY\n";

    (* lt m p and lt m2 q (m < p=Suc(m+m), m2 < q=Suc(m2+m2)) *)
    val ltmp = lt_m_p_U pF mF hPp hOp;     (* lt m p *)
    val ltm2q = lt_m_p_U qF m2F hPq hOq;   (* lt m2 q *)
    (* bound : lt (q*m)(p*(Suc m2)).  q*m <= q*m+m2 = p*m2+m [ls_ident] < p*m2+p = p*(Suc m2). *)
    val bound_qm =
      let
        val le_qm = le_add_U_at (mult qF mF, m2F);   (* le (q*m)(q*m + m2) *)
        val le_qm2 = oeq_rw_U (Term.lambda (Free("zbq", natT)) (le (mult qF mF) (Free("zbq", natT))),
                       add (mult qF mF) m2F, add (mult pF m2F) mF) ls_ident le_qm;  (* le (q*m)(p*m2 + m) *)
        (* lt (p*m2 + m)(p*m2 + p) from lt m p (add on left p*m2) *)
        val lt_inner = le_add_mono_l_U (mult pF m2F, suc mF, pF) ltmp;
                       (* le (p*m2 + Suc m)(p*m2 + p) ; note lt m p = le (Suc m) p *)
        (* (p*m2 + Suc m) = Suc(p*m2 + m) ; so le (Suc(p*m2+m))(p*m2+p) = lt (p*m2+m)(p*m2+p) *)
        val aSr = addSr_U (mult pF m2F, mF);   (* (p*m2 + Suc m) = Suc(p*m2 + m) *)
        val lt_pm = oeq_rw_U (Term.lambda (Free("zbq2", natT)) (le (Free("zbq2", natT)) (add (mult pF m2F) pF)),
                      add (mult pF m2F)(suc mF), suc (add (mult pF m2F) mF)) aSr lt_inner;
                    (* le (Suc(p*m2+m))(p*m2+p) = lt (p*m2+m)(p*m2+p) *)
        (* p*m2 + p = p*(Suc m2) *)
        val pSm2 = multSucR_U (pF, m2F);   (* p*(Suc m2) = add p (p*m2) *)
        val pSm2c = oeq_trans_U OF [pSm2, addcomm_U (pF, mult pF m2F)];  (* p*(Suc m2) = (p*m2 + p) *)
        val lt_pm2 = oeq_rw_U (Term.lambda (Free("zbq3", natT)) (lt (add (mult pF m2F) mF) (Free("zbq3", natT))),
                       add (mult pF m2F) pF, mult pF (suc m2F)) (oeq_sym_U OF [pSm2c]) lt_pm;
                     (* lt (p*m2+m)(p*(Suc m2)) *)
        (* combine : le (q*m)(p*m2+m) and lt (p*m2+m)(p*(Suc m2)) -> lt (q*m)(p*(Suc m2)) *)
        (* le a b = le (q*m)(p*m2+m) ; lt b c = le (Suc b) c.  le (Suc(q*m))(Suc b) [le_suc_mono le_qm2] ;
           le (Suc b) c -> le (Suc(q*m)) c via... le (Suc(q*m))(Suc b) and le (Suc b) c -> le (Suc(q*m)) c = lt(q*m) c. *)
        val leS = leSucMono_U (mult qF mF, add (mult pF m2F) mF) le_qm2;  (* le (Suc(q*m))(Suc(p*m2+m)) *)
        (* lt (p*m2+m)(p*(Sm2)) = le (Suc(p*m2+m))(p*(Sm2)) ; need le (Suc(q*m))(p*(Sm2)).
           le (Suc(q*m))(Suc(p*m2+m)) and le (Suc(p*m2+m))(p*(Sm2)) [=lt_pm2] -> trans. *)
        val res = le_trans_U_at (suc (mult qF mF), suc (add (mult pF m2F) mF), mult pF (suc m2F)) leS lt_pm2;
      in res end;  (* lt (q*m)(p*(Suc m2)) *)
    (* symmetric bound : lt (p*m2)(q*(Suc m)).  p*m2 <= p*m2 + m = q*m + m2 [ls_ident sym] ... 
       wait ls_ident : q*m + m2 = p*m2 + m.  so p*m2 <= p*m2 + m = q*m + m2 ; and q*m+m2 < q*m+q = q*(Suc m). *)
    val bound_pm2 =
      let
        val le_pm2 = le_add_U_at (mult pF m2F, mF);    (* le (p*m2)(p*m2 + m) *)
        val le_pm2b = oeq_rw_U (Term.lambda (Free("zbp", natT)) (le (mult pF m2F) (Free("zbp", natT))),
                        add (mult pF m2F) mF, add (mult qF mF) m2F) (oeq_sym_U OF [ls_ident]) le_pm2;  (* le (p*m2)(q*m + m2) *)
        val lt_inner = le_add_mono_l_U (mult qF mF, suc m2F, qF) ltm2q;  (* le (q*m + Suc m2)(q*m + q) *)
        val aSr = addSr_U (mult qF mF, m2F);   (* (q*m + Suc m2) = Suc(q*m + m2) *)
        val lt_pm = oeq_rw_U (Term.lambda (Free("zbp2", natT)) (le (Free("zbp2", natT))(add (mult qF mF) qF)),
                      add (mult qF mF)(suc m2F), suc (add (mult qF mF) m2F)) aSr lt_inner;  (* lt (q*m+m2)(q*m+q) *)
        val qSm = multSucR_U (qF, mF);   (* q*(Suc m) = add q (q*m) *)
        val qSmc = oeq_trans_U OF [qSm, addcomm_U (qF, mult qF mF)];  (* q*(Suc m) = (q*m + q) *)
        val lt_qm2 = oeq_rw_U (Term.lambda (Free("zbp3", natT)) (lt (add (mult qF mF) m2F) (Free("zbp3", natT))),
                       add (mult qF mF) qF, mult qF (suc mF)) (oeq_sym_U OF [qSmc]) lt_pm;  (* lt (q*m+m2)(q*(Suc m)) *)
        val leS = leSucMono_U (mult pF m2F, add (mult qF mF) m2F) le_pm2b;
        val res = le_trans_U_at (suc (mult pF m2F), suc (add (mult qF mF) m2F), mult qF (suc mF)) leS lt_qm2;
      in res end;  (* lt (p*m2)(q*(Suc m)) *)
    val () = out "LS_BOUNDS_READY\n";

    (* per-k : le (rdiv(q*k)p) m2  for le k m  (via q*k<=q*m<p*(Suc m2) + rdiv_bound) *)
    fun bound_rdiv_qk kt hkm =   (* hkm : le k m -> le (rdiv(q*k)p) m2 *)
      let
        val le_qk_qm = multLeMono_U (qF, kt, mF) hkm;   (* le (q*k)(q*m) *)
        (* lt (q*k)(p*(Suc m2)) : le (q*k)(q*m) and lt (q*m)(p*(Suc m2)) -> lt (q*k)(p*(Suc m2)) *)
        val leS = leSucMono_U (mult qF kt, mult qF mF) le_qk_qm;  (* le (Suc(q*k))(Suc(q*m)) *)
        val ltqk = le_trans_U_at (suc (mult qF kt), suc (mult qF mF), mult pF (suc m2F)) leS
                     (* need le (Suc(q*m))(p*(Suc m2)) = bound_qm (which is lt(q*m)(p*Sm2)=le(Suc(q*m))(p*Sm2)) *)
                     bound_qm;   (* lt (q*k)(p*(Suc m2)) *)
      in rdiv_bound (pF, mult qF kt, m2F) lt0p ltqk end;
    fun bound_rdiv_pj jt hjm2 =   (* hjm2 : le j m2 -> le (rdiv(p*j)q) m *)
      let
        val le_pj_pm2 = multLeMono_U (pF, jt, m2F) hjm2;   (* le (p*j)(p*m2) *)
        val leS = leSucMono_U (mult pF jt, mult pF m2F) le_pj_pm2;
        val ltpj = le_trans_U_at (suc (mult pF jt), suc (mult pF m2F), mult qF (suc mF)) leS bound_pm2;  (* lt (p*j)(q*(Suc m)) *)
      in rdiv_bound (qF, mult pF jt, mF) lt0q ltpj end;

    (* ~(dvd p (q*k)) for k in 1..m : prime_not_dvd_mult + ~dvd p q + ~dvd p k *)
    fun ndvd_p_qk kt h1k hkm =
      let val nDvdK = not_dvd_in_range_U (pF, mF, kt) hPp hOp h1k hkm   (* ~(dvd p k) *)
      in primeNotDvdMult_U (pF, qF, kt) hPp nDvd_pq nDvdK end;          (* ~(dvd p (q*k)) *)
    fun ndvd_q_pj jt h1j hjm2 =
      let val nDvdJ = not_dvd_in_range_U (qF, m2F, jt) hPq hOq h1j hjm2  (* ~(dvd q j) *)
      in primeNotDvdMult_U (qF, pF, jt) hPq nDvd_qp nDvdJ end;          (* ~(dvd q (p*j)) *)

    (* ===== STEP 1 : LHS1 = sumf(%k. rdiv(q*k)p) m = sumf(%k. cnt(BQ k) m2) m ===== *)
    val rdivQAbs = let val kk = Free("kq_fr", natT) in Term.lambda kk (rdiv (mult qF kk) pF) end;  (* %k. rdiv(q*k)p *)
    val cntBQAbs = let val kk = Free("kq_fr", natT) in Term.lambda kk (cnt (BQ kk) m2F) end;        (* %k. cnt(BQ k) m2 *)
    val step1cong =   (* !!k. le k m ==> rdiv(q*k)p = cnt(BQ k) m2 *)
      let
        val kF = Free("k_s1", natT);
        val hkm = Thm.assume (ctermU (jT (le kF mF)));
        (* case k=0 vs k=Suc : dzos *)
        val dz = dzos_U kF;   (* Disj (oeq k 0)(Ex(%q. oeq k (Suc q))) *)
        val goal = oeq (rdiv (mult qF kF) pF)(cnt (BQ kF) m2F);
        val cZero =
          let
            val hk0 = Thm.assume (ctermU (jT (oeq kF ZeroC)));   (* k = 0 *)
            (* rdiv(q*0)p = 0 : q*0=0 (mult0r), rdiv 0 p = 0 (rdiv_zero) *)
            val qk0 = oeq_rw_U (Term.lambda (Free("zs1a", natT)) (oeq (mult qF kF) (mult qF (Free("zs1a", natT)))),
                        kF, ZeroC) hk0 (oeqRefl_U (mult qF kF));  (* mult q k = mult q 0 *)
            val q0 = mult0r_U2 qF;   (* mult q 0 = 0 *)
            val qkz = oeq_trans_U OF [qk0, q0];   (* mult q k = 0 *)
            val rdq = oeq_rw_U (Term.lambda (Free("zs1b", natT)) (oeq (rdiv (mult qF kF) pF)(rdiv (Free("zs1b", natT)) pF)),
                        mult qF kF, ZeroC) qkz (oeqRefl_U (rdiv (mult qF kF) pF));  (* rdiv(q*k)p = rdiv 0 p *)
            val rz = rdivZero_U pF lt0p;   (* rdiv 0 p = 0 *)
            val lhs0 = oeq_trans_U OF [rdq, rz];   (* rdiv(q*k)p = 0 *)
            (* cnt(BQ k) m2 = cnt(BQ 0) m2 = 0 : BQ 0 = %y. lt(p*y)(q*0) = %y. lt(p*y) 0 = false-pred *)
            (* cnt(BQ k) m2 = cnt(BQ 0) m2 via k=0 ; cnt(BQ 0) m2 = 0 via cnt_full of false? use cnt_cong to false then... 
               simpler: cnt of an always-false pred = 0.  Prove cnt(BQ 0) m2 = 0 by cnt_empty. *)
            val cntBQk_eq = oeq_rw_U (Term.lambda (Free("zs1c", natT)) (oeq (cnt (BQ kF) m2F)(cnt (BQ (Free("zs1c", natT))) m2F)),
                              kF, ZeroC) hk0 (oeqRefl_U (cnt (BQ kF) m2F));  (* cnt(BQ k) m2 = cnt(BQ 0) m2 *)
            (* cnt(BQ 0) m2 = 0 : !!y. ~(BQ 0 (Suc y)) = ~(lt (p*(Suc y))(q*0)) = ~(lt _ 0) ; cnt_empty *)
            val cntBQ0_zero =
              let
                val yF = Free("y_bq0", natT)
                (* BQ 0 (Suc y) = lt (p*(Suc y))(q*0) ; q*0=0 ; ~(lt _ 0) = not_lt_zero *)
                val q0e = mult0r_U2 qF;   (* q*0 = 0 *)
                val nlt = not_lt_zero_U (mult pF (suc yF));   (* ~(lt (p*(Suc y)) 0) *)
                val nBQ = oeq_rw_U (Term.lambda (Free("zs1d", natT)) (neg (lt (mult pF (suc yF)) (Free("zs1d", natT)))),
                            ZeroC, mult qF ZeroC) (oeq_sym_U OF [q0e]) nlt;  (* ~(lt (p*(Suc y))(q*0)) = ~(BQ 0 (Suc y)) *)
                val allNeg = Thm.forall_intr (ctermU yF) nBQ;   (* !!y. ~(BQ 0 (Suc y)) *)
                (* cnt_empty : (!!y. ~(P(Suc y))) ==> cnt P n = 0.  derive via cnt_full of ~? 
                   simpler : induction is overkill ; use a tiny cnt_empty lemma below. *)
              in cnt_empty_at (BQ ZeroC, m2F) allNeg end;
            val cntEq = oeq_trans_U OF [cntBQk_eq, cntBQ0_zero];   (* cnt(BQ k) m2 = 0 *)
            val res = oeq_trans_U OF [lhs0, oeq_sym_U OF [cntEq]];  (* rdiv(q*k)p = cnt(BQ k) m2 *)
          in Thm.implies_intr (ctermU (jT (oeq kF ZeroC))) res end;
        val cSuc =
          let
            val PabsE = Abs("qq", natT, oeq kF (suc (Bound 0)));
            fun body wF (hw:thm) =   (* hw : oeq k (Suc w) ; so k = Suc w, k>=1 *)
              let
                (* le 1 k : k = Suc w, le 1 (Suc w) via le_intro (1, Suc w, w) : Suc w = 1 + w *)
                val le1k = let val aS = addSuc_U (ZeroC, wF); val a0 = add0_U wF;
                               val sum = oeq_trans_U OF [aS, Succong_U a0];   (* (Suc 0 + w) = Suc w *)
                               val le1Sw = le_intro_U (suc ZeroC, suc wF, wF) (oeq_sym_U OF [sum])  (* le 1 (Suc w) *)
                           in oeq_rw_U (Term.lambda (Free("zs1e", natT)) (le (suc ZeroC) (Free("zs1e", natT))),
                                suc wF, kF) (oeq_sym_U OF [hw]) le1Sw end;  (* le 1 k *)
                val nd = ndvd_p_qk kF le1k hkm;          (* ~(dvd p (q*k)) *)
                val bnd = bound_rdiv_qk kF hkm;          (* le (rdiv(q*k)p) m2 *)
                val fc = floor_as_count_at (pF, mult qF kF, m2F) lt0p nd bnd;  (* cnt(ltPredAbs(p,q*k)) m2 = rdiv(q*k)p *)
                (* ltPredAbs(p, q*k) = BQ k ; so cnt(BQ k) m2 = rdiv(q*k)p ; sym -> goal *)
                val res = oeq_sym_U OF [fc];   (* rdiv(q*k)p = cnt(BQ k) m2 *)
              in res end;
          in Thm.implies_intr (ctermU (jT (mkExSuc kF)))
               (exE_U_at (PabsE, goal) (Thm.assume (ctermU (jT (mkExSuc kF)))) "w_s1" body) end;
        val res = disjE_U_at (oeq kF ZeroC, mkExSuc kF, goal) dz cZero cSuc;
      in Thm.forall_intr (ctermU kF) (Thm.implies_intr (ctermU (jT (le kF mF))) res) end;
    val step1 = sum_cong_U (rdivQAbs, cntBQAbs, mF) step1cong;   (* sumf rdivQ m = sumf cntBQ m *)
    val () = out "LS_STEP1_READY\n";

    (* ===== STEP 2 : LHS2 = sumf(%j. rdiv(p*j)q) m2 = sumf(%j. cnt(rowP j) m) m2 ===== *)
    val rdivPAbs = let val jj = Free("jp_fr", natT) in Term.lambda jj (rdiv (mult pF jj) qF) end;  (* %j. rdiv(p*j)q *)
    val cntRowAbs = let val jj = Free("jp_fr", natT) in Term.lambda jj (cnt (rowP jj) mF) end;      (* %j. cnt(rowP j) m *)
    val step2cong =   (* !!j. le j m2 ==> rdiv(p*j)q = cnt(rowP j) m *)
      let
        val jF = Free("j_s2", natT);
        val hjm2 = Thm.assume (ctermU (jT (le jF m2F)));
        val dz = dzos_U jF;
        val goal = oeq (rdiv (mult pF jF) qF)(cnt (rowP jF) mF);
        val cZero =
          let
            val hj0 = Thm.assume (ctermU (jT (oeq jF ZeroC)));
            val pj0 = oeq_rw_U (Term.lambda (Free("zs2a", natT)) (oeq (mult pF jF) (mult pF (Free("zs2a", natT)))),
                        jF, ZeroC) hj0 (oeqRefl_U (mult pF jF));
            val p0 = mult0r_U2 pF;
            val pjz = oeq_trans_U OF [pj0, p0];   (* p*j = 0 *)
            val rdp = oeq_rw_U (Term.lambda (Free("zs2b", natT)) (oeq (rdiv (mult pF jF) qF)(rdiv (Free("zs2b", natT)) qF)),
                        mult pF jF, ZeroC) pjz (oeqRefl_U (rdiv (mult pF jF) qF));
            val rz = rdivZero_U qF lt0q;
            val lhs0 = oeq_trans_U OF [rdp, rz];   (* rdiv(p*j)q = 0 *)
            (* cnt(rowP j) m = cnt(rowP 0) m = 0 ; rowP 0 = %k. lt(q*k)(p*0) = %k. lt(q*k) 0 = false *)
            val cntEqk = oeq_rw_U (Term.lambda (Free("zs2c", natT)) (oeq (cnt (rowP jF) mF)(cnt (rowP (Free("zs2c", natT))) mF)),
                           jF, ZeroC) hj0 (oeqRefl_U (cnt (rowP jF) mF));   (* cnt(rowP j) m = cnt(rowP 0) m *)
            val cntRow0_zero =
              let
                val kF = Free("k_rp0", natT)
                val p0e = mult0r_U2 pF;   (* p*0 = 0 *)
                val nlt = not_lt_zero_U (mult qF (suc kF));   (* ~(lt (q*(Suc k)) 0) *)
                val nRow = oeq_rw_U (Term.lambda (Free("zs2d", natT)) (neg (lt (mult qF (suc kF)) (Free("zs2d", natT)))),
                             ZeroC, mult pF ZeroC) (oeq_sym_U OF [p0e]) nlt;  (* ~(lt (q*(Suc k))(p*0)) = ~(rowP 0 (Suc k)) *)
                val allNeg = Thm.forall_intr (ctermU kF) nRow;
              in cnt_empty_at (rowP ZeroC, mF) allNeg end;   (* cnt(rowP 0) m = 0 *)
            val cntEq = oeq_trans_U OF [cntEqk, cntRow0_zero];   (* cnt(rowP j) m = 0 *)
            val res = oeq_trans_U OF [lhs0, oeq_sym_U OF [cntEq]];
          in Thm.implies_intr (ctermU (jT (oeq jF ZeroC))) res end;
        val cSuc =
          let
            val PabsE = Abs("qq", natT, oeq jF (suc (Bound 0)));
            fun body wF (hw:thm) =
              let
                val le1j = let val aS = addSuc_U (ZeroC, wF); val a0 = add0_U wF;
                               val sum = oeq_trans_U OF [aS, Succong_U a0];
                               val le1Sw = le_intro_U (suc ZeroC, suc wF, wF) (oeq_sym_U OF [sum])
                           in oeq_rw_U (Term.lambda (Free("zs2e", natT)) (le (suc ZeroC) (Free("zs2e", natT))),
                                suc wF, jF) (oeq_sym_U OF [hw]) le1Sw end;
                val nd = ndvd_q_pj jF le1j hjm2;          (* ~(dvd q (p*j)) *)
                val bnd = bound_rdiv_pj jF hjm2;          (* le (rdiv(p*j)q) m *)
                val fc = floor_as_count_at (qF, mult pF jF, mF) lt0q nd bnd;  (* cnt(ltPredAbs(q,p*j)) m = rdiv(p*j)q *)
                (* ltPredAbs(q, p*j) = %k. lt(q*k)(p*j) = rowP j (aconv) ; goal needs cnt(rowP j) m *)
                val res = oeq_sym_U OF [fc];   (* rdiv(p*j)q = cnt(ltPredAbs(q,p*j)) m *)
              in res end;
          in Thm.implies_intr (ctermU (jT (mkExSuc jF)))
               (exE_U_at (PabsE, goal) (Thm.assume (ctermU (jT (mkExSuc jF)))) "w_s2" body) end;
        val res = disjE_U_at (oeq jF ZeroC, mkExSuc jF, goal) dz cZero cSuc;
      in Thm.forall_intr (ctermU jF) (Thm.implies_intr (ctermU (jT (le jF m2F))) res) end;
    val step2 = sum_cong_U (rdivPAbs, cntRowAbs, m2F) step2cong;   (* sumf rdivP m2 = sumf cntRow m2 *)
    val () = out "LS_STEP2_READY\n";

    (* ===== STEP 3 : CC summed : sumf(%k. cnt(BQ k) m2) m + sumf(%k. cnt(colP k) m2) m = mult m2 (Suc m) =====
       per-k : add (cnt(BQ k) m2)(cnt(colP k) m2) = m2   [CC for k>=1 ; direct for k=0]
       then sum_add + sum_cong + sum_const. *)
    val cntBQ2Abs = let val kk = Free("kc3_fr", natT) in Term.lambda kk (cnt (BQ kk) m2F) end;     (* %k. cnt(BQ k) m2 *)
    val cntColAbs = let val kk = Free("kc3_fr", natT) in Term.lambda kk (cnt (colP kk) m2F) end;   (* %k. cnt(colP k) m2 *)
    val m2constAbs = let val kk = Free("kc3_fr", natT) in Term.lambda kk m2F end;                  (* %k. m2 *)
    val sumBothAbs = let val kk = Free("kc3_fr", natT) in Term.lambda kk (add (cnt (BQ kk) m2F)(cnt (colP kk) m2F)) end;
    val cc_sumcong =   (* !!k. le k m ==> add (cnt(BQ k) m2)(cnt(colP k) m2) = m2 *)
      let
        val kF = Free("k_cc3", natT);
        val hkm = Thm.assume (ctermU (jT (le kF mF)));
        val dz = dzos_U kF;
        val goal = oeq (add (cnt (BQ kF) m2F)(cnt (colP kF) m2F)) m2F;
        val cZero =
          let
            val hk0 = Thm.assume (ctermU (jT (oeq kF ZeroC)));
            (* cnt(BQ 0) m2 = 0 ; cnt(colP 0) m2 = m2 ; add 0 m2 = m2 *)
            val cntBQ0 =   (* cnt(BQ k) m2 = 0 *)
              let val cek = oeq_rw_U (Term.lambda (Free("zc3a", natT)) (oeq (cnt (BQ kF) m2F)(cnt (BQ (Free("zc3a", natT))) m2F)),
                              kF, ZeroC) hk0 (oeqRefl_U (cnt (BQ kF) m2F))   (* cnt(BQ k)m2 = cnt(BQ 0)m2 *)
                  val z = let val yF = Free("y_b3", natT)
                              val q0e = mult0r_U2 qF
                              val nlt = not_lt_zero_U (mult pF (suc yF))
                              val nBQ = oeq_rw_U (Term.lambda (Free("zc3b", natT)) (neg (lt (mult pF (suc yF)) (Free("zc3b", natT)))),
                                          ZeroC, mult qF ZeroC) (oeq_sym_U OF [q0e]) nlt
                          in cnt_empty_at (BQ ZeroC, m2F) (Thm.forall_intr (ctermU yF) nBQ) end
              in oeq_trans_U OF [cek, z] end;   (* cnt(BQ k) m2 = 0 *)
            val cntCol0 =   (* cnt(colP k) m2 = m2 *)
              let val cek = oeq_rw_U (Term.lambda (Free("zc3c", natT)) (oeq (cnt (colP kF) m2F)(cnt (colP (Free("zc3c", natT))) m2F)),
                              kF, ZeroC) hk0 (oeqRefl_U (cnt (colP kF) m2F))   (* cnt(colP k)m2 = cnt(colP 0)m2 *)
                  val full = let val yF = Free("y_c3", natT)
                                 (* colP 0 (Suc y) = lt (q*0)(p*(Suc y)) ; q*0=0 ; lt 0 (p*(Suc y)) holds (p*(Suc y)>0) *)
                                 val q0e = mult0r_U2 qF   (* q*0 = 0 *)
                                 (* lt 0 (p*(Suc y)) : le 1 (p*(Suc y)).  p*(Suc y) = p + p*y >= p >= 1.
                                    use : le 1 p (prime>1 => >=2 => >=1) and le p (p*(Suc y))? 
                                    simpler : p*(Suc y) = add p (p*y) [multSucR] ; le 1 (add p (p*y)) since le 1 p. *)
                                 val pSy = multSucR_U (pF, yF)   (* p*(Suc y) = add p (p*y) *)
                                 val le1p = let val gt1 = prime2_gt1_U pF hPp   (* le 2 p *)
                                                val le12 = le_self_suc_U (suc ZeroC)  (* le 1 2 *)
                                            in le_trans_U_at (suc ZeroC, suc (suc ZeroC), pF) le12 gt1 end  (* le 1 p *)
                                 val le1_ppy = let val lap = le_add_U_at (pF, mult pF yF)  (* le p (add p (p*y)) *)
                                               in le_trans_U_at (suc ZeroC, pF, add pF (mult pF yF)) le1p lap end  (* le 1 (add p (p*y)) *)
                                 val lt0_ppy = oeq_rw_U (Term.lambda (Free("zc3d", natT)) (le (suc ZeroC) (Free("zc3d", natT))),
                                                 add pF (mult pF yF), mult pF (suc yF)) (oeq_sym_U OF [pSy]) le1_ppy   (* le 1 (p*(Suc y)) = lt 0 (p*(Suc y)) *)
                                 (* colP 0 (Suc y) = lt (q*0)(p*(Suc y)) ; rewrite q*0 -> 0 : lt 0 (p*(Suc y)) *)
                                 val colP0 = oeq_rw_U (Term.lambda (Free("zc3e", natT)) (lt (Free("zc3e", natT)) (mult pF (suc yF))),
                                               ZeroC, mult qF ZeroC) (oeq_sym_U OF [q0e]) lt0_ppy   (* lt (q*0)(p*(Suc y)) = colP 0 (Suc y) *)
                             in cnt_full_at (colP ZeroC, m2F) (Thm.forall_intr (ctermU yF) colP0) end   (* cnt(colP 0) m2 = m2 *)
              in oeq_trans_U OF [cek, full] end;   (* cnt(colP k) m2 = m2 *)
            (* add (cnt(BQ k)m2)(cnt(colP k)m2) = add 0 m2 = m2 *)
            val r1 = add_cong_l_U (cnt (BQ kF) m2F, ZeroC, cnt (colP kF) m2F) cntBQ0;   (* add (cntBQ)(cntCol) = add 0 (cntCol) *)
            val r2 = add_cong_r_U (ZeroC, cnt (colP kF) m2F, m2F) cntCol0;              (* add 0 (cntCol) = add 0 m2 *)
            val a0 = add0_U m2F;   (* add 0 m2 = m2 *)
            val res = oeq_trans_U OF [oeq_trans_U OF [r1, r2], a0];
          in Thm.implies_intr (ctermU (jT (oeq kF ZeroC))) res end;
        val cSuc =
          let
            val PabsE = Abs("qq", natT, oeq kF (suc (Bound 0)));
            fun body wF (hw:thm) =
              let
                val le1k = let val aS = addSuc_U (ZeroC, wF); val a0 = add0_U wF;
                               val sum = oeq_trans_U OF [aS, Succong_U a0];
                               val le1Sw = le_intro_U (suc ZeroC, suc wF, wF) (oeq_sym_U OF [sum])
                           in oeq_rw_U (Term.lambda (Free("zc3f", natT)) (le (suc ZeroC) (Free("zc3f", natT))),
                                suc wF, kF) (oeq_sym_U OF [hw]) le1Sw end;   (* le 1 k *)
                (* no-diagonal object-forall for CC : !!y. le (Suc y) m2 --> ~(oeq (p*(Suc y))(q*k)) *)
                val yND = Free("y_nd3", natT);
                val ndHypProp = mkForall (Term.lambda yND (mkImp (le (suc yND) m2F)(neg (oeq (mult pF (suc yND))(mult qF kF)))));
                val ndAllThm =
                  let
                    val hle = Thm.assume (ctermU (jT (le (suc yND) m2F)));   (* le (Suc y) m2 *)
                    val le1y = let val aS = addSuc_U (ZeroC, yND); val a0 = add0_U yND;
                                   val sum = oeq_trans_U OF [aS, Succong_U a0]
                               in le_intro_U (suc ZeroC, suc yND, yND) (oeq_sym_U OF [sum]) end;  (* le 1 (Suc y) *)
                    val ndval = no_diagonal_at (pF,qF,mF,m2F,kF,suc yND) hPp hPq hNe le1k hkm le1y hle hOp hOq;
                                (* ~(oeq (p*(Suc y))(q*k)) *)
                    val obj = impI_U_at (le (suc yND) m2F, neg (oeq (mult pF (suc yND))(mult qF kF)))
                                (Thm.implies_intr (ctermU (jT (le (suc yND) m2F))) ndval);
                  in Thm.forall_intr (ctermU yND) obj end;   (* the object-forall ndHyp *)
                (* CC : cnt(ltPredAbs(p,q*k)) m2 + cnt(aboveAbs(p,q*k)) m2 = m2.
                   ltPredAbs(p,q*k)=BQ k ; aboveAbs(p,q*k)=colP k. *)
                val cc = cnt_complement_at (pF, mult qF kF, m2F) ndAllThm;   (* add (cnt(BQ k)m2)(cnt(colP k)m2) = m2 *)
              in cc end;
          in Thm.implies_intr (ctermU (jT (mkExSuc kF)))
               (exE_U_at (PabsE, goal) (Thm.assume (ctermU (jT (mkExSuc kF)))) "w_cc3" body) end;
        val res = disjE_U_at (oeq kF ZeroC, mkExSuc kF, goal) dz cZero cSuc;
      in Thm.forall_intr (ctermU kF) (Thm.implies_intr (ctermU (jT (le kF mF))) res) end;
    (* sum_add : add (sumf cntBQ2 m)(sumf cntCol m) = sumf sumBoth m ; then sum_cong sumBoth = m2const ; sum_const *)
    val sumAdd = sum_add_U_at (cntBQ2Abs, cntColAbs, mF);   (* add (sumf cntBQ2 m)(sumf cntCol m) = sumf (%k. add(..)(..)) m *)
    val sumBothEq = sum_cong_U (sumBothAbs, m2constAbs, mF) cc_sumcong;   (* sumf sumBoth m = sumf (%k.m2) m *)
    val sumConst = sum_const_at_U (m2F, mF);   (* sumf (%k.m2) m = mult m2 (Suc m) *)
    val cc_total = oeq_trans_U OF [oeq_trans_U OF [sumAdd, sumBothEq], sumConst];
                   (* add (sumf cntBQ2 m)(sumf cntCol m) = mult m2 (Suc m) *)
    val () = out "LS_STEP3_READY\n";

    (* fu_swap at (q,p,m,m2) : sumf (colSummand m2) m = add (cnt(colP 0) m2)(sumf (rowSummand m) m2) *)
    val fu = beta_norm (Drule.infer_instantiate ctxtU
               [(("q_fs",0), ctermU qF),(("p_fs",0), ctermU pF),(("a_fs",0), ctermU mF),(("b_fs",0), ctermU m2F)] fu_swap);
    (* fu : oeq (sumf (%k. cnt(colP k) m2) m) (add (cnt(colP 0) m2)(sumf (%y. cnt(rowP y) m) m2)) *)
    (* the FU column summand uses kcs2_fr ; our cntColAbs uses kc3_fr ; aconv (alpha). *)

    (* cnt(colP 0) m2 = m2  (reuse the cZero full-count argument, standalone) *)
    val col0_eq_m2 =
      let val yF = Free("y_c0", natT)
          val q0e = mult0r_U2 qF
          val pSy = multSucR_U (pF, yF)
          val le1p = let val gt1 = prime2_gt1_U pF hPp
                         val le12 = le_self_suc_U (suc ZeroC)
                     in le_trans_U_at (suc ZeroC, suc (suc ZeroC), pF) le12 gt1 end
          val le1_ppy = let val lap = le_add_U_at (pF, mult pF yF)
                        in le_trans_U_at (suc ZeroC, pF, add pF (mult pF yF)) le1p lap end
          val lt0_ppy = oeq_rw_U (Term.lambda (Free("zc0d", natT)) (le (suc ZeroC) (Free("zc0d", natT))),
                          add pF (mult pF yF), mult pF (suc yF)) (oeq_sym_U OF [pSy]) le1_ppy
          val colP0 = oeq_rw_U (Term.lambda (Free("zc0e", natT)) (lt (Free("zc0e", natT)) (mult pF (suc yF))),
                        ZeroC, mult qF ZeroC) (oeq_sym_U OF [q0e]) lt0_ppy
      in cnt_full_at (colP ZeroC, m2F) (Thm.forall_intr (ctermU yF) colP0) end;   (* cnt(colP 0) m2 = m2 *)

    (* ===== FINAL ALGEBRA =====
       Let SB = sumf (%k.cnt(BQ k) m2) m  [= LHS1 by step1]
           SC = sumf (%k.cnt(colP k) m2) m
           SR = sumf (%y.cnt(rowP y) m) m2  [= LHS2 by step2]
       cc_total : add SB SC = mult m2 (Suc m)
       fu       : SC = add (cnt(colP 0) m2) SR = add m2 SR  [col0_eq_m2]
       mult m2 (Suc m) = add m2 (mult m2 m)  [mult_Suc_right]
       => add SB (add m2 SR) = add m2 (mult m2 m)
       => add m2 (add SB SR) = add m2 (mult m2 m)  [comm/assoc]
       => add SB SR = mult m2 m  [add_left_cancel]
       => SB + SR = mult m2 m = mult m m2  [comm]
       LHS1 + LHS2 = SB + SR = mult m m2. *)
    val SB = sumf cntBQ2Abs mF;     (* sumf (%k. cnt(BQ k) m2) m  (kc3_fr) *)
    val SC = sumf cntColAbs mF;     (* sumf (%k. cnt(colP k) m2) m *)
    val SR = sumf cntRowAbs m2F;    (* sumf (%j. cnt(rowP j) m) m2 (jp_fr) *)
    (* rewrite SC -> add m2 SR in cc_total : first fu : SC = add (cnt(colP 0)m2) SR ; then col0 -> m2 *)
    val fu_m2 = oeq_trans_U OF [fu, add_cong_l_U (cnt (colP ZeroC) m2F, m2F, SR) col0_eq_m2];
                (* SC = add m2 SR  (modulo alpha on the summands) *)
    (* cc_total : add SB SC = mult m2 (Suc m) ; rewrite SC -> add m2 SR *)
    val cc2 = oeq_trans_U OF [oeq_sym_U OF [add_cong_r_U (SB, SC, add m2F SR) fu_m2], cc_total];
              (* add SB (add m2 SR) = mult m2 (Suc m) *)
    val msr = multSucR_U (m2F, mF);   (* mult m2 (Suc m) = add m2 (mult m2 m) *)
    val cc3 = oeq_trans_U OF [cc2, msr];   (* add SB (add m2 SR) = add m2 (mult m2 m) *)
    (* LHS rearrange : add SB (add m2 SR) = add m2 (add SB SR) *)
    val rearr =
      let val a1 = addassoc_U (SB, m2F, SR);   (* (SB + m2) + SR = SB + (m2 + SR) *)
          val c1 = addcomm_U (SB, m2F);        (* (SB + m2) = (m2 + SB) *)
          val c1c = add_cong_l_U (add SB m2F, add m2F SB, SR) c1;  (* (SB+m2)+SR = (m2+SB)+SR *)
          val a2 = addassoc_U (m2F, SB, SR);   (* (m2+SB)+SR = m2+(SB+SR) *)
          (* SB + (m2+SR) = (SB+m2)+SR [assoc sym] = (m2+SB)+SR [comm] = m2+(SB+SR) [assoc] *)
      in oeq_trans_U OF [oeq_trans_U OF [oeq_sym_U OF [a1], c1c], a2] end;
              (* add SB (add m2 SR) = add m2 (add SB SR) *)
    val cc4 = oeq_trans_U OF [oeq_sym_U OF [rearr], cc3];   (* add m2 (add SB SR) = add m2 (mult m2 m) *)
    val sbsr = add_left_cancel_U OF [cc4];   (* add SB SR = mult m2 m *)
    (* now LHS1 = SB [step1] ; LHS2 = SR [step2] *)
    (* step1 : oeq (sumf rdivQAbs m)(sumf cntBQAbs m) ; cntBQAbs (kq_fr) aconv cntBQ2Abs (kc3_fr) = SB *)
    val lhs1_eq = step1;   (* sumf rdivQAbs m = sumf cntBQAbs m  (= SB up to alpha) *)
    val lhs2_eq = step2;   (* sumf rdivPAbs m2 = sumf cntRowAbs m2 = SR *)
    (* combine : add (sumf rdivQAbs m)(sumf rdivPAbs m2) = add SB SR = mult m2 m = mult m m2 *)
    val combineLHS =
      let val c1 = add_cong_l_U (sumf rdivQAbs mF, sumf cntBQAbs mF, sumf rdivPAbs m2F) lhs1_eq;
              (* add (sumf rdivQ m)(sumf rdivP m2) = add (sumf cntBQ m)(sumf rdivP m2) *)
          val c2 = add_cong_r_U (sumf cntBQAbs mF, sumf rdivPAbs m2F, sumf cntRowAbs m2F) lhs2_eq;
              (* = add (sumf cntBQ m)(sumf cntRow m2) *)
      in oeq_trans_U OF [c1, c2] end;
              (* add (sumf rdivQ m)(sumf rdivP m2) = add (sumf cntBQ m)(sumf cntRow m2) = add SB SR (alpha) *)
    val mcomm = multcomm_U2 (m2F, mF);   (* mult m2 m = mult m m2 *)
    val final0 = oeq_trans_U OF [oeq_trans_U OF [combineLHS, sbsr], mcomm];
                 (* add (sumf rdivQ m)(sumf rdivP m2) = mult m m2 *)
    val () = out "LS_FINAL_RAW\n";
    val d5 = Thm.implies_intr (ctermU (jT (oeq(sub qF oneC)(add m2F m2F)))) final0;
    val d4 = Thm.implies_intr (ctermU (jT (oeq(sub pF oneC)(add mF mF)))) d5;
    val d3 = Thm.implies_intr (ctermU (jT (neg(oeq pF qF)))) d4;
    val d2 = Thm.implies_intr (ctermU (jT (prime2 qF))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val () = out "LS_RAW_DONE\n";

(* validate LS *)
val pV_ls=Var(("p_ls",0),natT); val qV_ls=Var(("q_ls",0),natT); val mV_ls=Var(("m_ls",0),natT); val m2V_ls=Var(("m2_ls",0),natT);
val rdivQV = let val kk = Free("kq_fr", natT) in Term.lambda kk (rdiv (mult qV_ls kk) pV_ls) end;
val rdivPV = let val jj = Free("jp_fr", natT) in Term.lambda jj (rdiv (mult pV_ls jj) qV_ls) end;
val i_lattice_symmetry =
  Logic.mk_implies (jT (prime2 pV_ls),
   Logic.mk_implies (jT (prime2 qV_ls),
    Logic.mk_implies (jT (neg(oeq pV_ls qV_ls)),
     Logic.mk_implies (jT (oeq(sub pV_ls oneC)(add mV_ls mV_ls)),
      Logic.mk_implies (jT (oeq(sub qV_ls oneC)(add m2V_ls m2V_ls)),
        jT (oeq (add (sumf rdivQV mV_ls)(sumf rdivPV m2V_ls)) (mult mV_ls m2V_ls)))))));
val r_lattice_symmetry = checkF2c ("lattice_symmetry", lattice_symmetry, i_lattice_symmetry);
val () = if r_lattice_symmetry then out "LATTICE_OK\n" else out "LATTICE_FAILED\n";
val () = out "LS_END\n";

(* ############################################################################
   (QR)  QUADRATIC RECIPROCITY LAW (the finale).
   Apply the Eisenstein lemma BOTH ways + the lattice symmetry exponent law :
     (q/p) : cong p (pow q m)(pow (sub p 1)(sumf (floorAbsU q p) m))
     (p/q) : cong q (pow p m2)(pow (sub q 1)(sumf (floorAbsU p q) m2))
     exponent : parity(add (sumf(floorAbsU q p) m)(sumf(floorAbsU p q) m2)) = parity(mult m m2)
   The CONJUNCTION of these three IS reciprocity : each Legendre symbol is
   (-1)^(sum floor) [Eisenstein], and the two exponents sum to m*m2 mod 2 [lattice],
   so (q/p)(p/q) = (-1)^(m*m2) = (-1)^(((p-1)/2)((q-1)/2)).
   ############################################################################ *)
val () = out "QR_BEGIN\n";

(* parity congruence : oeq a b ==> oeq (parity a)(parity b) *)
fun parity_cong_U (aT, bT) hab =
  oeq_rw_U (Term.lambda (Free("z_pc", natT)) (oeq (parity aT)(parity (Free("z_pc", natT)))), aT, bT) hab (oeqRefl_U (parity aT));

(* eisenstein instantiators *)
fun eisenstein_at (pt, qt, mt) hPp hOddp hPq hOddq hNdvd hSub =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("q",0), ctermU qt),(("m",0), ctermU mt)] eisenstein_lemma)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
       (Thm.implies_elim inst hPp) hOddp) hPq) hOddq) hNdvd) hSub end;

(* lattice_symmetry instantiator *)
fun lattice_at (pt,qt,mt,m2t) hPp hPq hNe hSub_p hSub_q =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p_ls",0), ctermU pt),(("q_ls",0), ctermU qt),(("m_ls",0), ctermU mt),(("m2_ls",0), ctermU m2t)] lattice_symmetry)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPp) hPq) hNe) hSub_p) hSub_q end;
val () = out "QR_INSTANTIATORS_READY\n";

val qr_law =
  let
    val pF=Free("p_qr",natT); val qF=Free("q_qr",natT); val mF=Free("m_qr",natT); val m2F=Free("m2_qr",natT);
    val hPp=Thm.assume(ctermU(jT(prime2 pF)));
    val hPq=Thm.assume(ctermU(jT(prime2 qF)));
    val hNe=Thm.assume(ctermU(jT(neg(oeq pF qF))));
    val hOpar=Thm.assume(ctermU(jT(oeq(parity pF) oneC)));   (* parity p = 1 *)
    val hOqar=Thm.assume(ctermU(jT(oeq(parity qF) oneC)));   (* parity q = 1 *)
    val hSubP=Thm.assume(ctermU(jT(oeq(sub pF oneC)(add mF mF))));
    val hSubQ=Thm.assume(ctermU(jT(oeq(sub qF oneC)(add m2F m2F))));
    val nNe_q = let val h = Thm.assume (ctermU (jT (oeq qF pF)))
                in impI_U_at (oeq qF pF, oFalseC) (Thm.implies_intr (ctermU (jT (oeq qF pF)))
                     (mp_U_at (oeq pF qF, oFalseC) hNe (oeq_sym_U OF [h]))) end;  (* ~(oeq q p) *)
    val nDvd_pq = not_dvd_distinct_primes_U (pF, qF) hPp hPq hNe;   (* ~(dvd p q) *)
    val nDvd_qp = not_dvd_distinct_primes_U (qF, pF) hPq hPp nNe_q; (* ~(dvd q p) *)
    val FLqp = sumf (floorAbsU qF pF) mF;    (* sum_{k} floor(q*k/p) *)
    val FLpq = sumf (floorAbsU pF qF) m2F;   (* sum_{j} floor(p*j/q) *)
    (* (q/p) : cong p (pow q m)(pow (sub p 1) FLqp) *)
    val eis_qp = eisenstein_at (pF, qF, mF) hPp hOpar hPq hOqar nDvd_pq hSubP;
                 (* cong p (pow q m)(pow (sub p 1)(sumf (floorAbsU q p) m)) *)
    (* (p/q) : roles swapped : eisenstein_at (q, p, m2) ; premises : prime2 q, parity q=1, prime2 p, parity p=1, ~(dvd q p), sub q 1 = m2+m2 *)
    val eis_pq = eisenstein_at (qF, pF, m2F) hPq hOqar hPp hOpar nDvd_qp hSubQ;
                 (* cong q (pow p m2)(pow (sub q 1)(sumf (floorAbsU p q) m2)) *)
    (* lattice : add FLqp FLpq = mult m m2 ; note floorAbsU q p aconv rdivQAbs (alpha) *)
    val lat = lattice_at (pF,qF,mF,m2F) hPp hPq hNe hSubP hSubQ;
              (* oeq (add (sumf rdivQAbs m)(sumf rdivPAbs m2)) (mult m m2) *)
    (* parity exponent law : parity (add FLqp FLpq) = parity (mult m m2) *)
    val par_law = parity_cong_U (add FLqp FLpq, mult mF m2F) lat;
                  (* oeq (parity (add FLqp FLpq))(parity (mult m m2)) *)
    (* conjunction : eis_qp /\ eis_pq /\ par_law *)
    val conj1 = conjI_U_at (cong pF (pow qF mF)(pow (sub pF oneC) FLqp),
                            cong qF (pow pF m2F)(pow (sub qF oneC) FLpq)) eis_qp eis_pq;
    val conj = conjI_U_at (mkConj (cong pF (pow qF mF)(pow (sub pF oneC) FLqp))
                                  (cong qF (pow pF m2F)(pow (sub qF oneC) FLpq)),
                           oeq (parity (add FLqp FLpq))(parity (mult mF m2F))) conj1 par_law;
    val d7 = Thm.implies_intr (ctermU (jT (oeq(sub qF oneC)(add m2F m2F)))) conj;
    val d6 = Thm.implies_intr (ctermU (jT (oeq(sub pF oneC)(add mF mF)))) d7;
    val d5 = Thm.implies_intr (ctermU (jT (oeq(parity qF) oneC))) d6;
    val d4 = Thm.implies_intr (ctermU (jT (oeq(parity pF) oneC))) d5;
    val d3 = Thm.implies_intr (ctermU (jT (neg(oeq pF qF)))) d4;
    val d2 = Thm.implies_intr (ctermU (jT (prime2 qF))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val () = out "QR_RAW_DONE\n";

(* validate QR *)
val pV_qr=Var(("p_qr",0),natT); val qV_qr=Var(("q_qr",0),natT); val mV_qr=Var(("m_qr",0),natT); val m2V_qr=Var(("m2_qr",0),natT);
val FLqpV = sumf (floorAbsU qV_qr pV_qr) mV_qr;
val FLpqV = sumf (floorAbsU pV_qr qV_qr) m2V_qr;
val i_qr_law =
  Logic.mk_implies (jT (prime2 pV_qr),
   Logic.mk_implies (jT (prime2 qV_qr),
    Logic.mk_implies (jT (neg(oeq pV_qr qV_qr)),
     Logic.mk_implies (jT (oeq(parity pV_qr) oneC),
      Logic.mk_implies (jT (oeq(parity qV_qr) oneC),
       Logic.mk_implies (jT (oeq(sub pV_qr oneC)(add mV_qr mV_qr)),
        Logic.mk_implies (jT (oeq(sub qV_qr oneC)(add m2V_qr m2V_qr)),
          jT (mkConj (mkConj (cong pV_qr (pow qV_qr mV_qr)(pow (sub pV_qr oneC) FLqpV))
                             (cong qV_qr (pow pV_qr m2V_qr)(pow (sub qV_qr oneC) FLpqV)))
                     (oeq (parity (add FLqpV FLpqV))(parity (mult mV_qr m2V_qr)))))))))));
val r_qr_law = checkF2c ("qr_law", qr_law, i_qr_law);
val () = if r_qr_law then out "QR_LAW_OK\n" else out "QR_LAW_FAILED\n";
val () = out "QR_END\n";

(* ====== F3 MASTER GATE + AXIOM AUDIT ====== *)
val f3AllOK = r_floor_as_count andalso r_no_diagonal andalso r_cnt_complement
              andalso r_fu_swap andalso r_lattice_symmetry andalso r_qr_law;
val () = if f3AllOK then out "F3_ALL_OK\n" else out "F3_PARTIAL\n";
val () = if r_qr_law then out "QUADRATIC_RECIPROCITY_PROVED\n" else out "QR_NOT_CLOSED\n";
val () = out "F3_AXIOM_AUDIT_BEGIN\n";
val allAxF3 = Theory.all_axioms_of thyU;
val () = out ("f3_axiom_count=" ^ Int.toString (length allAxF3) ^ "\n");
val hasEMf3 = List.exists (fn (nm,_) => String.isSuffix "ex_middle" nm orelse nm = "ex_middle") allAxF3;
val () = out ("f3_ex_middle_present=" ^ Bool.toString hasEMf3 ^ "\n");
val badF3 = List.filter (fn nm => let val l = String.map Char.toLower nm in
              String.isSubstring "reciprocity" l orelse String.isSubstring "lattice" l
              orelse String.isSubstring "fubini" l orelse String.isSubstring "diagonal" l
              orelse String.isSubstring "legendre" l orelse String.isSubstring "floor" l
              orelse String.isSubstring "qr_" l orelse String.isSubstring "eisenstein" l
              orelse String.isSubstring "compl" l orelse String.isSubstring "swap" l end)
            (map fst allAxF3);
val () = out ("f3_fabricated_axioms=[" ^ String.concatWith "," badF3 ^ "]\n");
val () = out "F3_AXIOM_ENUM_BEGIN\n";
val () = List.app (fn (nm,_) => out ("  axiom: " ^ nm ^ "\n")) allAxF3;
val () = out "F3_AXIOM_ENUM_END\n";
val () = out "F3_AXIOM_AUDIT_END\n";
val () = out "F3_END\n";
