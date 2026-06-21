(* ============================================================================
   ONLY-IF DIRECTION of Fermat two-square (relational valuation), on ctxtSub.
   Fixed prime p with prime2 p and Ex k. p = 4k+3.  Descent by strong induction.
   ============================================================================ *)
val () = out "OI_ARITH_BEGIN\n";

(* ---------- generic Sub helpers we still need ---------- *)
val conjI_vSub = varify conjI_ax;
fun conjI_atSub (At, Bt) hA hB =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSub
      [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] conjI_vSub)) hA) hB;

val conjunct2_vSub = varify conjunct2_ax;
fun conjunct2_atSub (At, Bt) hConj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSub
      [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] conjunct2_vSub)) hConj;

val le_add_vSub = varify le_add;          (* le ?m (add ?m ?p) *)
fun le_addSub (mt, pt) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("m",0), ctermSub mt), (("p",0), ctermSub pt)] le_add_vSub);

(* lt 0 (Suc r) : le (Suc 0)(Suc r). *)
fun lt0_suc_at rT =
  let
    val a1   = addSucS2_at (ZeroC, rT);            (* add (Suc 0) r = Suc(add 0 r) *)
    val a0   = add0S2_at rT;                        (* add 0 r = r *)
    val a0S  = Suc_cong OF [a0];
    val chain = oeq_trans OF [a1, a0S];             (* add (Suc 0) r = Suc r *)
    val chainSym = oeq_sym OF [chain];
  in le_introS2 (suc ZeroC, suc rT, rT) chainSym end;

val () = out "OI_GENERIC_HELPERS_OK\n";

(* ---------- lt_add_pos : 0<w ==> lt r (add r w) ----------
   w = Suc q.  add r w = add r (Suc q) = Suc(add r q).
   le r (add r q)             [le_add]
   le (Suc r)(Suc(add r q))   [le_suc_mono]
   rewrite Suc(add r q) <- add r (Suc q) = add r w. *)
fun lt_add_pos_at (rT, wT, qT, hWeqSq) =
  (* hWeqSq : oeq w (Suc q)  (caller supplies the Suc-witness) *)
  let
    val zFr    = Free("zlap", natT);                          (* fresh Free for capture-safe rewrite predicate *)
    val leRrq  = le_addSub (rT, qT);                          (* le r (add r q) *)
    val leSS   = le_suc_monoSub (rT, add rT qT) leRrq;        (* le (Suc r)(Suc(add r q)) *)
    val aSr    = addSrS2_at (rT, qT);                         (* add r (Suc q) = Suc(add r q) *)
    val aSrSym = oeq_sym OF [aSr];                            (* Suc(add r q) = add r (Suc q) *)
    (* rewrite the RHS of leSS : le (Suc r) X with X = Suc(add r q) -> add r (Suc q) *)
    val Pabs   = Term.lambda zFr (le (suc rT) zFr);           (* %z. le (Suc r) z  (capture-safe : le has an inner Ex) *)
    val leRw1  = beta_norm (Drule.infer_instantiate ctxtSub
                   [(("P",0), ctermSub Pabs), (("a",0), ctermSub (suc (add rT qT))),
                    (("b",0), ctermSub (add rT (suc qT)))] oeq_subst_vS2) OF [aSrSym, leSS];
    (* now leRw1 : le (Suc r)(add r (Suc q)).  rewrite add r (Suc q) -> add r w via hWeqSq sym *)
    val hSqW   = oeq_sym OF [hWeqSq];                         (* oeq (Suc q) w *)
    val acong  = add_cong_rS2 (rT, suc qT, wT) hSqW;          (* oeq (add r (Suc q))(add r w) *)
    val Pabs2  = Term.lambda zFr (le (suc rT) zFr);
    val leRw   = beta_norm (Drule.infer_instantiate ctxtSub
                   [(("P",0), ctermSub Pabs2), (("a",0), ctermSub (add rT (suc qT))),
                    (("b",0), ctermSub (add rT wT))] oeq_subst_vS2) OF [acong, leRw1];
  in leRw end;  (* le (Suc r)(add r w) = lt r (add r w) *)

val () = out "OI_lt_add_pos_OK\n";

(* ---------- lt_self_mult : given pp = Suc(Suc s) and r = Suc q, prove lt r (mult pp r).
   mult pp r = mult (Suc(Suc s)) r = add r (mult (Suc s) r)   [mult_Suc]
   Let W = mult (Suc s) r = add r (mult s r) [mult_Suc] = Suc(add q (mult s r)) since r=Suc q.
   So mult pp r = add r W with W = Suc(add q (mult s r)) > 0 -> lt r (add r W) [lt_add_pos]
   then rewrite add r W -> mult pp r. *)
fun lt_self_mult_at (ppT, rT, sT, qT, hPP, hR) =
  (* hPP : oeq pp (Suc(Suc s)) ; hR : oeq r (Suc q) *)
  let
    val WT   = mult (suc sT) rT;                              (* W = (Suc s) * r *)
    (* mult pp r = mult (Suc(Suc s)) r : rewrite pp via hPP *)
    val cpp  = mult_cong_lS2 (ppT, suc (suc sT), rT) hPP;     (* oeq (mult pp r)(mult (Suc(Suc s)) r) *)
    val mS   = multSucS2_at (suc sT, rT);                     (* mult (Suc(Suc s)) r = add r (mult (Suc s) r) = add r W *)
    val ppEq = oeq_trans OF [cpp, mS];                        (* oeq (mult pp r)(add r W) *)
    (* W = (Suc s)*r = add r (mult s r) [mult_Suc]; with r = Suc q : add r (mult s r) = add (Suc q)(mult s r) = Suc(add q (mult s r)).
       To use lt_add_pos we need oeq W (Suc Wq) for some Wq. *)
    val mSW  = multSucS2_at (sT, rT);                         (* W = (Suc s)*r = add r (mult s r) *)
    (* rewrite add r (mult s r) using r = Suc q : add (Suc q)(mult s r) = Suc(add q (mult s r)) *)
    val crq  = add_cong_lS2 (rT, suc qT, mult sT rT) hR;      (* oeq (add r (mult s r))(add (Suc q)(mult s r)) *)
    val aSq  = addSucS2_at (qT, mult sT rT);                  (* add (Suc q)(mult s r) = Suc(add q (mult s r)) *)
    val Wsuc = oeq_trans OF [mSW, oeq_trans OF [crq, aSq]];   (* oeq W (Suc(add q (mult s r))) *)
    (* lt r (add r W) via lt_add_pos with w = W, witness q' = add q (mult s r) *)
    val ltrW = lt_add_pos_at (rT, WT, add qT (mult sT rT), Wsuc);  (* le (Suc r)(add r W) *)
    (* rewrite add r W -> mult pp r via (oeq_sym ppEq) *)
    val ppEqSym = oeq_sym OF [ppEq];                          (* oeq (add r W)(mult pp r) *)
    val zFr2 = Free("zlsm", natT);
    val Pabs = Term.lambda zFr2 (le (suc rT) zFr2);           (* capture-safe *)
    val res  = beta_norm (Drule.infer_instantiate ctxtSub
                 [(("P",0), ctermSub Pabs), (("a",0), ctermSub (add rT WT)),
                  (("b",0), ctermSub (mult ppT rT))] oeq_subst_vS2) OF [ppEqSym, ltrW];
  in res end;  (* le (Suc r)(mult pp r) = lt r (mult pp r) *)

val () = out "OI_lt_self_mult_OK\n";

(* ---------- sq_factor : oeq a (mult p a') ==> oeq (mult a a) (mult (mult p p)(mult a' a'))
   (p*a')*(p*a') = (p*p)*(a'*a').  Reassociation chain. *)
fun sq_factor_at (aT, pT, apT, hPa) =
  (* hPa : oeq a (mult p a') *)
  let
    val pa = mult pT apT;
    (* a*a = (p*a')*(p*a') *)
    val s1 = mult_cong_lS2 (aT, pa, aT) hPa;            (* oeq (mult a a)(mult (p*a') a) *)
    val s2 = mult_cong_rS2 (pa, aT, pa) hPa;            (* oeq (mult (p*a') a)(mult (p*a')(p*a')) *)
    val aaEq = oeq_trans OF [s1, s2];                   (* oeq (mult a a)(mult (p*a')(p*a')) *)
    (* now reassociate (p*a')*(p*a') -> (p*p)*(a'*a') *)
    (* e1 : (p*a')*(p*a') = p*(a'*(p*a'))      [assoc, m=p,n=a',k=(p*a')] *)
    val e1 = multassocS2_at (pT, apT, pa);
    (* a'*(p*a') = (a'*p)*a'   reverse-assoc : assoc gives (a'*p)*a' = a'*(p*a'); sym *)
    val e2a = multassocS2_at (apT, pT, apT);            (* (a'*p)*a' = a'*(p*a') *)
    val e2  = oeq_sym OF [e2a];                         (* a'*(p*a') = (a'*p)*a' *)
    (* (a'*p) = (p*a')  [comm] -> (a'*p)*a' = (p*a')*a' *)
    val cmm = multcommS2_at (apT, pT);                  (* oeq (a'*p)(p*a') *)
    val e3  = mult_cong_lS2 (mult apT pT, mult pT apT, apT) cmm; (* (a'*p)*a' = (p*a')*a' *)
    (* (p*a')*a' = p*(a'*a')  [assoc] *)
    val e4  = multassocS2_at (pT, apT, apT);            (* (p*a')*a' = p*(a'*a') *)
    (* chain inner : a'*(p*a') = p*(a'*a') *)
    val innerChain = oeq_trans OF [e2, oeq_trans OF [e3, e4]]; (* a'*(p*a') = p*(a'*a') *)
    (* p*(a'*(p*a')) = p*(p*(a'*a'))  [cong right] *)
    val e5  = mult_cong_rS2 (pT, mult apT pa, mult pT (mult apT apT)) innerChain;
    (* p*(p*(a'*a')) = (p*p)*(a'*a')  [assoc reverse] *)
    val e6a = multassocS2_at (pT, pT, mult apT apT);    (* (p*p)*(a'*a') = p*(p*(a'*a')) *)
    val e6  = oeq_sym OF [e6a];                         (* p*(p*(a'*a')) = (p*p)*(a'*a') *)
    val reassoc = oeq_trans OF [e1, oeq_trans OF [e5, e6]]; (* (p*a')*(p*a') = (p*p)*(a'*a') *)
  in oeq_trans OF [aaEq, reassoc] end;                  (* a*a = (p*p)*(a'*a') *)

val () = out "OI_sq_factor_OK\n";

(* ---------- factor_n : oeq n (add a2 b2) ==> oeq a2 (mult pp x2) ==> oeq b2 (mult pp y2)
                     ==> oeq n (mult pp (add x2 y2))     where pp = mult p p *)
fun factor_n_at (nT, a2, b2, ppT, x2, y2, hN, hA2, hB2) =
  let
    (* n = a2 + b2 -> (pp*x2) + b2 -> (pp*x2) + (pp*y2) *)
    val s1 = add_cong_lS2 (a2, mult ppT x2, b2) hA2;       (* oeq (add a2 b2)(add (pp*x2) b2) *)
    val s2 = add_cong_rS2 (mult ppT x2, b2, mult ppT y2) hB2; (* oeq (add (pp*x2) b2)(add (pp*x2)(pp*y2)) *)
    val nEq1 = oeq_trans OF [hN, oeq_trans OF [s1, s2]];   (* oeq n (add (pp*x2)(pp*y2)) *)
    (* pp*(x2+y2) = (pp*x2)+(pp*y2)  [left_distrib]; sym *)
    val ld  = ldistS2_at (ppT, x2, y2);                    (* oeq (mult pp (add x2 y2))(add (pp*x2)(pp*y2)) *)
    val ldS = oeq_sym OF [ld];                             (* oeq (add (pp*x2)(pp*y2))(mult pp (add x2 y2)) *)
  in oeq_trans OF [nEq1, ldS] end;                         (* oeq n (mult pp (add x2 y2)) *)

val () = out "OI_factor_n_OK\n";

(* ---------- pow_step : oeq (pow p (Suc(Suc v)))(mult (mult p p)(pow p v)) ---------- *)
fun pow_step_at (pT, vT) =
  let
    val ps1 = powSucS2_at (pT, suc vT);                    (* pow p (Suc(Suc v)) = p * pow p (Suc v) *)
    val ps2 = powSucS2_at (pT, vT);                        (* pow p (Suc v) = p * pow p v *)
    val cong = mult_cong_rS2 (pT, pow pT (suc vT), mult pT (pow pT vT)) ps2; (* p*pow p(Sv) = p*(p*pow p v) *)
    val chain1 = oeq_trans OF [ps1, cong];                 (* pow p (SSv) = p*(p*pow p v) *)
    val assoc = multassocS2_at (pT, pT, pow pT vT);        (* (p*p)*pow p v = p*(p*pow p v) *)
    val assocS = oeq_sym OF [assoc];                       (* p*(p*pow p v) = (p*p)*pow p v *)
  in oeq_trans OF [chain1, assocS] end;                    (* pow p (SSv) = (p*p)*pow p v *)

val () = out "OI_pow_step_OK\n";

(* ---------- even_step : oeq v (add j j) ==> oeq (Suc(Suc v))(add (Suc j)(Suc j)) ---------- *)
fun even_step_at (vT, jT, hV) =
  let
    (* add (Suc j)(Suc j) = Suc(add j (Suc j)) [add_Suc] = Suc(Suc(add j j)) [add_Suc_right] *)
    val a1 = addSucS2_at (jT, suc jT);                     (* add (Suc j)(Suc j) = Suc(add j (Suc j)) *)
    val a2 = addSrS2_at (jT, jT);                          (* add j (Suc j) = Suc(add j j) *)
    val a2S = Suc_cong OF [a2];                            (* Suc(add j (Suc j)) = Suc(Suc(add j j)) *)
    val rhsEq = oeq_trans OF [a1, a2S];                    (* add (Suc j)(Suc j) = Suc(Suc(add j j)) *)
    (* Suc(Suc v) = Suc(Suc(add j j)) via hV *)
    val lhsEq = Suc_cong OF [Suc_cong OF [hV]];            (* Suc(Suc v) = Suc(Suc(add j j)) *)
  in oeq_trans OF [lhsEq, oeq_sym OF [rhsEq]] end;         (* Suc(Suc v) = add (Suc j)(Suc j) *)

val () = out "OI_even_step_OK\n";

(* ---------- pp_suc2 : oeq p (Suc(Suc t)) ==> oeq (mult p p)(Suc(Suc S)), S = add t (mult (Suc t) p)
   p*p : rewrite LEFT p -> Suc(Suc t) : (Suc(Suc t))*p = add p (mult (Suc t) p) [mult_Suc].
   add p (mult (Suc t) p) : rewrite p -> Suc(Suc t) on the left add operand :
     add (Suc(Suc t)) X = Suc(add (Suc t) X) = Suc(Suc(add t X))   X = mult (Suc t) p. *)
fun pp_suc2_at (pT, tT, hP) =
  let
    val XT = mult (suc tT) pT;
    (* p*p = (Suc(Suc t))*p *)
    val c1 = mult_cong_lS2 (pT, suc (suc tT), pT) hP;        (* oeq (p*p)((Suc(Suc t))*p) *)
    val ms = multSucS2_at (suc tT, pT);                      (* (Suc(Suc t))*p = add p X *)
    val ppAddp = oeq_trans OF [c1, ms];                      (* oeq (p*p)(add p X) *)
    (* add p X -> add (Suc(Suc t)) X *)
    val cAdd = add_cong_lS2 (pT, suc (suc tT), XT) hP;       (* oeq (add p X)(add (Suc(Suc t)) X) *)
    val aS1  = addSucS2_at (suc tT, XT);                     (* add (Suc(Suc t)) X = Suc(add (Suc t) X) *)
    val aS2  = addSucS2_at (tT, XT);                         (* add (Suc t) X = Suc(add t X) *)
    val aS2S = Suc_cong OF [aS2];                            (* Suc(add (Suc t) X) = Suc(Suc(add t X)) *)
    val addEq = oeq_trans OF [cAdd, oeq_trans OF [aS1, aS2S]]; (* oeq (add p X)(Suc(Suc(add t X))) *)
  in oeq_trans OF [ppAddp, addEq] end;                       (* oeq (p*p)(Suc(Suc(add t X))) *)

val () = out "OI_pp_suc2_OK\n";

(* ---------- mult_pp_zero : oeq (mult pp ZeroC) ZeroC  (= mult_0_right) ---------- *)
val mult_0_right_vSub2 = varify mult_0_right;
fun mult0r_atSub t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_right_vSub2);

val () = out "OI_mult0r_OK\n";
