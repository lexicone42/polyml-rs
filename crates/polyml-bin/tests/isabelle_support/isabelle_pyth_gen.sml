(* ============================================================================
   PYTHAGOREAN TRIPLES — base stand-up + the GENERATION (parametrization) half.
   Built on common::with_gcd, final context ctxtS2 / ctermS2.

   (1) defines pyth_triple a b c  and  primitive a b  (term builders),
   (2) proves the GENERATION identity (a pure semiring polynomial identity),
       stated SUBTRACTION-FREELY via the le-witness: for n < m there is a d with
          m^2 = n^2 + d   AND   d^2 + (2 m n)^2 = (m^2 + n^2)^2.
       i.e. (m^2 - n^2, 2 m n, m^2 + n^2) is a Pythagorean triple for n < m.

   Slick algebra (avoids the full multinomial blow-up):
     let s = m^2 + n^2,  d the difference (m^2 = n^2 + d),  e = 2 n^2.
     s = d + e           [since s = (n^2 + d) + n^2 = d + 2 n^2]
     s^2 = (d+e)^2 = d^2 + (d*e + (e*d + e*e))             [rdist + ldist]
     and  d*e + (e*d + e*e) = (2 m n)^2,  because
        d*e + e*d = e*d + e*d = 2*(e*d),  and
        2*(e*d) + e*e = e*(2*d + e) = (2 n^2)*(2*d + 2 n^2)
                      = 4 n^2 * (d + n^2) = 4 n^2 * m^2 = (2 m n)^2.
   Everything is congruence + distrib + comm/assoc on ctxtS2.

   The companion CHARACTERIZATION (the hard direction — every primitive triple
   with even leg arises in this form) + the coprime-square-split KEY LEMMA are in
   isabelle_pyth.sml. Together: the full Pythagorean parametrization. This is the
   easy converse (the parametrized form always yields a triple).

   Markers: GEN_OK on success. ultracode wf_494e9c98-2e3.
   ============================================================================ *)
val () = out "PYTH_DELTA_BEGIN\n";

(* ---- DEFINITIONS (term builders) ---- *)
fun pyth_triple (aT, bT, cT) =
  mkConj (lt ZeroC aT)
    (mkConj (lt ZeroC bT)
       (oeq (add (mult aT aT) (mult bT bT)) (mult cT cT)));
fun primitive (aT, bT) =
  let val dF = Free("d_prim", natT)
  in mkForall (Term.lambda dF
       (mkImp (mkConj (dvd dF aT) (dvd dF bT)) (oeq dF (suc ZeroC)))) end;
val () = out "PYTH_DEFS_READY\n";

val twoC = suc (suc ZeroC);

(* ============================================================================
   REUSABLE SEMIRING HELPERS on ctxtS2 (each returns an oeq theorem).
   ============================================================================ *)
(* 2*x = x + x  : 2 = Suc(Suc 0).  mult x 2 via comm, then mult_Suc_right twice. *)
fun two_mult x =
  let
    val comm  = mult_comm_atS (twoC, x);                 (* (2*x) = (x*2) *)
    val s2    = multSrS_at (x, suc ZeroC);              (* (x*Suc(Suc 0)) = (x + (x*Suc 0)) *)
    val s1    = multSrS_at (x, ZeroC);                  (* (x*Suc 0) = (x + (x*0)) *)
    val x0    = mult0rS_at x;                            (* (x*0) = 0 *)
    val s1b   = add_cong_rS (x, mult x ZeroC, ZeroC) x0; (* (x + (x*0)) = (x + 0) *)
    val s1c   = add0rS_at x;                             (* (x + 0) = x *)
    val x1    = oeq_trans OF [s1, oeq_trans OF [s1b, s1c]]; (* (x*Suc 0) = x *)
    val s2b   = add_cong_rS (x, mult x (suc ZeroC), x) x1;   (* (x + (x*Suc 0)) = (x + x) *)
  in oeq_trans OF [comm, oeq_trans OF [s2, s2b]] end;    (* (2*x) = (x + x) *)

(* square of a binomial: ((d+e)*(d+e)) = ((d*d + d*e) + (e*d + e*e)) *)
fun sq_binom (dT, eT) =
  let
    val rd  = rdist_at_S2 (dT, eT, add dT eT);          (* ((d+e)*(d+e)) = (d*(d+e) + e*(d+e)) *)
    val ldd = left_distrib_atS (dT, dT, eT);            (* (d*(d+e)) = (d*d + d*e) *)
    val lde = left_distrib_atS (eT, dT, eT);            (* (e*(d+e)) = (e*d + e*e) *)
    val c1  = add_cong_lS (mult dT (add dT eT), add (mult dT dT) (mult dT eT), mult eT (add dT eT)) ldd;
              (* (d*(d+e) + e*(d+e)) = ((d*d + d*e) + e*(d+e)) *)
    val c2  = add_cong_rS (add (mult dT dT) (mult dT eT), mult eT (add dT eT), add (mult eT dT) (mult eT eT)) lde;
              (* ((d*d + d*e) + e*(d+e)) = ((d*d + d*e) + (e*d + e*e)) *)
  in oeq_trans OF [rd, oeq_trans OF [c1, c2]] end;

val () = out "PYTH_HELPERS_READY\n";

(* ============================================================================
   THE GENERATION IDENTITY (meta-quantified over m,n; conditional on lt n m).
   ============================================================================ *)
val () = out "GEN_BEGIN\n";

val generation =
  let
    val mF = Free("m", natT);
    val nF = Free("n", natT);

    val msq    = mult mF mF;
    val nsq    = mult nF nF;
    val two_mn = mult twoC (mult mF nF);
    val sumsq  = add msq nsq;

    (* goal: EX d. (m^2 = n^2 + d) /\ (d^2 + (2mn)^2 = sumsq^2) *)
    fun goalBodyFor dT =
      mkConj (oeq msq (add nsq dT))
             (oeq (add (mult dT dT) (mult two_mn two_mn)) (mult sumsq sumsq));
    val goalAbs = let val dF = Free("d_goal", natT) in Term.lambda dF (goalBodyFor dF) end;
    val goalEx  = mkEx goalAbs;

    val hLt = Thm.assume (ctermS2 (jT (lt nF mF)));     (* lt n m = le (Suc n) m *)
    val lePabs = Abs("p", natT, oeq mF (add (suc nF) (Bound 0)));

    fun leBody p (hp : thm) =                            (* hp : oeq m (add (Suc n) p) *)
      let
        (* witness d := m^2 - n^2 realized as 2nk + k^2 where k = Suc p, m = n+k.
           But we keep d ABSTRACT through the proof by first proving m^2 = n^2 + d
           for d := add (mult twoC (mult nF kT)) (mult kT kT), then using only
           the relation m^2 = n^2 + d in the identity proof. *)
        val kT  = suc p;                                 (* k = Suc p *)
        (* m = n + k *)
        val s1  = addSucS_at (nF, p);                    (* (Suc n + p) = Suc (n + p) *)
        val s2  = addSrS_at (nF, p);                     (* (n + Suc p) = Suc (n + p) *)
        val s12 = oeq_trans OF [s1, oeq_sym OF [s2]];    (* (Suc n + p) = (n + Suc p) *)
        val m_nk = oeq_trans OF [hp, s12];               (* m = (n + k) *)

        val dT  = add (mult twoC (mult nF kT)) (mult kT kT);   (* 2nk + k^2 *)

        (* ---- (A) m^2 = n^2 + d ----
           m^2 = (n+k)^2 = (n*n + n*k) + (k*n + k*k)   [sq_binom (n,k)]
           and n^2 + d = n*n + (2*(n*k) + k*k).
           Show ((n*n + n*k) + (k*n + k*k)) = (n*n + ((n*k + n*k) + k*k)). *)
        val mm_l  = mult_cong_lS (mF, add nF kT, mF) m_nk;        (* (m*m) = ((n+k)*m) *)
        val mm_r  = mult_cong_rS (add nF kT, mF, add nF kT) m_nk; (* ((n+k)*m) = ((n+k)*(n+k)) *)
        val mm_nk = oeq_trans OF [mm_l, mm_r];                    (* m*m = (n+k)*(n+k) *)
        val sqb   = sq_binom (nF, kT);                            (* ((n+k)*(n+k)) = ((n*n+n*k)+(k*n+k*k)) *)
        val mm_exp= oeq_trans OF [mm_nk, sqb];                    (* m*m = ((n*n+n*k)+(k*n+k*k)) *)

        (* normalize RHS-of-mm_exp into n*n + ((n*k+n*k)+k*k):
             k*n = n*k  [comm]
             ((n*n+n*k)+(n*k+k*k)) = (n*n+(n*k+(n*k+k*k)))  [assoc]
             (n*k+(n*k+k*k)) = ((n*k+n*k)+k*k)              [assoc back] *)
        val nk    = mult nF kT;
        val kn_nk = mult_comm_atS (kT, nF);                      (* (k*n) = (n*k) *)
        val r0    = add_cong_lS (mult kT nF, nk, mult kT kT) kn_nk; (* (k*n + k*k) = (n*k + k*k) *)
        val r0'   = add_cong_rS (add nsq nk, add (mult kT nF) (mult kT kT), add nk (mult kT kT)) r0;
                    (* ((n*n+n*k)+(k*n+k*k)) = ((n*n+n*k)+(n*k+k*k)) *)
        val as1   = addassocS_at (nsq, nk, add nk (mult kT kT));  (* ((n*n+n*k)+(n*k+k*k)) = (n*n+(n*k+(n*k+k*k))) *)
        val as2   = addassocS_at (nk, nk, mult kT kT);            (* ((n*k+n*k)+k*k) = (n*k+(n*k+k*k)) *)
        val inner = add_cong_rS (nsq, add (add nk nk) (mult kT kT), add nk (add nk (mult kT kT))) as2;
                    (* (n*n+((n*k+n*k)+k*k)) = (n*n+(n*k+(n*k+k*k))) *)
        val rhsN  = oeq_trans OF [r0', oeq_trans OF [as1, oeq_sym OF [inner]]];
                    (* ((n*n+n*k)+(k*n+k*k)) = (n*n+((n*k+n*k)+k*k)) *)
        val mm_N  = oeq_trans OF [mm_exp, rhsN];                  (* m*m = (n*n+((n*k+n*k)+k*k)) *)
        (* d = (2*nk + k*k) = ((nk+nk)+k*k) via two_mult nk *)
        val d_eq  = add_cong_lS (mult twoC nk, add nk nk, mult kT kT) (two_mult nk);
                    (* (2*nk + k*k) = ((nk+nk)+k*k) = d in normal form *)
        val nsqd  = add_cong_rS (nsq, dT, add (add nk nk) (mult kT kT)) d_eq;
                    (* (n*n + d) = (n*n + ((nk+nk)+k*k)) *)
        val hA    = oeq_trans OF [mm_N, oeq_sym OF [nsqd]];       (* m*m = (n*n + d)   == (A) *)

        (* ---- (B) the identity: d^2 + (2mn)^2 = sumsq^2 ----
           e := 2 n^2.  s := sumsq = m^2 + n^2.
           (B1) s = d + e :  s = (n^2+d) + n^2  [subst m^2 -> n^2+d]
                              = (d + n^2) + n^2  [comm on n^2+d]
                              = d + (n^2 + n^2)  [assoc]
                              = d + (2 n^2)      [two_mult n^2 backwards]
           (B2) s^2 = (d+e)^2 = (d*d + d*e) + (e*d + e*e)   [sq_binom (d,e)]
           (B3) (d*d + d*e) + (e*d + e*e)
                  = d*d + (d*e + (e*d + e*e))               [assoc]
                  = d*d + ((e*d + e*d) + e*e)               [d*e=e*d comm; (e*d+(e*d+e*e))=((e*d+e*d)+e*e) assoc]
                  = d*d + (2*(e*d) + e*e)                   [two_mult (e*d) backwards]
                  = d*d + (e*(2*d) + e*e)                   [e*d -> ... ; 2*(e*d)=e*(2*d): comm/assoc]
                  = d*d + e*((2*d) + e)                     [left_distrib backwards]
                  = d*d + (2mn)^2                           [e*((2*d)+e) = (2mn)^2, proved separately]
           The big sub-goal is  e*((2*d)+e) = (2mn)*(2mn).
        *)
        val eT  = mult twoC nsq;                          (* e = 2 n^2 *)
        val sT  = sumsq;                                  (* s = m^2 + n^2 *)

        (* (B1) s = d + e *)
        val b1_a = add_cong_lS (msq, add nsq dT, nsq) hA;        (* (m^2 + n^2) = ((n^2+d) + n^2) *)
        val b1_b = add_cong_lS (add nsq dT, add dT nsq, nsq) (addcommS_at (nsq, dT));
                   (* ((n^2+d)+n^2) = ((d+n^2)+n^2) *)
        val b1_c = addassocS_at (dT, nsq, nsq);                  (* ((d+n^2)+n^2) = (d+(n^2+n^2)) *)
        val b1_d = add_cong_rS (dT, add nsq nsq, eT) (oeq_sym OF [two_mult nsq]);
                   (* (d+(n^2+n^2)) = (d + (2*n^2)) = (d+e) *)
        val b1   = oeq_trans OF [b1_a, oeq_trans OF [b1_b, oeq_trans OF [b1_c, b1_d]]];
                   (* s = (d+e) *)
        (* s^2 = (d+e)^2 *)
        val ss_l = mult_cong_lS (sT, add dT eT, sT) b1;          (* (s*s) = ((d+e)*s) *)
        val ss_r = mult_cong_rS (add dT eT, sT, add dT eT) b1;   (* ((d+e)*s) = ((d+e)*(d+e)) *)
        val ss_de= oeq_trans OF [ss_l, ss_r];                    (* s*s = (d+e)*(d+e) *)
        (* (B2) *)
        val sqde = sq_binom (dT, eT);                            (* ((d+e)*(d+e)) = ((d*d+d*e)+(e*d+e*e)) *)
        val ss_e = oeq_trans OF [ss_de, sqde];                   (* s*s = ((d*d+d*e)+(e*d+e*e)) *)

        (* (B3) reduce RHS to d*d + (2mn)^2.
           target: ((d*d + d*e) + (e*d + e*e)) = (d*d + (2mn)^2).
           step1: assoc -> (d*d + (d*e + (e*d + e*e)))
           step2: d*e = e*d -> (d*d + (e*d + (e*d + e*e)))
           step3: assoc back inner -> (d*d + ((e*d + e*d) + e*e))
           step4: e*d+e*d = 2*(e*d) -> (d*d + (2*(e*d) + e*e))
           step5: 2*(e*d) = e*(2*d) -> (d*d + (e*(2*d) + e*e))
           step6: e*(2*d)+e*e = e*((2*d)+e)  [ldist backwards] -> (d*d + e*((2*d)+e))
           step7: e*((2*d)+e) = (2mn)*(2mn) -> (d*d + (2mn)^2)
        *)
        val de = mult dT eT; val ed = mult eT dT; val ee = mult eT eT;
        val st1 = addassocS_at (mult dT dT, de, add ed ee);     (* ((d*d+d*e)+(e*d+e*e)) = (d*d + (d*e + (e*d+e*e))) *)
        val de_ed = mult_comm_atS (dT, eT);                     (* (d*e) = (e*d) *)
        val st2 = add_cong_rS (mult dT dT, add de (add ed ee), add ed (add ed ee))
                    (add_cong_lS (de, ed, add ed ee) de_ed);
                  (* (d*d + (d*e+(e*d+e*e))) = (d*d + (e*d+(e*d+e*e))) *)
        val asInner = addassocS_at (ed, ed, ee);               (* ((e*d+e*d)+e*e) = (e*d+(e*d+e*e)) *)
        val st3 = add_cong_rS (mult dT dT, add ed (add ed ee), add (add ed ed) ee) (oeq_sym OF [asInner]);
                  (* (d*d + (e*d+(e*d+e*e))) = (d*d + ((e*d+e*d)+e*e)) *)
        val st4 = add_cong_rS (mult dT dT, add (add ed ed) ee, add (mult twoC ed) ee)
                    (add_cong_lS (add ed ed, mult twoC ed, ee) (oeq_sym OF [two_mult ed]));
                  (* (d*d + ((e*d+e*d)+e*e)) = (d*d + (2*(e*d) + e*e)) *)
        (* step5: 2*(e*d) = e*(2*d).
           2*(e*d) = (e*d)+(e*d)  [two_mult (e*d)]
           e*(2*d) = e*((2*d)) ; (2*d) = d+d [two_mult d]; e*(d+d) = e*d + e*d [ldist]
           so e*(2*d) = (e*d)+(e*d).  hence 2*(e*d) = e*(2*d). *)
        val two_ed   = two_mult ed;                            (* (2*(e*d)) = ((e*d)+(e*d)) *)
        val e_2d_ld  = left_distrib_atS (eT, dT, dT);          (* (e*(d+d)) = (e*d + e*d) *)
        val two_d    = two_mult dT;                            (* (2*d) = (d+d) *)
        (* e*(2*d) = e*(d+d) : congruence on RIGHT operand of mult e _ *)
        val e2d_eq   = mult_cong_rS (eT, mult twoC dT, add dT dT) two_d;  (* (e*(2*d)) = (e*(d+d)) *)
        val e2d_val  = oeq_trans OF [e2d_eq, e_2d_ld];         (* (e*(2*d)) = (e*d + e*d) *)
        val st5_eq   = oeq_trans OF [two_ed, oeq_sym OF [e2d_val]];  (* (2*(e*d)) = (e*(2*d)) *)
        val st5 = add_cong_rS (mult dT dT, add (mult twoC ed) ee, add (mult eT (mult twoC dT)) ee)
                    (add_cong_lS (mult twoC ed, mult eT (mult twoC dT), ee) st5_eq);
                  (* (d*d + (2*(e*d)+e*e)) = (d*d + (e*(2*d) + e*e)) *)
        (* step6: e*(2*d) + e*e = e*((2*d)+e)  [ldist backwards] *)
        val ld6 = left_distrib_atS (eT, mult twoC dT, eT);    (* (e*((2*d)+e)) = (e*(2*d) + e*e) *)
        val st6 = add_cong_rS (mult dT dT, add (mult eT (mult twoC dT)) ee, mult eT (add (mult twoC dT) eT))
                    (oeq_sym OF [ld6]);
                  (* (d*d + (e*(2*d)+e*e)) = (d*d + e*((2*d)+e)) *)

        (* step7: e*((2*d)+e) = (2mn)*(2mn).
           e = 2 n^2,  (2*d)+e = 2*d + 2*n^2.  Recall d + n^2 = m^2 (= hA backwards).
           e*((2*d)+e) = (2 n^2) * (2*d + 2 n^2)
                       = (2 n^2) * (2*(d + n^2))           [(2*d + 2*n^2) = 2*(d+n^2): ldist backwards]
                       = (2 n^2) * (2 * m^2)               [d+n^2 = m^2]
           and (2mn)*(2mn) : 2mn = 2*(m*n).
           Easiest common normal form: prove BOTH equal to  (4) * (m*m*n*n)? Heavy.
           Instead reduce (2 n^2)*(2 m^2) and (2*(m*n))*(2*(m*n)) to a SHARED
           canonical product  mult twoC (mult twoC (mult (mult mF mF) (mult nF nF)))
           via comm/assoc.  We do this with a dedicated lemma `four_msq_nsq`. *)
        (* (2*d + 2*n^2) = 2*(d + n^2) *)
        val ld7a = left_distrib_atS (twoC, dT, nsq);          (* (2*(d+n^2)) = (2*d + 2*n^2) *)
        (* so (2*d)+e = (2*d)+(2*n^2) ; need e = 2*n^2 which is definitional (eT = mult twoC nsq) OK *)
        val arg_eq = oeq_sym OF [ld7a];                       (* ((2*d)+(2*n^2)) = (2*(d+n^2)) *)
        (* d+n^2 = m^2 : from hA (m^2 = n^2 + d) -> commute -> n^2+d = ... -> need d+n^2 = m^2 *)
        val dn_m  = oeq_trans OF [addcommS_at (dT, nsq), oeq_sym OF [hA]];  (* (d+n^2) = m^2 *)
        val arg_eq2 = oeq_trans OF [arg_eq, mult_cong_rS (twoC, add dT nsq, msq) dn_m];
                    (* ((2*d)+(2*n^2)) = (2 * m^2) *)
        (* e*((2*d)+e) = (2*n^2)*(2*m^2) *)
        val s7a = mult_cong_rS (eT, add (mult twoC dT) eT, mult twoC msq) arg_eq2;
                  (* (e*((2*d)+e)) = ((2*n^2)*(2*m^2)) *)
        (* shared canonical product  P := 2 * (2 * (m^2 * n^2)) *)
        val P = mult twoC (mult twoC (mult msq nsq));
        (* LHS: (2*n^2)*(2*m^2) = P ----------------------------------------- *)
        (* (2*n^2)*(2*m^2) = 2*(n^2*(2*m^2))    [mult_assoc (2,n^2,2*m^2)] *)
        val l1 = mult_assoc_atS (twoC, nsq, mult twoC msq);   (* ((2*n^2)*(2*m^2)) = (2*(n^2*(2*m^2))) *)
        (* n^2*(2*m^2) = (n^2*2)*m^2 ... use assoc back: n^2*(2*m^2) = (n^2*2)*m^2 *)
        val l2a = mult_assoc_atS (nsq, twoC, msq);            (* ((n^2*2)*m^2) = (n^2*(2*m^2)) *)
        (* n^2*2 = 2*n^2  [comm] *)
        val l2b = mult_comm_atS (nsq, twoC);                  (* (n^2*2) = (2*n^2) *)
        val l2c = mult_cong_lS (mult nsq twoC, mult twoC nsq, msq) l2b;  (* ((n^2*2)*m^2) = ((2*n^2)*m^2) *)
        val l2  = oeq_trans OF [oeq_sym OF [l2a], l2c];       (* (n^2*(2*m^2)) = ((2*n^2)*m^2) *)
        (* (2*n^2)*m^2 = 2*(n^2*m^2)  [assoc] ; n^2*m^2 = m^2*n^2 [comm] *)
        val l3a = mult_assoc_atS (twoC, nsq, msq);            (* ((2*n^2)*m^2) = (2*(n^2*m^2)) *)
        val l3b = mult_comm_atS (nsq, msq);                  (* (n^2*m^2) = (m^2*n^2) *)
        val l3c = mult_cong_rS (twoC, mult nsq msq, mult msq nsq) l3b;  (* (2*(n^2*m^2)) = (2*(m^2*n^2)) *)
        val l3  = oeq_trans OF [l3a, l3c];                    (* ((2*n^2)*m^2) = (2*(m^2*n^2)) *)
        (* chain: (2*n^2)*(2*m^2) = 2*(n^2*(2*m^2)) = 2*((2*n^2)*m^2) = 2*(2*(m^2*n^2)) = P *)
        val l4  = mult_cong_rS (twoC, mult nsq (mult twoC msq), mult (mult twoC nsq) msq) l2;
                  (* (2*(n^2*(2*m^2))) = (2*((2*n^2)*m^2)) *)
        val l5  = mult_cong_rS (twoC, mult (mult twoC nsq) msq, mult twoC (mult msq nsq)) l3;
                  (* (2*((2*n^2)*m^2)) = (2*(2*(m^2*n^2))) = P *)
        val lhsP = oeq_trans OF [l1, oeq_trans OF [l4, l5]];  (* ((2*n^2)*(2*m^2)) = P *)
        val s7b  = oeq_trans OF [s7a, lhsP];                  (* (e*((2*d)+e)) = P *)

        (* RHS: (2*(m*n))*(2*(m*n)) = P --------------------------------------
           2*(m*n) * 2*(m*n) = 2*((m*n)*(2*(m*n)))         [assoc (2,mn,2mn)]
           (m*n)*(2*(m*n)) = ((m*n)*2)*(m*n) ... go to 2*((m*n)*(m*n)) then
           (m*n)*(m*n) = m^2*n^2 ? need (m*n)*(m*n) = (m*m)*(n*n).
           We instead reduce 2mn*2mn to P by the SAME canonical route:
             (2*(m*n))*(2*(m*n)) = 2*((m*n)*(2*(m*n)))      [assoc]
             (m*n)*(2*(m*n)) = 2*((m*n)*(m*n))              [comm to pull 2 out: (m*n)*(2*X)=2*((m*n)*X) via assoc+comm]
             (m*n)*(m*n) = (m*m)*(n*n)                      [mn_mn_lemma]
           so 2mn*2mn = 2*(2*((m*m)*(n*n))) = P.
        *)
        val mn = mult mF nF;
        val r1 = mult_assoc_atS (twoC, mn, mult twoC mn);    (* ((2*mn)*(2*mn)) = (2*(mn*(2*mn))) *)
        (* mn*(2*mn) = 2*(mn*mn) : mn*(2*mn) = (mn*2)*mn [assoc back] = (2*mn)*mn [comm] = 2*(mn*mn) [assoc] *)
        val r2a = mult_assoc_atS (mn, twoC, mn);             (* ((mn*2)*mn) = (mn*(2*mn)) *)
        val r2b = mult_comm_atS (mn, twoC);                 (* (mn*2) = (2*mn) *)
        val r2c = mult_cong_lS (mult mn twoC, mult twoC mn, mn) r2b;  (* ((mn*2)*mn) = ((2*mn)*mn) *)
        val r2d = mult_assoc_atS (twoC, mn, mn);            (* ((2*mn)*mn) = (2*(mn*mn)) *)
        val r2  = oeq_trans OF [oeq_sym OF [r2a], oeq_trans OF [r2c, r2d]];  (* (mn*(2*mn)) = (2*(mn*mn)) *)
        (* (m*n)*(m*n) = (m*m)*(n*n) : mn*mn = m*(n*(m*n)) = m*((n*m)*n)=m*((m*n)*n)=m*(m*(n*n)) = (m*m)*(n*n) *)
        val mnmn =
          let
            val q1 = mult_assoc_atS (mF, nF, mn);            (* ((m*n)*mn) = (m*(n*mn)) *)
            (* n*(m*n) = (n*m)*n = (m*n)*n = m*(n*n) *)
            val w1 = mult_assoc_atS (nF, mF, nF);            (* ((n*m)*n) = (n*(m*n)) *)
            val w2 = mult_comm_atS (nF, mF);                (* (n*m) = (m*n) *)
            val w3 = mult_cong_lS (mult nF mF, mult mF nF, nF) w2;  (* ((n*m)*n) = ((m*n)*n) *)
            val w4 = mult_assoc_atS (mF, nF, nF);           (* ((m*n)*n) = (m*(n*n)) *)
            val nmn = oeq_trans OF [oeq_sym OF [w1], oeq_trans OF [w3, w4]];  (* (n*(m*n)) = (m*(n*n)) *)
            val q2 = mult_cong_rS (mF, mult nF mn, mult mF (mult nF nF)) nmn;  (* (m*(n*mn)) = (m*(m*(n*n))) *)
            val q3 = mult_assoc_atS (mF, mF, mult nF nF);   (* ((m*m)*(n*n)) = (m*(m*(n*n))) *)
          in oeq_trans OF [q1, oeq_trans OF [q2, oeq_sym OF [q3]]] end;  (* ((m*n)*(m*n)) = ((m*m)*(n*n)) *)
        val r3 = mult_cong_rS (twoC, mult mn mn, mult msq nsq) mnmn;  (* (2*(mn*mn)) = (2*(m^2*n^2)) *)
        val r2' = oeq_trans OF [r2, r3];                    (* (mn*(2*mn)) = (2*(m^2*n^2)) *)
        val r4 = mult_cong_rS (twoC, mult mn (mult twoC mn), mult twoC (mult msq nsq)) r2';
                 (* (2*(mn*(2*mn))) = (2*(2*(m^2*n^2))) = P *)
        val rhsP = oeq_trans OF [r1, r4];                   (* ((2*mn)*(2*mn)) = P *)
        (* e*((2*d)+e) = (2mn)*(2mn) *)
        val step7 = oeq_trans OF [s7b, oeq_sym OF [rhsP]];  (* (e*((2*d)+e)) = ((2*mn)*(2*mn)) = two_mn^2 *)
        val st7 = add_cong_rS (mult dT dT, mult eT (add (mult twoC dT) eT), mult two_mn two_mn) step7;
                  (* (d*d + e*((2*d)+e)) = (d*d + (2mn)^2) *)

        (* assemble (B3): ss_e RHS -> d*d + (2mn)^2 *)
        val b3 = oeq_trans OF [st1, oeq_trans OF [st2, oeq_trans OF [st3, oeq_trans OF [st4, oeq_trans OF [st5, oeq_trans OF [st6, st7]]]]]];
                 (* ((d*d+d*e)+(e*d+e*e)) = (d*d + (2mn)^2) *)
        val ss_final = oeq_trans OF [ss_e, b3];             (* s*s = (d*d + (2mn)^2) *)
        (* the identity wants  (d^2 + (2mn)^2) = s^2 : symmetrize & commute the sum *)
        val ident0 = oeq_sym OF [ss_final];                (* (d*d + (2mn)^2) = s*s *)
        (* note goal LHS is (mult dT dT) + (mult two_mn two_mn) = exactly (d*d + (2mn)^2) — match *)
        val hB = ident0;                                   (* (d^2 + (2mn)^2) = sumsq^2 *)

        (* assemble the conjunction and exI on d *)
        val conj = conjI_atS2 (oeq msq (add nsq dT),
                               oeq (add (mult dT dT) (mult two_mn two_mn)) (mult sumsq sumsq))
                              hA hB;
        val exG  = exI_atS2 goalAbs dT conj;               (* goalEx *)
      in exG end;

    val body = exE_elimS2 (lePabs, goalEx) hLt "p_le" leBody;
    val disch = Thm.implies_intr (ctermS2 (jT (lt nF mF))) body;
  in varify disch end;

val () = out "GEN_PROVED\n";

(* ---- validation : 0-hyp + aconv intended ---- *)
val mVg = Var (("m",0), natT);
val nVg = Var (("n",0), natT);
val generation_intended =
  let
    val msqV = mult mVg mVg; val nsqV = mult nVg nVg;
    val two_mnV = mult twoC (mult mVg nVg);
    val sumsqV = add msqV nsqV;
    fun bodyFor dT = mkConj (oeq msqV (add nsqV dT))
                            (oeq (add (mult dT dT) (mult two_mnV two_mnV)) (mult sumsqV sumsqV));
    val gAbs = let val dF = Free("d_goal", natT) in Term.lambda dF (bodyFor dF) end;
  in Logic.mk_implies (jT (lt nVg mVg), jT (mkEx gAbs)) end;

val r_gen = checkS2 ("generation", generation, generation_intended);
val () = if r_gen then out "OK generation\n" else out "FAIL generation\n";

(* soundness probe: dropping the lt n m hypothesis would be false (n=m gives
   m^2 = n^2 + 0 ok but the existence of POSITIVE difference fails; more simply
   the *unconditional* statement is not what we proved). Probe: the proved thm
   must NOT be aconv the hypothesis-free existential. *)
val probe_gen =
  let
    val msqV = mult mVg mVg; val nsqV = mult nVg nVg;
    val two_mnV = mult twoC (mult mVg nVg);
    val sumsqV = add msqV nsqV;
    fun bodyFor dT = mkConj (oeq msqV (add nsqV dT))
                            (oeq (add (mult dT dT) (mult two_mnV two_mnV)) (mult sumsqV sumsqV));
    val gAbs = let val dF = Free("d_goal", natT) in Term.lambda dF (bodyFor dF) end;
    val bogus = jT (mkEx gAbs);  (* hypothesis-free *)
  in not ((Thm.prop_of generation) aconv bogus) end;

val () = if r_gen andalso probe_gen then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";
val () = if r_gen andalso probe_gen then out "GEN_OK\n" else out "GEN_FAILED\n";
val () = out "PYTH_DELTA_END\n";
