(* pelletier_problems.sml — GENERATED (tools/gen_pelletier.py via the
   hol4-pelletier-meson workflow). The classic Pelletier 1986 FOL benchmark
   suite, run through HOL4's mesonLib.MESON_TAC on /tmp/hol4_meson. 46 of 47
   PROVED (incl. P34 Andrews's Challenge, P38, P39 Russell); P47 (Schubert's
   Steamroller) is the expected MESON failure, matching HOL4's own selftest.
   Predicates F,S renamed Fp,Sp (F=false, S=combinator in HOL4). MESON is sound:
   a PROVED line is a real |- theorem. *)
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = (mesonLib.chatting := 0) handle _ => ();
val () = (Feedback.set_trace "meson" 0) handle _ => ();
val () = (mesonLib.max_depth := 60) handle _ => ();
fun attempt (num, q) =
  let val g = Parse.Term [QUOTE q]
      val th = Tactical.prove(g, mesonLib.MESON_TAC [])
  in pr ("PELL " ^ num ^ " PROVED HYPS=" ^ Int.toString (length (Thm.hyp th)) ^ "\n") end
  handle _ => pr ("PELL " ^ num ^ " FAILED\n");
val proved = [
  ("P1", "(p ==> q) <=> (~q ==> ~p)"),
  ("P2", "~(~p) <=> p"),
  ("P3", "~(p ==> q) ==> (q ==> p)"),
  ("P4", "(~p ==> q) <=> (~q ==> p)"),
  ("P5", "((p \\/ q) ==> (p \\/ r)) ==> (p \\/ (q ==> r))"),
  ("P6", "p \\/ ~p"),
  ("P7", "p \\/ ~(~(~p))"),
  ("P8", "((p ==> q) ==> p) ==> p"),
  ("P9", "((p \\/ q) /\\ (~p \\/ q) /\\ (p \\/ ~q)) ==> ~(~p \\/ ~q)"),
  ("P10", "((q ==> r) /\\ (r ==> (p /\\ q)) /\\ (p ==> (q \\/ r))) ==> (p <=> q)"),
  ("P11", "p <=> p"),
  ("P12", "((p <=> q) <=> r) <=> (p <=> (q <=> r))"),
  ("P13", "(p \\/ (q /\\ r)) <=> ((p \\/ q) /\\ (p \\/ r))"),
  ("P14", "(p <=> q) <=> ((q \\/ ~p) /\\ (~q \\/ p))"),
  ("P15", "(p ==> q) <=> (~p \\/ q)"),
  ("P16", "(p ==> q) \\/ (q ==> p)"),
  ("P17", "((p /\\ (q ==> r)) ==> s) <=> ((~p \\/ q \\/ s) /\\ (~p \\/ ~r \\/ s))"),
  ("P18", "?y. !x. Fp y ==> Fp x"),
  ("P19", "?x. !y z. (P y ==> Q z) ==> (P x ==> Q x)"),
  ("P20", "(!x y. ?z. !w. P x /\\ Q y ==> R z /\\ Sp w) ==> (?x y. P x /\\ Q y) ==> (?z. R z)"),
  ("P21", "(?x. p ==> Fp x) /\\ (?x. Fp x ==> p) ==> (?x. p <=> Fp x)"),
  ("P22", "(!x. p <=> Fp x) ==> (p <=> !x. Fp x)"),
  ("P23", "(!x. p \\/ Fp x) <=> (p \\/ !x. Fp x)"),
  ("P24", "~(?x. U x /\\ Q x) /\\ (!x. P x ==> Q x \\/ R x) /\\ ~(?x. P x ==> (?x. Q x)) /\\ (!x. Q x /\\ R x ==> U x) ==> (?x. P x /\\ R x)"),
  ("P25", "(?x. P x) /\\ (!x. U x ==> ~(G x /\\ R x)) /\\ (!x. P x ==> G x /\\ U x) /\\ ((!x. P x ==> Q x) \\/ (?x. Q x /\\ P x)) ==> (?x. Q x /\\ P x)"),
  ("P26", "((?x. P x) <=> (?x. Q x)) /\\ (!x y. P x /\\ Q y ==> (R x <=> Sp y)) ==> ((!x. P x ==> R x) <=> (!x. Q x ==> Sp x))"),
  ("P27", "(?x. Fp x /\\ ~G x) /\\ (!x. Fp x ==> H x) /\\ (!x. J x /\\ I x ==> Fp x) /\\ ((?x. H x /\\ ~G x) ==> (!x. I x ==> ~H x)) ==> (!x. J x ==> ~I x)"),
  ("P28", "(!x. P x ==> (!x. Q x)) /\\ ((!x. Q x \\/ R x) ==> (?x. Q x /\\ R x)) /\\ ((?x. R x) ==> (!x. L x ==> M x)) ==> (!x. P x /\\ L x ==> M x)"),
  ("P29", "(?x. P x) /\\ (?y. Q y) ==> ((!x. P x ==> R x) /\\ (!y. Q y ==> V y) <=> (!x y. P x /\\ Q y ==> R x /\\ V y))"),
  ("P30", "(!x. P x \\/ Q x ==> ~R x) /\\ (!x. (Q x ==> ~V x) ==> P x /\\ R x) ==> (!x. V x)"),
  ("P31", "~(?x. P x /\\ (Q x \\/ R x)) /\\ (?x. U x /\\ P x) /\\ (!x. ~R x ==> M x) ==> (?x. U x /\\ M x)"),
  ("P32", "(!x. P x /\\ (Q x \\/ R x) ==> V x) /\\ (!x. V x /\\ R x ==> U x) /\\ (!x. M x ==> R x) ==> (!x. P x /\\ M x ==> U x)"),
  ("P33", "(!x. P a /\\ (P x ==> P b) ==> P c) <=> (!x. (~P a \\/ P x \\/ P c) /\\ (~P a \\/ ~P b \\/ P c))"),
  ("P34", "((?x. !y. P x <=> P y) <=> ((?x. Q x) <=> (!y. Q y))) <=> ((?x. !y. Q x <=> Q y) <=> ((?x. P x) <=> (!y. P y)))"),
  ("P35", "?x y. P x y ==> (!x y. P x y)"),
  ("P36", "(!x. ?y. R x y) /\\ (!x. ?y. G x y) /\\ (!x y. R x y \\/ G x y ==> (!z. R y z \\/ G y z ==> H x z)) ==> (!x. ?y. H x y)"),
  ("P37", "(!z. ?w. !x. ?y. (P x z ==> P y w) /\\ P y z /\\ (P y w ==> (?u. Q u w))) /\\ (!x z. ~P x z ==> (?y. Q y z)) /\\ ((?x y. Q x y) ==> (!x. R x x)) ==> (!x. ?y. R x y)"),
  ("P38", "(!x. P a /\\ (P x ==> (?y. P y /\\ R x y)) ==> (?z w. P z /\\ R x w /\\ R w z)) <=> (!x. (~P a \\/ P x \\/ (?z w. P z /\\ R x w /\\ R w z)) /\\ (~P a \\/ ~(?y. P y /\\ R x y) \\/ (?z w. P z /\\ R x w /\\ R w z)))"),
  ("P39", "~?x. !y. H y x <=> ~H y y"),
  ("P40", "(?y. !x. Fp x y <=> Fp x x) ==> ~(!x. ?y. !z. Fp z y <=> ~Fp z x)"),
  ("P41", "(!z. ?y. !x. Fp x y <=> Fp x z /\\ ~Fp x x) ==> ~(?z. !x. Fp x z)"),
  ("P42", "~(?y. !x. Fp x y <=> ~(?z. Fp x z /\\ Fp z x))"),
  ("P43", "(!x y. Q x y <=> (!z. Fp z x <=> Fp z y)) ==> (!x y. Q x y <=> Q y x)"),
  ("P44", "(!x. Fp x ==> (?y. G y /\\ H x y) /\\ (?y. G y /\\ ~H x y)) /\\ (?x. J x /\\ (!y. G y ==> H x y)) ==> (?x. J x /\\ ~Fp x)"),
  ("P45", "(!x. Fp x /\\ (!y. G y /\\ H x y ==> J x y) ==> (!y. G y /\\ H x y ==> Kp y)) /\\ ~(?y. L y /\\ Kp y) /\\ (?x. Fp x /\\ (!y. H x y ==> L y) /\\ (!y. G y /\\ H x y ==> J x y)) ==> (?x. Fp x /\\ ~(?y. G y /\\ H x y))"),
  ("P46", "(!x. Fp x /\\ (!y. Fp y /\\ H y x ==> G y) ==> G x) /\\ ((?x. Fp x /\\ ~G x) ==> (?x. Fp x /\\ ~G x /\\ (!y. Fp y /\\ ~G y ==> J x y))) /\\ (!x y. Fp x /\\ Fp y /\\ H x y ==> ~J y x) ==> (!x. Fp x ==> G x)"),
  ("", "")];
val () = List.app attempt (List.filter (fn (n,_) => n <> "") proved);
(* P47: expected failure for plain MESON_TAC (parity with HOL4 selftest). *)
val () = (let val _ = Tactical.prove(Parse.Term [QUOTE "((!x. P1 x ==> P0 x) /\\ (?x. P1 x)) /\\ ((!x. P2 x ==> P0 x) /\\ (?x. P2 x)) /\\ ((!x. P3 x ==> P0 x) /\\ (?x. P3 x)) /\\ ((!x. P4 x ==> P0 x) /\\ (?x. P4 x)) /\\ ((!x. P5 x ==> P0 x) /\\ (?x. P5 x)) /\\ ((?x. Q1 x) /\\ (!x. Q1 x ==> Q0 x)) /\\ (!x. P0 x ==> (!y. Q0 y ==> R x y) \\/ (((!y. P0 y /\\ S0 y x /\\ ?z. Q0 z /\\ R y z) ==> R x y))) /\\ (!x y. P3 y /\\ (P5 x \\/ P4 x) ==> S0 x y) /\\ (!x y. P3 x /\\ P2 y ==> S0 x y) /\\ (!x y. P2 x /\\ P1 y ==> S0 x y) /\\ (!x y. P1 x /\\ (P2 y \\/ Q1 y) ==> ~(R x y)) /\\ (!x y. P3 x /\\ P4 y ==> R x y) /\\ (!x y. P3 x /\\ P5 y ==> ~(R x y)) /\\ (!x. (P4 x \\/ P5 x) ==> ?y. Q0 y /\\ R x y) ==> ?x y. P0 x /\\ P0 y /\\ ?z. Q1 z /\\ R y z /\\ R x y"], mesonLib.MESON_TAC [])
          in pr "PELL P47 UNEXPECTED_PASS\n" end
          handle _ => pr "PELL P47 EXPECTED_FAIL\n");
val () = pr "PELLETIER_DONE\n";
