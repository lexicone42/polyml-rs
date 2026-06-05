val () = print "PAIRBUILD_START\n";
structure Definition = Theory.Definition;
open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite Abbrev BoundedRewrites;
infix THEN THENL THEN1 ORELSE;
fun pr s = print (s ^ "\n");
fun T q = Parse.Term [QUOTE q];
fun ck name th = pr (name ^ "_OK: " ^ Parse.thm_to_string th) handle e => pr (name ^ "_FAIL: " ^ exnMessage e);

(* PAIR_EXISTS : ?p. (\p. ?x y. p = \a b. (a=x)/\(b=y)) p *)
val pairfn = T "\\a:'a b:'b. (a=x) /\\ (b=y)";
val PAIR_EXISTS = Tactical.prove(
   T "?p:'a -> 'b -> bool. (\\p. ?x y. p = (\\a:'a b:'b. (a=x) /\\ (b=y))) p",
   BETA_TAC
    THEN EXISTS_TAC (T "(\\a:'a b:'b. (a=x) /\\ (b=y))")
    THEN EXISTS_TAC (T "x:'a") THEN EXISTS_TAC (T "y:'b") THEN REFL_TAC);
val _ = ck "PAIR_EXISTS" PAIR_EXISTS;

val prod_tydef = Definition.new_type_definition("prod", PAIR_EXISTS);
val _ = ck "prod_tydef" prod_tydef;
val ABS_REP_prod = Drule.define_new_type_bijections
   {ABS="ABS_prod", REP="REP_prod", name="ABS_REP_prod", tyax=prod_tydef};
val _ = ck "ABS_REP_prod" ABS_REP_prod;
val () = print "PAIRBUILD_TYDEF_DONE\n";
