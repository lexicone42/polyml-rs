(* basicSizeTheory built INLINE inside build_defn (Stage 6b), after pairLib
   loads — pairLib installs Definition.new_definition_hook, which makes the
   paired `(x,y)` LHS in min_pair_size/pair_size work (the standalone sweep
   failed precisely because it lacked pairLib's hook). Definitions copied
   verbatim from src/num/theories/basicSizeScript.sml; runs as a fresh
   `basicSize` segment on top of the option chain. *)
fun bsz_pr s = (print s; TextIO.flushOut TextIO.stdOut);
bsz_pr "BASICSIZE_INLINE_START\n";
val () = Theory.new_theory "basicSize";

local open boolLib in
val bool_size_def = new_definition
  ("bool_size_def", Parse.Term [QUOTE "bool_size (b:bool) = 0"]);
val min_pair_size_def = new_definition
  ("min_pair_size_def", Parse.Term [QUOTE "min_pair_size f g (x, y) = f x + g y"]);
val pair_size_def = new_definition
  ("pair_size_def", Parse.Term [QUOTE "pair_size f g (x, y) = 1 + (f x + g y)"]);
val one_size_def = new_definition
  ("one_size_def", Parse.Term [QUOTE "one_size (x:one) = 0"]);
val itself_size_def = new_definition
  ("itself_size_def", Parse.Term [QUOTE "itself_size (x : 'a itself) = 0"]);
val sum_size_def =
 Prim_rec.new_recursive_definition
   {def = Parse.Term [QUOTE "(sum_size (f:'a->num) g (INL x) = f x) /\\ (sum_size f (g:'b->num) (INR y) = g y)"],
    name = "sum_size_def",
    rec_axiom = sumTheory.sum_Axiom};
val full_sum_size_def = new_definition
  ("full_sum_size_def", Parse.Term [QUOTE "full_sum_size f g sum = 1 + (sum_size f g sum)"]);
val option_size_def =
 Prim_rec.new_recursive_definition
   {def = Parse.Term [QUOTE "(option_size f NONE = 0) /\\ (option_size f (SOME x) = 1 + (f x))"],
    name = "option_size_def",
    rec_axiom = optionTheory.option_Axiom};
end;

(* synthesize structure basicSizeTheory from the just-defined names *)
structure basicSizeTheory = struct
  val bool_size_def = bool_size_def
  val min_pair_size_def = min_pair_size_def
  val pair_size_def = pair_size_def
  val one_size_def = one_size_def
  val itself_size_def = itself_size_def
  val sum_size_def = sum_size_def
  val full_sum_size_def = full_sum_size_def
  val option_size_def = option_size_def
end;
val () = bsz_pr "BASICSIZE_INLINE_OK\n";
