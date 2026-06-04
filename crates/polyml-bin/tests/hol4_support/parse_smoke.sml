(* parse_smoke.sml — smoke test for the /tmp/hol4_parse checkpoint.
   Confirms the HOL4 term/type parser runs: parses a type, a typed variable,
   and a lambda — none of which need any theory constant.

   Usage (cwd = vendor/polyml):
     tools/sml-exp.sh /tmp/hol4_parse \
       crates/polyml-bin/tests/hol4_support/parse_smoke.sml

   QUOTE / frag are in top-level scope via Overlay (baked into the checkpoint),
   so the frag-list quotations below need no extra plumbing.

   Sentinels: PARSE_SMOKE_START, TYPE_OK / TERM_OK / LAMBDA_OK (or *_FAIL),
              ARROW_TYVARS_OK, PARSE_SMOKE_PASS / PARSE_SMOKE_FAIL. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
pr "\nPARSE_SMOKE_START\n";

val ok = ref true;
fun fail m = (ok := false; pr m);

(* 1. a function type built from two type variables *)
val () =
    (let val ty = Parse.Type [QUOTE ":'a -> 'a"]
         val (d, r) = Type.dom_rng ty
     in if Type.is_vartype d andalso Type.is_vartype r
        then pr ("TYPE_OK " ^ Type.type_to_string ty ^ "\n")
        else fail ("TYPE_FAIL not two tyvars: " ^ Type.type_to_string ty ^ "\n")
     end)
    handle e => fail ("TYPE_FAIL " ^ exnMessage e ^ "\n");

(* 2. a typed variable *)
val () =
    (let val tm = Parse.Term [QUOTE "x:'a"]
     in if Term.is_var tm
        then let val (nm, _) = Term.dest_var tm
             in pr ("TERM_OK var=" ^ nm ^ "\n") end
        else fail "TERM_FAIL not a var\n"
     end)
    handle e => fail ("TERM_FAIL " ^ exnMessage e ^ "\n");

(* 3. a lambda abstraction *)
val () =
    (let val tm = Parse.Term [QUOTE "\\x. x"]
     in if Term.is_abs tm
        then let val (bv, bod) = Term.dest_abs tm
             in if Term.aconv bv bod
                then pr "LAMBDA_OK identity\n"
                else pr "LAMBDA_OK\n"
             end
        else fail "LAMBDA_FAIL not an abstraction\n"
     end)
    handle e => fail ("LAMBDA_FAIL " ^ exnMessage e ^ "\n");

(* 4. round-trip: the two tyvars of ':'a -> 'b' are distinct *)
val () =
    (let val ty = Parse.Type [QUOTE ":'a -> 'b"]
         val (d, r) = Type.dom_rng ty
     in if not (d = r)
        then pr "ARROW_TYVARS_OK\n"
        else fail "ARROW_TYVARS_FAIL tyvars collapsed\n"
     end)
    handle e => fail ("ARROW_TYVARS_FAIL " ^ exnMessage e ^ "\n");

val () = if !ok then pr "PARSE_SMOKE_PASS\n" else pr "PARSE_SMOKE_FAIL\n";
