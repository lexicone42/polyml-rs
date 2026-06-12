(* build_datatype_checkpoint.sml — Stage 8 (FINAL): the HOL4 Datatype package
   on /tmp/hol4_ind_type, exported as /tmp/hol4_datatype.

   The SML assembly on top of ind_typeTheory:
     ParseDatatype_dtype/ParseDatatype (the datatype-spec parser/AST)
     -> ind_types (JRH define_type : tyspec list -> {induction, recursion})
     -> DataSize / EnumType / RecordType / DatatypeSimps
     -> Datatype  (==> Datatype.Datatype q  builds a datatype + registers it
        in TypeBase, generating constructors/induction/recursion/case/size).

   Smoke: Datatype `tree = Leaf | Node tree tree` (via [QUOTE ...], non-enum
   so it routes through ind_types.define_type).

   Usage (cwd = vendor/polyml):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 600000000000 \
       /tmp/hol4_ind_type crates/polyml-bin/tests/hol4_support/build_datatype_checkpoint.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
infix THEN THENL THEN1 ORELSE;
pr "\nDATATYPE_BUILD_START\n";
val () = Globals.interactive := true;

fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;
fun fileExists p =
    (let val is = TextIO.openIn p in TextIO.closeIn is; true end) handle _ => false;
fun replaceAll (s, old, new) =
    let val (pre, suf) = Substring.position old (Substring.full s)
    in if Substring.size suf = 0 then s
       else Substring.string pre ^ new
            ^ replaceAll (Substring.string (Substring.triml (size old) suf), old, new)
    end;

(* ---- Phase 0: prelude. numLib (EnumType opens it; uses ARITH_CONV/REDUCE_CONV
   only, both present) + a couple of helpers. ---- *)
pr "PHASE0_PRELUDE\n";
structure numLib = struct
  val INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC
  val arith_ss = simpLib.++ (boolSimps.bool_ss, numSimps.ARITH_ss)
  val std_ss = simpLib.++ (boolSimps.bool_ss, numSimps.ARITH_ss)
  val ARITH_CONV = Arith.ARITH_CONV
  val REDUCE_CONV = reduceLib.REDUCE_CONV
  val ARITH_PROVE = fn tm => Drule.EQT_ELIM (Arith.ARITH_CONV tm)
  val REDUCE_TAC = Tactic.CONV_TAC reduceLib.REDUCE_CONV
  fun DECIDE tm = ARITH_PROVE tm
                  handle _ => tautLib.TAUT_PROVE tm
  (* numLib re-exports numSyntax — EnumType opens numLib and uses these
     unqualified (num type, term_of_int, mk_less/leq, mk_numeral). *)
  val num = numSyntax.num
  val term_of_int = numSyntax.term_of_int
  val mk_less = numSyntax.mk_less
  val mk_leq = numSyntax.mk_leq
  val mk_numeral = numSyntax.mk_numeral
  val dest_numeral = numSyntax.dest_numeral
  val int_of_term = numSyntax.int_of_term
  val zero_tm = numSyntax.zero_tm
  val dest_less = numSyntax.dest_less
end;

(* ind_types' load-time code calls TypeBase.induction_of for sum$sum (and the
   Datatype package needs sum/option registered for sum-of-products encodings).
   Register them like num/pair were. *)
fun regTy tag rcd = (TypeBase.write (TypeBasePure.gen_datatype_info rcd);
                     pr ("REGTY_OK " ^ tag ^ "\n"))
                    handle e => pr ("REGTY_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n");
val () = regTy "sum" {ax = sumTheory.sum_Axiom, ind = sumTheory.sum_INDUCT,
                      case_defs = [sumTheory.sum_case_def]};
val () = regTy "option" {ax = optionTheory.option_Axiom,
                         ind = optionTheory.option_induction,
                         case_defs = [optionTheory.option_case_def]};
val () = pr "PRELUDE_OK\n";

(* per-module post-filter patches. grammarDB returns NONE for ancestor
   segments -> the `val SOME g = grammarDB{..}` bindings raise Bind; current
   grammars are the right ones on this image. *)
val modPatches : (string * (string * string) list) list =
  [("ind_types",
    [("val SOME ind_type_grammars = grammarDB { thyname = \"ind_type\" }",
      "val ind_type_grammars = Parse.current_grammars ()"),
     ("val SOME ind_type_grammars = grammarDB {thyname=\"ind_type\"}",
      "val ind_type_grammars = Parse.current_grammars ()")]),
   ("RecordType",
    [("val SOME bool_grammars = grammarDB { thyname = \"bool\" }",
      "val bool_grammars = Parse.current_grammars ()"),
     ("val SOME bool_grammars = grammarDB {thyname=\"bool\"}",
      "val bool_grammars = Parse.current_grammars ()")]),
   ("EnumType",
    [("val SOME arithmetic_grammars = Parse.grammarDB { thyname = \"arithmetic\" }",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     ("val SOME arithmetic_grammars = Parse.grammarDB {thyname=\"arithmetic\"}",
      "val arithmetic_grammars = Parse.current_grammars ()")]),
   ("Datatype",
    (* the baked computeLib.write_datatype_info was compiled against the OLD
       stub TypeBasePure, so it can't take the REAL tyinfo Datatype produces
       (type mismatch). It only registers the datatype into the EVAL compset
       (so EVAL reduces constructors) — drop it; TypeBase.export still runs. *)
    [("app computeLib.write_datatype_info tyinfos", "()"),
     ("val SOME arithmetic_grammars = Parse.grammarDB { thyname = \"arithmetic\" }",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     ("val SOME arithmetic_grammars = Parse.grammarDB {thyname=\"arithmetic\"}",
      "val arithmetic_grammars = Parse.current_grammars ()")])];

fun useFilt path =
    let val name = List.last (String.fields (fn c => c = #"/") path)
        val sigf = path ^ ".sig"
        val smlf = path ^ ".sml"
    in
      if not (fileExists smlf) then (pr ("DT_MISSING " ^ name ^ "\n"); false)
      else
        ((if fileExists sigf then (PolyML.use sigf handle _ => ()) else ();
          let val txt0 = HOLSource.inputFile {quietOpen = false, print = fn _ => ()} smlf
              val txt = case List.find (fn (n, _) => n = name) modPatches of
                            NONE => txt0
                          | SOME (_, ps) =>
                              List.foldl (fn ((a, b), t) => replaceAll (t, a, b)) txt0 ps
          in writeFile ("/tmp/dt_filtered.sml", txt); PolyML.use "/tmp/dt_filtered.sml" end;
          pr ("DT_OK   " ^ name ^ "\n"); true)
         handle e => (pr ("DT_FAIL " ^ name ^ " :: " ^
                          (case e of Fail m => m | _ => exnMessage e) ^ "\n"); false))
    end;

(* ---- Phase 1: the datatype-spec parser ---- *)
pr "PHASE1_PARSEDT\n";
val parse = HOL ^ "/src/parse/";
val _ = useFilt (parse ^ "ParseDatatype_dtype");
val _ = useFilt (parse ^ "ParseDatatype");

(* ---- Phase 2: the JRH define_type implementation ---- *)
pr "PHASE2_INDTYPES\n";
val dt = HOL ^ "/src/datatype/";
val _ = useFilt (dt ^ "ind_types");

(* ---- Phase 3: size / enum / record / simps ---- *)
pr "PHASE3_SUPPORT\n";
val _ = useFilt (dt ^ "DataSize");
val _ = useFilt (dt ^ "EnumType");
val _ = useFilt (HOL ^ "/src/datatype/record/RecordType");
val _ = useFilt (dt ^ "DatatypeSimps");

(* ---- Phase 4: the Datatype entrypoint ---- *)
pr "PHASE4_DATATYPE\n";
val _ = useFilt (dt ^ "Datatype");

fun need tag b = pr ((if b then "OK " else "MISSING ") ^ tag ^ "\n");
val () = need "ind_types-define_type"
              ((ignore (PolyML.makestring ind_types.define_type); true) handle _ => false);
val () = need "Datatype-Datatype"
              ((ignore (PolyML.makestring Datatype.Datatype); true) handle _ => false);
val () = pr "DATATYPE_PHASES_DONE\n";

(* ---- THE SMOKE: build a real recursive datatype ---- *)
val smoke = ref true;
fun trySmoke tag f = (f (); pr ("SMOKE_OK " ^ tag ^ "\n"))
                     handle e => (smoke := false;
                                  pr ("SMOKE_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
(* backticks aren't parsed -> [QUOTE ...] frag list (the Datatype quotation form) *)
val () = trySmoke "Datatype-tree" (fn () =>
    Datatype.Datatype [QUOTE "tree = Leaf | Node tree tree"]);
(* the package should have registered `tree` in TypeBase with its induction/
   nchotomy/case theorems *)
val () = trySmoke "tree-in-TypeBase" (fn () =>
    let val ty = Type.mk_thy_type {Thy = Theory.current_theory (), Tyop = "tree", Args = []}
    in case TypeBase.fetch ty of
           SOME _ => ()
         | NONE => raise Fail "tree not registered in TypeBase" end);
val () = pr (if !smoke then "DATATYPE_SMOKE_PASS\n" else "DATATYPE_SMOKE_FAIL\n");

(* ---- Repair numeral MULTIPLICATION in the global computeLib compset ----
   The numeral sweep that built the arithmetic checkpoints banked DEGRADED DB
   entries for the numeral-reduction theorems (DB.fetch "numeral" "numeral_distrib"
   = `T`, etc. — the logged DB_FETCH_FILLER fallback), so the global compset can
   pull NUMERAL out over `*` but cannot reduce the bit-level product, leaving
   3*4 stuck as NUMERAL(BIT1(BIT1 ZERO) * BIT2(BIT1 ZERO)). Addition reduces fine.
   The STRUCTURE-value theorems (numeralTheory.numeral_mult etc.) are CORRECT —
   reduceLib.MUL_CONV uses them and computes 3*4=12 — so re-adding them to the
   global compset repairs computeLib EVAL of multiplication. (These are exactly
   the conv-old Arithconv MUL_RW theorems.) Verified before baking: a copy of
   the_compset with these added reduces 3*4 -> 12 and 12*13 -> 156. *)
val () = (ignore (computeLib.add_thms
   [numeralTheory.numeral_distrib, numeralTheory.numeral_add, numeralTheory.numeral_suc,
    numeralTheory.numeral_iisuc, numeralTheory.numeral_mult, numeralTheory.iDUB_removal,
    numeralTheory.numeral_pre] (!computeLib.the_compset));
   pr "NUMERAL_MULT_COMPSET_PATCHED\n")
  handle e => pr ("NUMERAL_MULT_PATCH_FAIL :: " ^ exnMessage e ^ "\n");
(* sanity: the patched global compset now reduces 3*4 to 12 *)
val () = (let val th = computeLib.CBV_CONV (computeLib.copy (!computeLib.the_compset))
                          (Parse.Term [QUOTE "3 * 4"])
          in pr ("NUMERAL_MULT_CHECK 3*4 = " ^ Parse.term_to_string (boolSyntax.rhs (Thm.concl th)) ^ "\n") end)
         handle e => pr ("NUMERAL_MULT_CHECK_FAIL :: " ^ exnMessage e ^ "\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_datatype\n";
       PolyML.export ("/tmp/hol4_datatype", PolyML.rootFunction);
       pr "DATATYPE_CHECKPOINT_DONE\n")
    else pr "DATATYPE_EXPORT_SKIPPED\n";
