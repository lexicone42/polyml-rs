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
end;
val () = pr "PRELUDE_OK\n";

(* per-module post-filter patches (grammarDB -> current_grammars is the usual
   one; filled in as failures surface). *)
val modPatches : (string * (string * string) list) list = [];

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

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_datatype\n";
       PolyML.export ("/tmp/hol4_datatype", PolyML.rootFunction);
       pr "DATATYPE_CHECKPOINT_DONE\n")
    else pr "DATATYPE_EXPORT_SKIPPED\n";
