(* build_numsimps_checkpoint.sml — Stage 5: load the arithmetic simpset +
   reduction libraries (src/num/arith/src + src/num/reduce/src) on
   /tmp/hol4_numeral and export /tmp/hol4_numsimps.

   Closure-probe found 32/57 load raw; the rest carry backtick quotations /
   unicode quotes -> EVERY .sml goes through the HOLSource quote-filter
   (harmless when not needed). Fixpoint over (sig, sml) pairs until no
   progress. The two Scripts (reduceScript -> reduceTheory,
   normalizerScript) are attempted last, filtered, with export_theory
   neutralized (they execute on the CURRENT theory).

   Prize: numSimps (ARITH_ss / arith dproc) + reduceLib.REDUCE_CONV —
   real arith_ss retroactively strengthens every remaining sweep.

   Usage (cwd = vendor/polyml):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 1000000000000 \
       /tmp/hol4_numeral crates/polyml-bin/tests/hol4_support/build_numsimps_checkpoint.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
infix THEN THENL THEN1 ORELSE;
infix 8 by;

pr "\nNUMSIMPS_BUILD_START\n";
val () = Globals.interactive := true;

fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;
fun fileExists p =
    (let val is = TextIO.openIn p in TextIO.closeIn is; true end) handle _ => false;

fun useFiltered tag src =
    let val txt = HOLSource.inputFile {quietOpen = false, print = fn _ => ()} src
        val tmp = "/tmp/ns_filtered.sml"
    in writeFile (tmp, txt); PolyML.use tmp end;

(* module list in rough dependency order; fixpoint sorts out the rest. *)
val arithDir = HOL ^ "/src/num/arith/src/";
val reduceDir = HOL ^ "/src/num/reduce/src/";
val mods =
  List.map (fn m => arithDir ^ m)
    ["Arith_cons", "Term_coeffs", "GenPolyCanon", "GenRelNorm", "Int_extra",
     "Thm_convs", "Norm_bool", "Norm_ineqs", "Norm_arith", "NumRelNorms",
     "RJBConv", "Sub_and_cond", "Theorems", "Sol_ranges", "Solve_ineqs",
     "Solve", "Rationals", "Streams", "Sup_Inf", "Exists_arith",
     "Gen_arith", "Instance", "Prenex", "qtools", "Arith", "numSimps"]
  @ List.map (fn m => reduceDir ^ m) ["Boolconv", "reduceLib"];

val loaded = ref ([] : string list);
fun isLoaded m = List.exists (fn x => x = m) (!loaded);
fun tryLoad m =
    if isLoaded m then ()
    else
      let val sigf = m ^ ".sig"
          val smlf = m ^ ".sml"
          val name = List.last (String.fields (fn c => c = #"/") m)
      in
        (if fileExists sigf then (PolyML.use sigf handle _ => ()) else ();
         useFiltered name smlf;
         loaded := m :: !loaded;
         pr ("NS_OK   " ^ name ^ "\n"))
        handle e => pr ("NS_FAIL " ^ name ^ " :: " ^
                        (case e of Fail msg => msg | _ => exnMessage e) ^ "\n")
      end;

fun round n =
    let val before_n = length (!loaded)
        val () = pr ("NS_ROUND " ^ Int.toString n ^ "\n")
        val () = List.app tryLoad mods
    in
      if length (!loaded) > before_n andalso length (!loaded) < length mods
      then round (n + 1) else ()
    end;
val () = round 1;
val () = pr ("NS_LOADED " ^ Int.toString (length (!loaded)) ^ "/" ^
             Int.toString (length mods) ^ "\n");

(* smoke: the arith fragment + decision procedure + REDUCE. *)
val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "numSimps-ARITH_ss"
              ((ignore (PolyML.makestring numSimps.ARITH_ss); true) handle _ => false)
         handle _ => need "numSimps-ARITH_ss" false;
val () = need "reduceLib-REDUCE_CONV"
              ((ignore (PolyML.makestring reduceLib.REDUCE_CONV); true) handle _ => false)
         handle _ => need "reduceLib-REDUCE_CONV" false;
val () = pr (if !smoke then "NUMSIMPS_SMOKE_PASS\n" else "NUMSIMPS_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_numsimps\n";
       PolyML.export ("/tmp/hol4_numsimps", PolyML.rootFunction);
       pr "NUMSIMPS_CHECKPOINT_DONE\n")
    else pr "NUMSIMPS_EXPORT_SKIPPED\n";
