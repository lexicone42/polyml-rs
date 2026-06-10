(* relation_tail_sweep.sml — per-THEOREM sweep of relationScript's remaining
   ranges, run ON TOP of /tmp/hol4_relation (all shims baked in the image).

   The build-script loop aborts a part at its first failure; this harness
   chunks the source at Theorem/Definition/Inductive boundaries, quote-filters
   and loads each chunk independently, and CONTINUES past failures — one run
   yields the complete OK/FAIL map (and banks every theorem that proves).
   Ranges swept: (A) the EQC tail [EQC_MOVES_IN, WF_DEF) and (B) the WFREC
   tail [WF_PULL, export_theory). Re-exports /tmp/hol4_relation_swept.

   Usage (cwd = vendor/polyml):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 400000000000 \
       /tmp/hol4_relation crates/polyml-bin/tests/hol4_support/relation_tail_sweep.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
infix THEN THENL THEN1 ORELSE;
infix 8 by;
fun (q by tac) =
    Tactical.THEN1 (Q.SUBGOAL_THEN q Tactic.STRIP_ASSUME_TAC,
                    Tactical.THEN (tac, Tactical.NO_TAC));

pr "\nRELATION_SWEEP_START\n";

(* the image's boolLib.save_thm_at is the naive one; strip [attr] suffixes.
   Same for Definition X[attr]: -> new_definition with the raw tagged name
   (this single failure cascaded 70+ static errors in the algebra tail:
   inv_DEF[simp] rejected -> inv unbound -> everything downstream). *)
structure boolLib = struct
  open boolLib
  fun save_thm_at _ (n, th) =
      Theory.save_thm (hd (String.fields (fn c => c = #"[") n), th)
  fun new_definition (n, tm) =
      Theory.Definition.new_definition
        (hd (String.fields (fn c => c = #"[") n), tm)
end;
(* chunks call these UNQUALIFIED (the original file's `open boolLib` header
   is not part of a chunk) — bind the stripped versions at top level too. *)
val new_definition = boolLib.new_definition;
val save_thm = boolLib.save_thm;

(* shadow the image's BasicProvers: its SRW/RW closer used ASM_REWRITE_TAC,
   which LOOPS on permutative assumptions (e.g. `!x y. R x y <=> R y x` from
   symmetric_def — 20 min at 100% cpu). ONCE_ASM_REWRITE + REWRITE is bounded
   and still closes the "use an assumption once" goals. *)
structure BasicProvers = struct
  open BasicProvers
  val closer =
      Tactical.TRY (Tactical.THEN (Rewrite.ONCE_ASM_REWRITE_TAC [],
        Tactical.THEN (Rewrite.REWRITE_TAC [], Tactical.NO_TAC)))
  fun RW_TAC ss thl =
      Tactical.THEN (Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
        simpLib.FULL_SIMP_TAC ss thl), closer)
  val rw_tac = RW_TAC
  fun SRW_TAC frags thl =
      RW_TAC (List.foldl (fn (f, ss) => simpLib.++ (ss, f)) (srw_ss ()) frags) thl
end;

fun readFile path =
    let val is = TextIO.openIn path
        val s = TextIO.inputAll is
    in TextIO.closeIn is; s end;
fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;

val lines =
    String.fields (fn c => c = #"\n")
                  (readFile (HOL ^ "/src/relation/relationScript.sml"));

fun isBoundary l =
    String.isPrefix "Theorem " l orelse String.isPrefix "Definition " l
    orelse String.isPrefix "Inductive " l orelse String.isPrefix "CoInductive " l;
fun chunkName l =
    let val tok = List.nth (String.tokens (fn c => c = #" ") l, 1)
    in hd (String.fields (fn c => c = #":" orelse c = #"[") tok) end
    handle _ => "?";

fun findIdx p =
    let fun go (_, []) = ~1
          | go (i, l :: t) = if p l then i else go (i + 1, t)
    in go (0, lines) end;

val ok = ref 0  and bad = ref 0  and failed = ref ([] : string list);

(* known-looping chunks (FULL_SIMP allocation storm on permutative asms —
   e.g. the symmetric_def rewrite `R x y <=> R y x`); skipped, spliced later. *)
val skip = ["symmetric_inv_image"];

fun runChunk (name, chunkLines) =
  if List.exists (fn s => s = name) skip
  then pr ("CHUNK_SKIP " ^ name ^ " (known loop)\n")
  else
    let val () = pr ("CHUNK_TRY  " ^ name ^ "\n")
        val src = String.concatWith "\n" chunkLines
        val () = writeFile ("/tmp/rsweep_src.sml", src)
        val filtered = HOLSource.inputFile {quietOpen = false, print = fn _ => ()}
                                           "/tmp/rsweep_src.sml"
        val () = writeFile ("/tmp/rsweep_chunk.sml", filtered)
    in
      (PolyML.use "/tmp/rsweep_chunk.sml";
       ok := !ok + 1; pr ("CHUNK_OK   " ^ name ^ "\n"))
      handle e =>
        (bad := !bad + 1; failed := name :: !failed;
         pr ("CHUNK_FAIL " ^ name ^ " :: " ^
             (case e of Fail m => m | _ => exnMessage e) ^ "\n"))
    end;

fun sweep (tag, startPred, stopPred) =
    let
      val si = findIdx startPred
      val ei0 = findIdx stopPred
      val ei = if ei0 < 0 then length lines else ei0   (* no marker -> EOF *)
      val () = pr ("SWEEP " ^ tag ^ " lines " ^ Int.toString (si + 1) ^ ".." ^
                   Int.toString ei ^ "\n")
      val range = List.take (List.drop (lines, si), ei - si)
      (* split range at boundaries; boundary line starts a new chunk *)
      fun go (cur, curName, acc) [] = List.rev ((curName, List.rev cur) :: acc)
        | go (cur, curName, acc) (l :: t) =
            if isBoundary l andalso not (null cur)
            then go ([l], chunkName l, (curName, List.rev cur) :: acc) t
            else go (l :: cur, curName, acc) t
      val chunks =
          case range of
              [] => []
            | l0 :: t => go ([l0], chunkName l0, []) t
    in
      List.app runChunk chunks
    end;

val () = sweep ("EQC-tail",
                String.isPrefix "Theorem EQC_MOVES_IN",
                String.isPrefix "val WF_DEF");
val () = sweep ("WFREC-tail",
                String.isPrefix "Theorem WF_PULL",
                fn l => String.isPrefix "val _ = export_theory" l);

val () = pr ("SWEEP_SUMMARY ok=" ^ Int.toString (!ok) ^ " fail=" ^
             Int.toString (!bad) ^ "\n");
val () = pr ("SWEEP_FAILED " ^ String.concatWith "," (List.rev (!failed)) ^ "\n");

(* re-synthesize relationTheory + export the enriched image. *)
val all_named =
    Theory.current_axioms () @ Theory.current_definitions () @
    Theory.current_theorems ();
fun validName s =
    size s > 0 andalso Char.isAlpha (String.sub (s, 0)) andalso
    CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s;
val seen = ref ([] : string list);
val btbl = ref ([] : (string * Thm.thm) list);
val () = app (fn (n, th) =>
                 if validName n andalso not (List.exists (fn m => m = n) (!seen))
                 then (seen := n :: !seen; btbl := (n, th) :: !btbl) else ())
             all_named;
fun bt n = #2 (valOf (List.find (fn (m, _) => m = n) (!btbl)));
val () = pr ("RELATIONTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () =
    let val os = TextIO.openOut "/tmp/relationTheory_gen.sml"
    in TextIO.output (os, "structure relationTheory = struct\n");
       app (fn (n, _) =>
               TextIO.output (os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
           (!btbl);
       TextIO.output (os, "end;\n"); TextIO.closeOut os
    end;
val () = (PolyML.use "/tmp/relationTheory_gen.sml"; pr "STRUCT_OK\n")
         handle e => pr ("STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

val () = pr "EXPORTING /tmp/hol4_relation_swept\n";
val () = PolyML.export ("/tmp/hol4_relation_swept", PolyML.rootFunction);
pr "SWEEP_DONE\n";
