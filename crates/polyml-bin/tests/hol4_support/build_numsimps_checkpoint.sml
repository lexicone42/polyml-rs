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

fun replaceAll (s, old, new) =
    let val (pre, suf) = Substring.position old (Substring.full s)
    in if Substring.size suf = 0 then s
       else Substring.string pre ^ new
            ^ replaceAll (Substring.string (Substring.triml (size old) suf), old, new)
    end;
(* numSyntax's only WhileTheory reference is a load-forcing `local open` —
   nothing is used from it (whileTheory is post-Stage-5 material). *)
val modPatches =
  [("numSyntax",
    [("local open arithmeticTheory WhileTheory numeralTheory in end",
      "local open arithmeticTheory numeralTheory in end"),
     (* prim_rec$measure is in the WF tail we didn't port into the (closed)
        prim_rec segment; the arith stack never uses measure syntax. Bind a
        same-type placeholder term so the mk_/dest_ entries typecheck (any
        actual use would dest-fail loudly, not silently succeed). *)
     ("prim_mk_const { Name = \"measure\" , Thy = \"prim_rec\" }",
      "Term.mk_var (\"measure_placeholder\", Type.alpha)"),
     (* same class: constants whose defining chunks need later stages
        (DIVMOD <- pairTheory; WHILE/LEAST <- whileTheory). Batched probe
        showed these are the ONLY 4 misses of numSyntax's ~22 constants. *)
     ("prim_mk_const { Name = \"DIVMOD\" , Thy = \"arithmetic\" }",
      "Term.mk_var (\"DIVMOD_placeholder\", Type.alpha)"),
     ("prim_mk_const { Name = \"WHILE\" , Thy = \"While\" }",
      "Term.mk_var (\"WHILE_placeholder\", Type.alpha)"),
     ("prim_mk_const { Name = \"LEAST\" , Thy = \"While\" }",
      "Term.mk_var (\"LEAST_placeholder\", Type.alpha)")]),
   (* grammarDB stub returns NONE for ancestor segments -> Bind. The
      established fix: current grammars ARE the arithmetic grammars on this
      image. Both raw and filtered token-spacings listed (no-op if absent). *)
   ("Thm_convs",
    [("val SOME arithmetic_grammars = grammarDB {thyname=\"arithmetic\"}",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     ("val SOME arithmetic_grammars = grammarDB { thyname = \"arithmetic\" }",
      "val arithmetic_grammars = Parse.current_grammars ()")]),
   ("numSimps",
    [("val SOME arithmetic_grammars = grammarDB {thyname=\"arithmetic\"}",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     ("val SOME arithmetic_grammars = grammarDB { thyname = \"arithmetic\" }",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     (* BasicProvers shim has no srw_ss fragment registry; registering
        numeral frags is meaningless until real BasicProvers (Stage 3) *)
     ("BasicProvers.logged_addfrags {thyname = \"numeral\"}",
      "(fn (_ : simpLib.ssfrag list) => ())"),
     ("BasicProvers.logged_addfrags { thyname = \"numeral\" }",
      "(fn (_ : simpLib.ssfrag list) => ())")]),
   ("Arithconv",
    (* filter emits: ... $ ( valOf $ grammarDB { thyname = "arithmetic" } ) *)
    [("( valOf $ grammarDB { thyname = \"arithmetic\" } )",
      "(Parse.current_grammars ())"),
     ("valOf $ grammarDB {thyname=\"arithmetic\"}",
      "(Parse.current_grammars ())")]),
   ("Num_conv",
    [("val SOME arithmetic_grammars = grammarDB {thyname=\"arithmetic\"}",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     ("val SOME arithmetic_grammars = grammarDB { thyname = \"arithmetic\" }",
      "val arithmetic_grammars = Parse.current_grammars ()")]),
   ("Boolconv",
    [("val SOME bool_grammars = Parse.grammarDB {thyname=\"bool\"}",
      "val bool_grammars = Parse.current_grammars ()"),
     ("val SOME bool_grammars = Parse.grammarDB { thyname = \"bool\" }",
      "val bool_grammars = Parse.current_grammars ()")]),
   (* numeral_redns mostly restored (TWO_EXP_THM/texp/div2/DIV2_BIT1 landed
      via fleet splices + re-sweeps). 3 entries still unproved: numeral_MIN/
      MAX ("unsolved goals" under our shims) + enumeral_mult (onecount THENL
      chain) — dropped; REDUCE loses MIN/MAX + enhanced-mult fast paths only
      (internal_mult_characterisation still covers mult). Defn is TFL
      (Stage 6). *)
   ("reduceLib",
    [("numeral_MAX, numeral_MIN, numeral_div2,", "numeral_div2,"),
     ("numeral_MAX , numeral_MIN , numeral_div2 ,", "numeral_div2 ,"),
     ("enumeral_mult", "numeral_distrib"),
     ("val _ = Defn.const_eq_ref := NEQ_CONV", "val _ = ()")])];
fun useFiltered tag src =
    let val txt0 = HOLSource.inputFile {quietOpen = false, print = fn _ => ()} src
        val txt = case List.find (fn (n, _) => n = tag) modPatches of
                      NONE => txt0
                    | SOME (_, ps) =>
                        List.foldl (fn ((a, b), t) => replaceAll (t, a, b)) txt0 ps
        val tmp = "/tmp/ns_filtered.sml"
    in writeFile (tmp, txt); PolyML.use tmp end;

(* module list in TOPO order (v6 timed out: the old rough order needed
   multiple 30-min fixpoint rounds; opens-mapped order makes round 1 carry).
   Cross-deps found by grep '^open': Thm_convs<-Theorems; Sol_ranges<-
   Rationals/Sup_Inf/Streams; reduceLib<-Arithconv+computeLib(+Boolconv);
   Exists_arith<-reduceLib. computeLib's LoadableThyData/ThmSetData are
   already baked in the image (relation stage). Arithconv = the LEGACY
   conv-old one (the conv/ one needs cvTheory — the roadmap sidestep). *)
val arithDir = HOL ^ "/src/num/arith/src/";
val reduceDir = HOL ^ "/src/num/reduce/src/";
val computeDir = HOL ^ "/src/compute/src/";
(* mods1 = through computeLib; then reduceTheory is built INLINE (3 thms,
   needs computeLib.lazyfy_thm + re-swept DIV_UNIQUE/MOD_UNIQUE); mods2 =
   the consumers. Num_conv: Norm_arith/Solve_ineqs/Arithconv want it.
   Norm_arith/Norm_ineqs/NumRelNorms/Solve* qualify reduceLib directly ->
   all after reduceLib. Cache (src/simp) is numSimps.sig's dep (not baked). *)
val mods1 =
  [HOL ^ "/src/num/theories/numSyntax",
   HOL ^ "/src/num/theories/Num_conv"]
  @ List.map (fn m => arithDir ^ m)
    ["Arith_cons", "Term_coeffs", "GenPolyCanon", "GenRelNorm", "Int_extra",
     "RJBConv", "Theorems", "Thm_convs", "Norm_bool"]
  (* Streams lives in portableML in this HOL4 (qtools doesn't exist at all) *)
  @ [HOL ^ "/src/portableML/Streams"]
  @ List.map (fn m => arithDir ^ m)
    ["Rationals", "Sup_Inf", "Sol_ranges"]
  @ List.map (fn m => computeDir ^ m)
    ["compute_rules", "clauses", "equations", "computeLib"];
val mods2 =
  [HOL ^ "/src/num/reduce/conv-old/Arithconv"]
  @ List.map (fn m => reduceDir ^ m) ["Boolconv", "reduceLib"]
  @ List.map (fn m => arithDir ^ m)
    ["Norm_arith", "Norm_ineqs", "NumRelNorms", "Solve_ineqs", "Solve",
     "Sub_and_cond", "Exists_arith", "Gen_arith", "Instance", "Prenex",
     "Arith"]
  @ [HOL ^ "/src/simp/src/Cache"]
  @ [arithDir ^ "numSimps"];
val mods = mods1 @ mods2;

(* clauses needs 3 TypeBase(Pure) names beyond the build_simp typed stubs.
   Shadow-widen (baked modules keep the old stub; only newly compiled code
   sees these). Empty typeBase is semantically right: no datatypes are
   registered on this image, so listItems = [] and constructors_of is
   unreachable. *)
structure TypeBasePure = struct
  open TypeBasePure
  type typeBase = unit
  datatype shared = ORIG of Thm.thm | COPY of (string * string) * Thm.thm
  fun listItems (_ : typeBase) : tyinfo list = []
  fun constructors_of (_ : tyinfo) : Term.term list = []
  (* computeLib.add_datatype_info pattern-matches these; with listItems = []
     and fetch = NONE it is unreachable, so NONE/raise are honest. *)
  fun size_of0 (_ : tyinfo) : (Term.term * shared) option = NONE
  fun encode_of0 (_ : tyinfo) : (Term.term * shared) option = NONE
  fun case_const_of (_ : tyinfo) : Term.term =
      raise Fail "case_const_of: no datatypes registered"
end;
structure TypeBase = struct
  open TypeBase
  fun theTypeBase () : TypeBasePure.typeBase = ()
  fun register_update_fn (_ : TypeBasePure.tyinfo -> TypeBasePure.tyinfo) = ()
end;

(* DB shadow: numSimps' arithmetic_rewrites does 40+ DB.fetch "arithmetic"
   calls at load; the baked DB stub has no ancestor data. The sweeps now
   bake a dbTable into each synthesized theory structure — serve from it
   (metis-build precedent, generalized). *)
structure DB = struct
  open DB
  fun fetch thy s =
      let val tbl = case thy of
                        "arithmetic" => arithmeticTheory.dbTable
                      | "numeral" => numeralTheory.dbTable
                      | _ => []
      in case List.find (fn (n, _) => n = s) tbl of
             SOME (_, th) => th
           | NONE => DB.fetch thy s
      end
end;

val loaded = ref ([] : string list);
fun isLoaded m = List.exists (fn x => x = m) (!loaded);
fun tryLoad m =
    if isLoaded m then ()
    else
      let val sigf = m ^ ".sig"
          val smlf = m ^ ".sml"
          val name = List.last (String.fields (fn c => c = #"/") m)
      in
        if not (fileExists smlf) then
          (* missing files must not raise: "Cannot open" propagating through
             use trips the exn-unwinding VM halt (killed v7 at Streams). *)
          pr ("NS_MISSING " ^ name ^ " (" ^ smlf ^ ")\n")
        else
        (if fileExists sigf then (PolyML.use sigf handle _ => ()) else ();
         useFiltered name smlf;
         loaded := m :: !loaded;
         pr ("NS_OK   " ^ name ^ "\n"))
        handle e => pr ("NS_FAIL " ^ name ^ " :: " ^
                        (case e of Fail msg => msg | _ => exnMessage e) ^ "\n")
      end;

fun rounds ms n =
    let val before_n = length (!loaded)
        val () = pr ("NS_ROUND " ^ Int.toString n ^ "\n")
        val () = List.app tryLoad ms
        val now = length (List.filter (fn m => isLoaded m) ms)
    in
      if length (!loaded) > before_n andalso now < length ms
      then rounds ms (n + 1) else ()
    end;
val () = rounds mods1 1;

(* reduceTheory, inline (reduceScript.sml is 3 theorems; the Script->Theory
   recipe is overkill). div/mod_thm proofs are upstream's verbatim. Written
   to a temp file + use'd-with-catch so a missing computeLib/DIV_UNIQUE
   can't statically kill the piped driver. *)
val () =
  (writeFile ("/tmp/ns_reduce_thy.sml",
     "infix THEN THENL THEN1 ORELSE;\n\
     \structure reduceTheory = struct\n\
     \  local open boolLib in\n\
     \  val num_case_compute_lazy =\n\
     \      computeLib.lazyfy_thm arithmeticTheory.num_case_compute\n\
     \  val div_thm = Tactical.prove (\n\
     \      Parse.Term [QUOTE\n\
     \        \"!x y q r. x DIV y = if (x = q * y + r) /\\\\ (r < y) then q else x DIV y\"],\n\
     \      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN\n\
     \      MATCH_MP_TAC arithmeticTheory.DIV_UNIQUE THEN\n\
     \      EXISTS_TAC (Parse.Term [QUOTE \"r:num\"]) THEN ASM_REWRITE_TAC [])\n\
     \  val mod_thm = Tactical.prove (\n\
     \      Parse.Term [QUOTE\n\
     \        \"!x y q r. x MOD y = if (x = q * y + r) /\\\\ r < y then r else x MOD y\"],\n\
     \      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN\n\
     \      MATCH_MP_TAC arithmeticTheory.MOD_UNIQUE THEN\n\
     \      EXISTS_TAC (Parse.Term [QUOTE \"q:num\"]) THEN ASM_REWRITE_TAC [])\n\
     \  end\n\
     \end;\n");
   PolyML.use "/tmp/ns_reduce_thy.sml";
   pr "REDUCE_THY_OK\n")
  handle e => pr ("REDUCE_THY_FAIL :: " ^ exnMessage e ^ "\n");

val () = rounds mods2 1;
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
val () = need "computeLib-CBV_CONV"
              ((ignore (PolyML.makestring computeLib.CBV_CONV); true) handle _ => false)
         handle _ => need "computeLib-CBV_CONV" false;
val () = pr (if !smoke then "NUMSIMPS_SMOKE_PASS\n" else "NUMSIMPS_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_numsimps\n";
       PolyML.export ("/tmp/hol4_numsimps", PolyML.rootFunction);
       pr "NUMSIMPS_CHECKPOINT_DONE\n")
    else pr "NUMSIMPS_EXPORT_SKIPPED\n";
