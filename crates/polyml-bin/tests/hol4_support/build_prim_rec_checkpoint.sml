(* build_prim_rec_checkpoint.sml — WORK IN PROGRESS (blocked).
   Goal: build the part of HOL4's prim_recTheory we need for primitive recursion
   (num_Axiom) on the warm /tmp/hol4_num checkpoint, then DEFINE addition and
   prove the FULL trophy  |- !n. n + 0 = n.

   STATUS (2026-06-04): BLOCKED before num_Axiom.  The SIMP_REC machinery
   (prim_recScript.sml:361-442) needs both (a) a full bool_ss simplifier and
   (b) `UNIQUE_SKOLEM_THM`.  The hand-built bool_ss (below) loads, but the LCF
   proof of UNIQUE_SKOLEM_THM (replicated from src/1/boolLib.sml:89) FAILS at
   `DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)` on our checkpoint: after
   `REWRITE_TAC[EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM] THEN EQ_TAC`
   the goal is not in the `A /\ B ==> C` shape the proof expects (rewriting
   yields a slightly different normal form than upstream).  Without
   UNIQUE_SKOLEM_THM the SIMP_REC specification (line 410) cannot be proved, so
   num_Axiom (line 549) is unreachable — hence no `new_recursive_definition`,
   no ADD, no `n + 0 = n`.  The cleaner trophy that DOES land is in
   prove_induction.sml (genuine induction over num, no addition needed).
   Kept here as a documented partial: the simp-core load + bool_ss build + the
   prim_recScript truncation recipe all work; the wall is UNIQUE_SKOLEM_THM.

   prim_recScript.sml needs:
     * src/1/Prim_rec (generic induction/rec support) — patched grammarDB{bool};
     * the simplifier core (src/simp/src/{Trace,Opening,Travrules,Cond_rewr,
       Traverse,simpLib}) + leaves, exactly as build_simp_checkpoint.sml;
     * `bool_ss` — boolSimps' real bool_ss pulls in UNWIND_ss -> the absent SAT
       subsystem, so we HAND-BUILD a bool_ss substitute: empty_ss + BETA + the
       boolTheory boolean-clause rewrites.  prim_recScript's 4 bool_ss calls pass
       their domain rewrites explicitly, so this suffices;
     * `UNIQUE_SKOLEM_THM` (line 414) — not in boolTheory; we PROVE it from
       boolTheory.SKOLEM_THM etc., replicating src/1/boolLib.sml:89.
   We TRUNCATE the script just after `num_Axiom` (line 558), dropping
   define_case_constant / Overload / TypeBase.export / the WF tail (those need
   relationTheory + TypeBase, absent).  num_Axiom is all we need to define
   recursive functions via Prim_rec.new_recursive_definition.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_num \
       crates/polyml-bin/tests/hol4_support/build_prim_rec_checkpoint.sml       *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val explode = String.explode; val implode = String.implode;
structure Definition = Theory.Definition;
infix THEN THENL THEN1 ORELSE >> >-;

val nok = ref 0; val nf = ref 0;
fun U f =
  let val p = HOL ^ "/" ^ f in
    (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); nok := !nok + 1; true)
    handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n");
                 nf := !nf + 1; false)
  end;
fun Uabs p =
  (PolyML.use p; pr ("USED_OK   " ^ p ^ "\n"); nok := !nok + 1; true)
  handle e => (pr ("USE_FAIL  " ^ p ^ " :: " ^ exnMessage e ^ "\n");
               nf := !nf + 1; false);

pr "\nPRIMREC_BUILD_START\n";
val () = pr ("BASE current_theory=" ^ Theory.current_theory() ^ "\n");

(* ---------- STEP 0: DB stub + Hol_pp + widened boolLib (build_simp recipe) -- *)
structure DB = struct
  datatype theory = datatype DB_dtype.theory
  datatype selector = datatype DB_dtype.selector
  datatype location = datatype DB_dtype.location
  datatype class = datatype DB_dtype.class
  type thm = Thm.thm  type term = Term.term  type hol_type = Type.hol_type
  type data = DB_dtype.data  type public_data = DB_dtype.public_data
  type data_value = DB_dtype.data_value  type 'a named = 'a DB_dtype.named
  type thminfo = DB_dtype.thminfo  type thm_src_location = DB_dtype.thm_src_location
  exception DB_STUB of string
  fun thy (_:string) : data list = raise DB_STUB "thy"
  fun fetch (_:string) (_:string) : thm = raise DB_STUB "fetch"
  fun fetch_knm (_:KernelSig.kernelname) : thm = raise DB_STUB "fetch_knm"
  fun lookup (_:KernelSig.kernelname) : data_value option = raise DB_STUB "lookup"
  fun thms (_:string) : (string*thm) list = raise DB_STUB "thms"
  fun theorem (_:string) : thm = raise DB_STUB "theorem"
  fun definition (_:string) : thm = raise DB_STUB "definition"
  fun axiom (_:string) : thm = raise DB_STUB "axiom"
  fun axioms (_:string) : (string*thm) list = raise DB_STUB "axioms"
  fun theorems (_:string) : (string*thm) list = raise DB_STUB "theorems"
  fun definitions (_:string) : (string*thm) list = raise DB_STUB "definitions"
  fun find_all (_:string) : data list = raise DB_STUB "find_all"
  fun find (_:string) : public_data list = raise DB_STUB "find"
  fun find_in (_:string) (l:'a named list) : 'a named list = raise DB_STUB "find_in"
  fun matchp (_:thm->bool) (_:string list) : public_data list = raise DB_STUB "matchp"
  fun matcher (_:term->term->'a) (_:string list) (_:term) = raise DB_STUB "matcher"
  fun match (_:string list) (_:term) : public_data list = raise DB_STUB "match"
  fun matches (_:term) (_:thm) : bool = raise DB_STUB "matches"
  fun apropos (_:term) : public_data list = raise DB_STUB "apropos"
  fun apropos_in (_:term) (_:public_data list) : public_data list = raise DB_STUB "apropos_in"
  fun selectDB (_:selector list) : public_data list = raise DB_STUB "selectDB"
  fun listDB () : data list = raise DB_STUB "listDB"
  fun revlookup (_:thm) : location list = raise DB_STUB "revlookup"
  fun polarity_search (_:bool) (_:term) : public_data list = raise DB_STUB "polarity_search"
  fun store_local (_:thminfo) (_:string) (_:thm) : unit = raise DB_STUB "store_local"
  fun local_thm (_:string) : thm option = raise DB_STUB "local_thm"
  fun dest_theory (_:string) : theory = raise DB_STUB "dest_theory"
  fun bindl (_:string) (_:(string*thm*thminfo) list) : unit = raise DB_STUB "bindl"
  fun find_consts_thy (_:string list) (_:hol_type) : term list = raise DB_STUB "find_consts_thy"
  fun find_consts (_:hol_type) : term list = raise DB_STUB "find_consts"
end;

val _ = U "src/parse/Hol_pp.sig";
val _ = U "src/parse/Hol_pp.sml";

structure boolLib = struct
  open boolTheory boolSyntax Thm Definition Drule Conv Tactical Tactic
       Thm_cont Rewrite Abbrev BoundedRewrites Theory DB
  val pp_thm = Hol_pp.pp_thm
end;

(* ---------- STEP 1: simp leaves (build_simp recipe) ----------------------- *)
fun patchPrimrec () =
  let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/src/1/Prim_rec.sml"))
      fun rs (s, f, r) =
          let val (pre,suf) = Substring.position f (Substring.full s)
          in if Substring.isEmpty suf then s
             else Substring.string pre ^ r
                  ^ Substring.string (Substring.triml (size f) suf) end
      val p1 = rs(raw,
            "val bool_grammars = Option.valOf $ grammarDB {thyname=\"bool\"}",
            "val bool_grammars = ()")
      val p2 = rs(p1,
            "val (Type,Term) = parse_from_grammars bool_grammars",
            "val (Type,Term) = (Parse.Type, Parse.Term)")
      val os = TextIO.openOut "/tmp/Prim_rec_patched.sml"
  in TextIO.output(os, p2); TextIO.closeOut os end;

val _ = U "src/1/term_tactic.sig";
val _ = U "src/1/term_tactic.sml";
val _ = U "src/portableML/Table.sml";
val _ = U "src/1/Ho_Net.sig";
val _ = U "src/1/Ho_Net.sml";
val _ = U "src/1/ParseExtras.sig";
val _ = U "src/1/ParseExtras.sml";
val _ = U "src/1/Ho_Rewrite.sig";
val _ = U "src/1/Ho_Rewrite.sml";
val () = patchPrimrec();
val _ = U "src/1/Prim_rec.sig";
val _ = Uabs "/tmp/Prim_rec_patched.sml";
val _ = U "src/lite/liteLib.sig";
val _ = U "src/lite/liteLib.sml";
val _ = U "src/refute/AC.sig";
val _ = U "src/refute/AC.sml";
val _ = U "src/1/simpfrag.sig";
val _ = U "src/1/simpfrag.sml";
val _ = U "src/marker/markerSyntax.sig";
val _ = U "src/marker/markerSyntax.sml";
pr ("LEAVES_DONE " ^ Int.toString (!nok) ^ "/" ^ Int.toString (!nok + !nf) ^ "\n");

(* TypeBasePure / TypeBase typed stubs (simpLib only type-checks them). *)
structure TypeBasePure = struct
  type tyinfo = unit
  fun ty_name_of (_:tyinfo) : string * string = ("","")
  fun simpls_of (_:tyinfo) : simpfrag.simpfrag = simpfrag.empty_simpfrag
end;
structure TypeBase = struct
  type tyinfo = TypeBasePure.tyinfo
  fun fetch (_:Type.hol_type) : tyinfo option = NONE
end;

val _ = U "src/simp/src/Trace.sig";
val _ = U "src/simp/src/Trace.sml";
val _ = U "src/simp/src/Opening.sig";
val _ = U "src/simp/src/Opening.sml";
val _ = U "src/simp/src/Travrules.sig";
val _ = U "src/simp/src/Travrules.sml";
val _ = U "src/simp/src/Cond_rewr.sig";
val _ = U "src/simp/src/Cond_rewr.sml";
val _ = U "src/simp/src/Traverse.sig";
val _ = U "src/simp/src/Traverse.sml";
pr ("CORE_DONE " ^ Int.toString (!nok) ^ "/" ^ Int.toString (!nok + !nf) ^ "\n");

(* markerLib typed stub (15 names simpLib uses). *)
structure markerLib = struct
  type 'a set = 'a HOLset.set
  fun Cong (_:thm) : thm = raise Fail "markerLib stub Cong"
  fun unCong (_:thm) : thm = raise Fail "markerLib stub unCong"
  fun AC (_:thm) (_:thm) : thm = raise Fail "markerLib stub AC"
  fun unAC (_:thm) : thm * thm = raise Fail "markerLib stub unAC"
  fun Excl (_:string) : thm = raise Fail "markerLib stub Excl"
  fun destExcl (_:thm) : string option = NONE
  fun ExclSF (_:string) : thm = raise Fail "markerLib stub ExclSF"
  fun destExclSF (_:thm) : string option = NONE
  fun FRAG (_:string) : thm = raise Fail "markerLib stub FRAG"
  fun destFRAG (_:thm) : string option = NONE
  fun mk_Req0 (_:thm) : thm = raise Fail "markerLib stub mk_Req0"
  fun mk_ReqD (_:thm) : thm = raise Fail "markerLib stub mk_ReqD"
  fun mk_require_tac (f:thm list -> tactic) : thm list -> tactic = f
  fun ABBRS_THEN (f:thm list -> tactic) (l:thm list) : tactic = f l
  fun LLABEL_RES_THEN (f:thm list -> tactic) (l:thm list) : tactic = f l
  val NoAsms : thm = TRUTH
  fun process_taclist_then ({arg}:{arg:thm list}) (f:thm list -> tactic) : tactic = f arg
end;

val _ = U "src/simp/src/simpLib.sig";
val simplib_ok = U "src/simp/src/simpLib.sml";
pr ("SIMPLIB_LOAD " ^ (if simplib_ok then "USED_OK" else "USE_FAIL") ^ "\n");

(* ---------- STEP 2: hand-built bool_ss + UNIQUE_SKOLEM_THM ---------------- *)
(* BETA conv fragment + boolTheory boolean-clause rewrites. *)
val bool_ss =
  let
    open simpLib
    val beta_frag =
        std_conv_ss {name = "BETA_CONV",
                     pats = [Parse.Term [QUOTE "(\\x:'a. (y:'b)) z"]],
                     conv = Thm.BETA_CONV}
    val rw_frag =
        rewrites [boolTheory.REFL_CLAUSE, boolTheory.EQ_CLAUSES,
                  boolTheory.NOT_CLAUSES, boolTheory.AND_CLAUSES,
                  boolTheory.OR_CLAUSES, boolTheory.IMP_CLAUSES,
                  boolTheory.COND_CLAUSES, boolTheory.FORALL_SIMP,
                  boolTheory.EXISTS_SIMP, boolTheory.COND_ID,
                  boolTheory.EXISTS_REFL, boolTheory.EXISTS_UNIQUE_REFL,
                  boolTheory.bool_case_thm]
  in mk_simpset [rw_frag, beta_frag] end;
val () = pr "BOOL_SS_BUILT\n";

(* UNIQUE_SKOLEM_THM — replicate src/1/boolLib.sml:89 from boolTheory. *)
val UNIQUE_SKOLEM_THM =
  let
    open boolTheory Drule Tactic Tactical Thm_cont Conv Rewrite boolSyntax
    val q = fn s => Parse.Term [QUOTE s]
  in
    Tactical.prove
      (q "!P. (!x:'a. ?!y:'b. P x y) = ?!f. !x. P x (f x)",
       GEN_TAC
        THEN REWRITE_TAC[EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM]
        THEN EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)
        THEN ASM_REWRITE_TAC[] THENL
         [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
          X_GEN_TAC (q "x:'a") THEN FIRST_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (q "x:'a") THEN ASM_REWRITE_TAC[],
          MAP_EVERY X_GEN_TAC [q "x:'a", q "y1:'b", q "y2:'b"]
          THEN STRIP_TAC THEN
          FIRST_ASSUM(X_CHOOSE_TAC (q "f:'a->'b")) THEN
          SUBGOAL_THEN (q "(\\z. if z=x then y1 else (f:'a->'b) z) = \
                          \(\\z. if z=x then y2 else (f:'a->'b) z)") MP_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN
            REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
            ASM_REWRITE_TAC[],
            DISCH_THEN(MP_TAC o C AP_THM (q "x:'a")) THEN
            REWRITE_TAC[BETA_THM]]])
  end;
val () = (pr ("UNIQUE_SKOLEM_THM = " ^ Parse.thm_to_string UNIQUE_SKOLEM_THM ^ "\n"))
         handle e => pr ("USKOLEM_FAIL :: " ^ exnMessage e ^ "\n");

(* ---------- STEP 3: register bool ancestor axioms (KEYSTONE) -------------- *)
val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax; pr ("REG_AX " ^ nm ^ "\n"))
            handle e => pr ("REG_AX_NOTE " ^ nm ^ " :: " ^ exnMessage e ^ "\n"))
        [("BOOL_CASES_AX", boolTheory.BOOL_CASES_AX),
         ("ETA_AX",        boolTheory.ETA_AX),
         ("SELECT_AX",     boolTheory.SELECT_AX),
         ("INFINITY_AX",   boolTheory.INFINITY_AX)];
(* also register num's axioms while current=num. *)
val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax; pr ("REG_NUM_AX " ^ nm ^ "\n"))
            handle e => pr ("REG_NUM_AX_NOTE " ^ nm ^ " :: " ^ exnMessage e ^ "\n"))
        (Theory.current_axioms());

(* ---------- STEP 4: truncate prim_recScript at num_Axiom, neutralize, use - *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/num/theories/prim_recScript.sml");
(* truncate at the line after num_Axiom's QED (before define_case_constant). *)
val cutmarker = "val [num_case_def] = Prim_rec.define_case_constant";
val (pre2, _) = Substring.position cutmarker (Substring.full raw);
val truncated = Substring.string pre2;
(* neutralize export_theory just in case it survives (it won't, truncated). *)
val () = let val os = TextIO.openOut "/tmp/prim_recScript_filtered.sml"
         in TextIO.output(os, truncated); TextIO.closeOut os end;
val () = (PolyML.use "/tmp/prim_recScript_filtered.sml"; pr "PRIMREC_USED_OK\n")
         handle e => pr ("PRIMREC_USE_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("PRIMREC_THEORY current=" ^ Theory.current_theory() ^ "\n");

(* ---------- STEP 5: synthesize structure prim_recTheory ------------------- *)
val all_named =
    Theory.current_axioms() @ Theory.current_definitions() @
    Theory.current_theorems();
fun validName s =
    size s > 0 andalso Char.isAlpha (String.sub(s,0)) andalso
    CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s;
val seen = ref ([] : string list);
val btbl = ref ([] : (string * Thm.thm) list);
val () = app (fn (n,th) =>
                 if validName n andalso not (List.exists (fn m => m = n) (!seen))
                 then (seen := n :: !seen; btbl := (n,th) :: !btbl) else ())
             all_named;
fun bt n = #2 (valOf (List.find (fn (m,_) => m = n) (!btbl)));
val () = pr ("PRIMRECTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");

(* num_Axiom is a Theorem (segment-stored); fetch it directly for the trophy. *)
val num_Axiom_opt =
    (SOME (bt "num_Axiom")) handle _ => NONE;
val () = case num_Axiom_opt of
             SOME th => pr ("NUM_AXIOM = " ^ Parse.thm_to_string th ^ "\n")
           | NONE => pr "NUM_AXIOM_MISSING\n";

(* ---------- STEP 6: define ADD, prove |- !n. n + 0 = n ------------------- *)
val INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC;

val trophy_ok = ref false;
val () =
  case num_Axiom_opt of
    NONE => pr "TROPHY_SKIPPED_NO_AXIOM\n"
  | SOME num_Axiom =>
    (let
       val ADD = Prim_rec.new_recursive_definition
                   {name = "ADD", rec_axiom = num_Axiom,
                    def = Parse.Term [QUOTE
                      "(add 0 n = n) /\\ (add (SUC m) n = SUC (add m n))"]}
       val () = pr ("ADD = " ^ Parse.thm_to_string ADD ^ "\n")
       (* prove  !n. add n 0 = n  by induction (n+0 form; genuinely needs it) *)
       val thm = Tactical.prove
                   (Parse.Term [QUOTE "!n. add n 0 = n"],
                    INDUCT_TAC THEN Rewrite.ASM_REWRITE_TAC [ADD])
     in
       pr ("TROPHY_THM = " ^ Parse.thm_to_string thm ^ "\n");
       pr ("TROPHY_HYPS = " ^ Int.toString (length (Thm.hyp thm)) ^ "\n");
       if null (Thm.hyp thm) then (trophy_ok := true; pr "FULL_TROPHY_PASS\n")
       else pr "FULL_TROPHY_FAIL_HYPS\n"
     end
     handle e => pr ("TROPHY_FAIL :: " ^ exnMessage e ^ "\n"));

(* ---------- STEP 7: export prim_rec checkpoint if num_Axiom present ------- *)
val () =
    case num_Axiom_opt of
      SOME _ =>
        (pr "EXPORTING /tmp/hol4_prim_rec\n";
         PolyML.export("/tmp/hol4_prim_rec", PolyML.rootFunction);
         pr "PRIMREC_CHECKPOINT_DONE\n")
    | NONE => pr "PRIMREC_CHECKPOINT_SKIPPED\n";
val () = pr "PRIMREC_BUILD_DONE\n";
