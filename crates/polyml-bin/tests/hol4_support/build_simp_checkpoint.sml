(* build_simp_checkpoint.sml — assemble HOL4's simplifier (simpLib / SIMP_CONV /
   SIMP_TAC) on top of the warm combin checkpoint and export /tmp/hol4_simp.
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_combin (basis+kernel+Theory+parser+bool+tactic+REWRITE_TAC+
   markerTheory+combinTheory).

   simpLib needs bool+combin+marker theories (all present) + a stack of src leaves
   + the 5-module simp core, and it references markerLib/TypeBasePure/TypeBase.
   We load the leaves + core, supply REAL markerSyntax (via the expanded DB stub),
   and TYPED STUBS for markerLib (15 names — the real one needs the absent
   proofManagerLib) and TypeBasePure/TypeBase (simpLib only type-checks
   ty_name_of/simpls_of/fetch, never exercised at load).

   ONE footgun fixed: the synthesized boolLib opens Theory, whose `pp_thm` is a
   (thm -> pretty) REF that shadows the FUNCTION pp_thm simpLib.sml needs
   (`val pp_thm = lift pp_thm`). So load Hol_pp first and re-export
   `val pp_thm = Hol_pp.pp_thm` (a function) inside the synthesized boolLib.

   The full default bool_ss is NOT used (UNWIND_ss -> Unwind -> refuteLib/Canon/
   tautLib -> HolSatLib SAT subsystem, absent; Canon also has backtick quotes).
   A hand-rolled simpset (simpLib.empty_ss ++ rewrites [...]) drives SIMP_CONV/
   SIMP_TAC for the milestone.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_combin \
       crates/polyml-bin/tests/hol4_support/build_simp_checkpoint.sml
   Produces /tmp/hol4_simp.  Emits: LEAVES_DONE, CORE_DONE, SIMPLIB_LOAD USED_OK,
   SIMP_CONV_RESULT …, SIMP_TAC_RESULT …, SIMP_SMOKE_PASS|FAIL,
   EXPORTING /tmp/hol4_simp, SIMP_CHECKPOINT_DONE. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val explode = String.explode; val implode = String.implode;
structure Definition = Theory.Definition;
infix THEN THENL THEN1 ORELSE;

val nok = ref 0; val nf = ref 0;
fun U f =
  let val p = HOL ^ "/" ^ f in
    (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); nok := !nok + 1; true)
    handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); nf := !nf + 1; false)
  end;
fun Uabs p =
    (PolyML.use p; pr ("USED_OK   " ^ p ^ "\n"); nok := !nok + 1; true)
    handle e => (pr ("USE_FAIL  " ^ p ^ " :: " ^ exnMessage e ^ "\n"); nf := !nf + 1; false);

(* STEP 0: expanded DB stub + widened boolLib. *)
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

(* Hol_pp before boolLib so boolLib can re-export Hol_pp.pp_thm as a FUNCTION
   (open Theory otherwise shadows pp_thm with a thm->pretty ref). *)
val _ = U "src/parse/Hol_pp.sig";
val _ = U "src/parse/Hol_pp.sml";

structure boolLib = struct
  open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite Abbrev
       BoundedRewrites Thm Theory DB
  val pp_thm = Hol_pp.pp_thm
end;

fun patchPrimrec () =
  let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/src/1/Prim_rec.sml"))
      fun rs (s, f, r) =
          let val (pre,suf) = Substring.position f (Substring.full s)
          in if Substring.isEmpty suf then s
             else Substring.string pre ^ r ^ Substring.string (Substring.triml (size f) suf) end
      val p1 = rs(raw, "val bool_grammars = Option.valOf $ grammarDB {thyname=\"bool\"}", "val bool_grammars = ()")
      val p2 = rs(p1, "val (Type,Term) = parse_from_grammars bool_grammars", "val (Type,Term) = (Parse.Type, Parse.Term)")
      val os = TextIO.openOut "/tmp/Prim_rec_patched.sml"
  in TextIO.output(os, p2); TextIO.closeOut os end;

pr "BUILDSIMP_START\n";

(* STEP 1: leaves. *)
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
pr ("LEAVES_DONE " ^ Int.toString (!nok) ^ "/" ^ Int.toString (!nok + !nf) ^ "\n");

(* STEP 2: markerSyntax (real). *)
val _ = U "src/marker/markerSyntax.sig";
val _ = U "src/marker/markerSyntax.sml";

(* STEP 3: TypeBasePure / TypeBase — typed stubs (simpLib only type-checks them). *)
structure TypeBasePure = struct
  type tyinfo = unit
  fun ty_name_of (_:tyinfo) : string * string = ("","")
  fun simpls_of (_:tyinfo) : simpfrag.simpfrag = simpfrag.empty_simpfrag
end;
structure TypeBase = struct
  type tyinfo = TypeBasePure.tyinfo
  fun fetch (_:Type.hol_type) : tyinfo option = NONE
end;

(* STEP 4: the 5 simp-core modules. *)
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

(* STEP 5: markerLib stub. The REWRITING-marker functions (Cong/unCong/AC/unAC/
   TIDY_ABBREV_CONV) are REAL — they are tiny kernel ops over markerTheory (copied
   verbatim from src/marker/markerLib.sml), and simpLib/boolSimps actually CALL
   them at load (boolSimps' BOOL_ss/CONG_ss build with Cong + TIDY_ABBREV_CONV).
   The suspended-goal / Excl / FRAG / Req machinery (which needs the heavy
   BasicProvers/AncestryData/proofManagerLib closure) is NOT on the simp/bool_ss
   path, so those stay raise-stubs. This makes simpLib compile against a real Cong,
   which is what unblocks the full bool_ss (and hence METIS' normalForms). *)
structure markerLib = struct
  local open Thm Drule Conv Rewrite in
  type 'a set = 'a HOLset.set
  fun Cong th = EQ_MP (SYM (SPEC (concl th) markerTheory.Cong_def)) th
  fun unCong th = PURE_REWRITE_RULE [markerTheory.Cong_def] th
  fun AC th1 th2 =
      EQ_MP (SYM (SPECL [concl th1, concl th2] markerTheory.AC_DEF)) (CONJ th1 th2)
  fun unAC th = let val th1 = PURE_REWRITE_RULE [markerTheory.AC_DEF] th
                in (CONJUNCT1 th1, CONJUNCT2 th1) end
  fun TIDY_ABBREV_CONV t =
      if markerSyntax.is_malformed_abbrev t then
        (REWR_CONV markerTheory.Abbrev_def THENC TRY_CONV (REWR_CONV boolTheory.EQ_SYM_EQ)) t
      else ALL_CONV t
  val TIDY_ABBREV_RULE = CONV_RULE TIDY_ABBREV_CONV
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
  end (* local open *)
end;

(* STEP 6: simpLib. *)
val _ = U "src/simp/src/simpLib.sig";
val simplib_ok = U "src/simp/src/simpLib.sml";
pr ("SIMPLIB_LOAD " ^ (if simplib_ok then "USED_OK" else "USE_FAIL") ^ "\n");
pr ("TOTAL " ^ Int.toString (!nok) ^ "/" ^ Int.toString (!nok + !nf) ^ "\n");

(* STEP 7: smoke — SIMP_CONV + SIMP_TAC via a hand-rolled simpset. *)
val smoke = ref false;
val () =
  if simplib_ok then
    (let
       open simpLib
       infix ++
       val ss = empty_ss ++ rewrites [combinTheory.I_THM, boolTheory.AND_CLAUSES,
                                       boolTheory.REFL_CLAUSE]
       val tm = Parse.Term [QUOTE "(I:'a->'a) x = x"]
       val cth = SIMP_CONV ss [] tm
       val pth = Tactical.prove (tm, SIMP_TAC ss [])
     in
       pr ("SIMP_CONV_RESULT " ^ thm_to_string cth ^ "\n");
       pr ("SIMP_TAC_RESULT " ^ thm_to_string pth ^ "\n");
       smoke := (not (null (Thm.hyp pth)) = false)
     end
     handle e => pr ("SIMP_PROOF_FAIL :: " ^ exnMessage e ^ "\n"))
  else ();
pr (if !smoke then "SIMP_SMOKE_PASS\n" else "SIMP_SMOKE_FAIL\n");

(* STEP 8: export if the simplifier proved a goal. *)
val () =
  if !smoke then
    (pr "EXPORTING /tmp/hol4_simp\n";
     PolyML.export("/tmp/hol4_simp", PolyML.rootFunction);
     pr "SIMP_CHECKPOINT_DONE\n")
  else pr "SIMP_CHECKPOINT_SKIPPED\n";
pr "BUILDSIMP_DONE\n";
