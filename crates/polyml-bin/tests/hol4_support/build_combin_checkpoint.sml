(* build_combin.sml — build HOL4's combinTheory on the warm marker checkpoint
   (/tmp/hol4_marker) and export /tmp/hol4_combin.

   combinScript.sml = "Theory combin[bare]" + "Libs HolKernel Parse boolLib
   computeLib".  It uses Q.* dot-tactics, the Theorem/Definition keywords, and
   tags several theorems with the [compute] attribute.

   Strategy (lightweight — avoid the heavy computeLib/TypeBase closure):
     * load the real src/q/Q.sml (all its deps present on marker) after
       providing a typed markerLib STUB (combinScript uses none of Q's
       ABBREV/rename tactics) and a widened synthesized boolLib that also
       supplies clean-path save_thm_at / store_thm_at / new_definition.
     * register a no-op `compute` ThmAttribute so Theorem name[compute] is
       accepted (save_thm_attrs rejects *unknown* attributes).
     * provide a STUB structure computeLib (combinScript only `open`s it; it
       never calls computeLib.X) and a STUB combinpp (dict-update syntax sugar
       the theorems don't use).
     * register bool ancestor axioms (KEYSTONE) before new_theory.
     * run the Script->Theory recipe, synthesize structure combinTheory,
       smoke-check, export.                                                  *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val explode = String.explode;
val implode = String.implode;
structure Definition = Theory.Definition;

fun U f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;

(* tactic infixes used by combinScript proofs *)
infix THEN THENL THEN1 ORELSE >> >- ;

pr "\nCOMBIN_BUILD_START\n";

(* ---------------------------------------------------------------------------
   1. markerLib STUB — typed per src/marker/markerLib.sig; never invoked by
   combinScript, so the bodies raise.  Q.sml references markerLib.* qualified.
   --------------------------------------------------------------------------- *)
structure markerLib =
struct
  fun ABBREV_TAC (_:term) : tactic = raise Fail "markerLib stub"
  fun PAT_ABBREV_TAC (_:term HOLset.set) (_:term) : tactic =
      raise Fail "markerLib stub"
  fun MATCH_ABBREV_TAC (_:term HOLset.set) (_:term) : tactic =
      raise Fail "markerLib stub"
  fun MATCH_ASSUM_ABBREV_TAC (_:term HOLset.set) (_:term) : tactic =
      raise Fail "markerLib stub"
  fun HO_MATCH_ABBREV_TAC (_:term HOLset.set) (_:term) : tactic =
      raise Fail "markerLib stub"
  fun UNABBREV_TAC (_:string) : tactic = raise Fail "markerLib stub"
  fun RM_ABBREV_TAC (_:string) : tactic = raise Fail "markerLib stub"
  fun ABB' (_:{redex:term,residue:term}) : tactic = raise Fail "markerLib stub"
  fun safe_inst_cmp (_:{redex:term,residue:term},_:{redex:term,residue:term})
      : order = raise Fail "markerLib stub"
  fun safe_inst_sort (s:(term,term)Lib.subst) : (term,term)Lib.subst =
      raise Fail "markerLib stub"
end;

(* ---------------------------------------------------------------------------
   2. Register a no-op `compute` attribute so Theorem nm[compute] is accepted.
   --------------------------------------------------------------------------- *)
val () =
    (if ThmAttribute.is_attribute "compute" then
        pr "COMPUTE_ATTR_ALREADY\n"
     else
        (ThmAttribute.register_attribute
           ("compute",
            {storedf = (fn _ => ()), localf = (fn _ => ())});
         pr "COMPUTE_ATTR_REGISTERED\n"))
    handle e => pr ("COMPUTE_ATTR_FAIL :: " ^ exnMessage e ^ "\n");

(* ---------------------------------------------------------------------------
   3. Widened synthesized boolLib.  Opens the structures combinScript and Q
   need, plus clean-path save_thm_at / store_thm_at / new_definition.
   --------------------------------------------------------------------------- *)
structure boolLib =
struct
  open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite
       Abbrev BoundedRewrites Parse
  (* names combinScript/Q want that the opens above don't surface *)
  val EQ_IMP_RULE     = Thm.EQ_IMP_RULE
  val CONJ            = Thm.CONJ
  val add_ML_dependency = Theory.add_ML_dependency

  (* simplified clean-path store machinery (combinTheory theorems carry no
     suspended hyps, so the full boolLib.save_thm_attrs branching is not
     needed).  We DO honour known attributes (e.g. the no-op compute) and
     silently drop unknown ones. *)
  fun do_known_attrs name th attrs =
      List.app
        (fn (k,vs) =>
            ThmAttribute.store_at_attribute
              {thm = th, name = name, attrname = k, args = vs})
        attrs
  fun handle_reserved call R =
      (* accept only "local"/"unlisted"/"allow_rebind"/"schematic"/
         "nocompute"/"unlisted"; combinTheory uses none, so just ignore. *)
      ()
  fun save_thm_attrs loc (attrblock:ThmAttribute.attrblock, th) =
      let val {thmname=n,attrs,unknown,reserved} = attrblock
      in handle_reserved "save_thm_attrs" reserved;
         Theory.gen_save_thm{name=n,private=false,thm=th,loc=loc};
         do_known_attrs n th attrs;
         th
      end
  fun save_thm_at loc (n0,th) =
      save_thm_attrs loc (ThmAttribute.extract_attributes n0, th)
  val save_thm = save_thm_at DB.Unknown
  fun store_thm_at loc (n0,t,tac) =
      let val attrblock = ThmAttribute.extract_attributes n0
          val th = Tactical.prove(t,tac)
      in save_thm_attrs loc (attrblock,th) end
  val store_thm = store_thm_at DB.Unknown
  (* definitions: boolSyntax provides new_definition_at/new_definition,
     re-export so Q.new_definition_at finds them via boolLib. *)
  val new_definition_at = boolSyntax.new_definition_at
  val new_definition = boolSyntax.new_definition
  val new_infixl_definition = boolSyntax.new_infixl_definition
  val new_infixr_definition = boolSyntax.new_infixr_definition
end;

(* ---------------------------------------------------------------------------
   4. Load the real Q (all deps present; markerLib stub satisfies references).
   --------------------------------------------------------------------------- *)
val q_sig_ok = U "src/q/Q.sig";
val q_sml_ok = U "src/q/Q.sml";
val () = (ignore Q.new_definition_at; ignore Q.store_thm_at; ignore Q.SPEC_THEN;
          ignore Q.PAT_X_ASSUM; pr "Q_FUNCS_OK\n")
         handle e => pr ("Q_FUNCS_FAIL :: " ^ exnMessage e ^ "\n");

(* ---------------------------------------------------------------------------
   5. Stub structures the Libs-open needs: computeLib (open only) + combinpp.
   --------------------------------------------------------------------------- *)
structure computeLib = struct end;
val add_ML_dependency = Theory.add_ML_dependency;  (* combinScript bare use *)
structure combinpp =
struct
  fun enable_dictsyntax () = ()
  fun new_form (_ : { left : string, right : string,
                      upd_term_name : term * string,
                      lookup_term_name : (term * string) option }) = ()
end;

(* ---------------------------------------------------------------------------
   6. KEYSTONE: register the bool ancestor axioms before new_theory.
   --------------------------------------------------------------------------- *)
val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax;
             pr ("REG_AX " ^ nm ^ "\n"))
            handle e => pr ("REG_AX_FAIL " ^ nm ^ " :: " ^ exnMessage e ^ "\n"))
        [("BOOL_CASES_AX", boolTheory.BOOL_CASES_AX),
         ("ETA_AX",        boolTheory.ETA_AX),
         ("SELECT_AX",     boolTheory.SELECT_AX),
         ("INFINITY_AX",   boolTheory.INFINITY_AX)];

(* ---------------------------------------------------------------------------
   7. Script->Theory recipe: filter combinScript, neutralize export_theory,
   write, PolyML.use.
   --------------------------------------------------------------------------- *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/combin/combinScript.sml");
val (pre, suf) = Substring.position "export_theory" (Substring.full raw);
val neutralized =
    Substring.string pre ^ "current_theory"
    ^ Substring.string (Substring.triml (size "export_theory") suf);
val () = let val os = TextIO.openOut "/tmp/combinScript_filtered.sml"
         in TextIO.output(os, neutralized); TextIO.closeOut os end;
val () = (PolyML.use "/tmp/combinScript_filtered.sml"; pr "COMBIN_USED_OK\n")
         handle e => pr ("COMBIN_USE_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("COMBIN_THEORY current=" ^ Theory.current_theory() ^ "\n");

(* ---------------------------------------------------------------------------
   8. Synthesize structure combinTheory from the live segment.
   --------------------------------------------------------------------------- *)
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
val () = pr ("COMBINTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () = let val os = TextIO.openOut "/tmp/combinTheory_gen.sml"
         in TextIO.output(os, "structure combinTheory = struct\n");
            app (fn (n,_) => TextIO.output(os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
                (!btbl);
            TextIO.output(os, "end;\n"); TextIO.closeOut os
         end;
val () = (PolyML.use "/tmp/combinTheory_gen.sml"; pr "COMBINTHEORY_STRUCT_LOADED\n")
         handle e => pr ("COMBINTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* ---------------------------------------------------------------------------
   9. Smoke checks then export.
   --------------------------------------------------------------------------- *)
val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "combin-current" (Theory.current_theory() = "combin");
val () = need "I-const"
              ((ignore (Term.prim_mk_const{Name="I",Thy="combin"}); true)
               handle _ => false);
val () = need "I_THM" ((ignore combinTheory.I_THM; true) handle _ => false);
val () = need "K_THM" ((ignore combinTheory.K_THM; true) handle _ => false);
val () = need "o_THM" ((ignore combinTheory.o_THM; true) handle _ => false);
val () = pr (if !smoke then "COMBIN_SMOKE_PASS\n" else "COMBIN_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_combin\n";
       PolyML.export("/tmp/hol4_combin", PolyML.rootFunction);
       pr "COMBIN_CHECKPOINT_DONE\n")
    else pr "COMBIN_CHECKPOINT_SKIPPED\n";
