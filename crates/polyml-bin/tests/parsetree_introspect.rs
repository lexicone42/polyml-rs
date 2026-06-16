//! The PolyML compiler parse-tree introspection path on the polyml-rs interpreter.
//!
//! `PolyML.compiler` with a `CPCompilerResultFun` returns a typed parse tree, and
//! the `PT*` accessors (`PTfirstChild`/`PTnextSibling`/`PTtype`/`PTdefId`/…) walk it.
//! HOL4's `PolyML.use` uses the default result-discarding path and never builds or
//! walks a parse tree, so this is the SECOND major compiler-coupling that Isabelle
//! needs (its `ml_compiler.ML` walks the tree for markup/types/errors) and that our
//! HOL4 work never exercised. The Isabelle gap-recon flagged it as the biggest
//! untested risk after `PolyML.NameSpace`; this pins it GREEN.
//!
//! The runtime does not implement the compiler — it runs PolyML's own SML compiler
//! bytecode (`mlsource/MLCompiler/`), which builds the tree via unsafe casts in
//! `ExportTree.sml`. That this round-trips proves our interpreter executes that
//! low-level tree-encoding machinery faithfully.
//!
//! `#[ignore]` (needs /tmp/basis_loaded; self-contained — no Isabelle source):
//! ```sh
//! tools/build-hol4-checkpoints.sh basis
//! cargo test --release -p polyml-bin --test parsetree_introspect -- --ignored --nocapture
//! ```

mod common;
use common::*;

#[test]
#[ignore = "needs /tmp/basis_loaded (tools/build-hol4-checkpoints.sh basis)"]
fn compiler_parsetree_walk_and_types() {
    let Some(basis) = basis_checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded missing — run tools/build-hol4-checkpoints.sh basis");
        return;
    };
    // Drive PolyML.compiler on a small decl with a CPCompilerResultFun, then walk
    // the returned parse tree collecting every PTtype rendered via the same accessor
    // Isabelle's ml_compiler.ML uses (NameSpace.Values.printType). Also check the
    // error path returns code=NONE but tree=SOME (Isabelle relies on this for markup).
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun renderType types =
  let val pretty = PolyML.NameSpace.Values.printType (types, 100, SOME PolyML.globalNameSpace)
      val buf = ref ([] : string list)
  in PolyML.prettyPrint ((fn s => buf := s :: !buf), 80) pretty;
     String.concat (rev (!buf))
  end;
val types_seen = ref ([] : string list);
fun walk depth (loc, props) =
  if depth > 12 then () else
  List.app (fn p =>
    case p of
        PolyML.PTfirstChild f => walk (depth+1) (f ())
      | PolyML.PTnextSibling f => walk depth (f ())
      | PolyML.PTtype types => types_seen := renderType types :: !types_seen
      | _ => ()) props;
fun compileAndWalk source =
  let val chars = ref (String.explode source)
      val off = ref 0
      fun getChar () = case !chars of [] => NONE | c::r => (chars := r; off := !off+1; SOME c)
      val tree = ref (NONE : PolyML.parseTree option)
      val code = ref false
      fun resFun (treeOpt, codeOpt) =
        (tree := treeOpt; code := (case codeOpt of SOME _ => true | NONE => false); fn () => ())
      val () = (PolyML.compiler (getChar,
                 [ PolyML.Compiler.CPNameSpace PolyML.globalNameSpace,
                   PolyML.Compiler.CPFileName "probe.sml",
                   PolyML.Compiler.CPLineNo (fn () => 1),
                   PolyML.Compiler.CPLineOffset (fn () => !off),
                   PolyML.Compiler.CPCompilerResultFun resFun,
                   PolyML.Compiler.CPBindingSeq (fn () => 99) ]) ())
                handle _ => ()
  in (!tree, !code) end;
(* good decl: tree + code present, and a PTtype renders to int *)
val (t1, c1) = compileAndWalk "val a = 10; val b = a + a;\n";
val () = pr ("GOOD_CODE=" ^ Bool.toString c1 ^ "\n");
val () = pr ("GOOD_TREE=" ^ Bool.toString (Option.isSome t1) ^ "\n");
val () = (case t1 of SOME tr => walk 0 tr | NONE => ());
val () = pr ("GOOD_TYPES=[" ^ String.concatWith "|" (!types_seen) ^ "]\n");
val () = pr ("GOOD_HAS_INT_TYPE=" ^ Bool.toString (List.exists (fn s => String.isSubstring "int" s) (!types_seen)) ^ "\n");
(* error decl: Isabelle relies on code=NONE but tree=SOME for error markup *)
val (t2, c2) = compileAndWalk "val bad = 1 + true;\n";
val () = pr ("ERR_CODE=" ^ Bool.toString c2 ^ "\n");
val () = pr ("ERR_TREE=" ^ Bool.toString (Option.isSome t2) ^ "\n");
pr "PARSETREE_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&basis, driver, 10_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("PARSETREE_DONE"),
        "probe did not finish.\n{}",
        tail(&out, 30)
    );
    // a successful compile yields both a runnable code fn and a parse tree
    assert!(
        out.contains("GOOD_CODE=true"),
        "compiler did not return code.\n{}",
        tail(&out, 30)
    );
    assert!(
        out.contains("GOOD_TREE=true"),
        "compiler did not return a parseTree.\n{}",
        tail(&out, 30)
    );
    // the PT* walk reaches a PTtype that renders to `int` (NameSpace.Values.printType)
    assert!(
        out.contains("GOOD_HAS_INT_TYPE=true"),
        "parse-tree walk did not find an int PTtype.\n{}",
        tail(&out, 30)
    );
    // error path: no code, but a tree (what Isabelle uses to report errors with markup)
    assert!(
        out.contains("ERR_CODE=false"),
        "type-error decl should not yield code.\n{}",
        tail(&out, 30)
    );
    assert!(
        out.contains("ERR_TREE=true"),
        "type-error decl should still yield a parseTree.\n{}",
        tail(&out, 30)
    );
}
