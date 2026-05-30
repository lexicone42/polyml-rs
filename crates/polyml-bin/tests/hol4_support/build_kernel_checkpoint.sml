(* build_kernel_checkpoint.sml — load the HOL4 LCF kernel (Type / Term /
   Subst / Net … up through src/thm/std-thm) on top of a basis-loaded
   checkpoint, then PolyML.export a warm "basis + kernel" image so the
   Theory-subsystem experiments start in seconds instead of minutes.
   Run from cwd = vendor/polyml (or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/basis_loaded \
       crates/polyml-bin/tests/hol4_support/build_kernel_checkpoint.sml
   Produces /tmp/hol4_kernel. Mirrors hol4_kernel_prelude() in
   crates/polyml-bin/tests/hol4_recon.rs — keep the two in sync. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
(* ../hol4 relative to cwd = vendor/polyml. Our runtime's OS.Process.getEnv
   currently returns SOME "" for set vars, so only honor a NON-empty value. *)
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
fun U dir f = PolyML.use (HOL ^ "/" ^ dir ^ "/" ^ f);
fun PMu f = U "src/portableML" f;
fun PKu f = U "src/prekernel" f;
fun K0u f = U "src/0" f;
fun TPu f = U "tools-poly/poly" f;
fun H   f = U "tools/Holmake/hfs" f;
fun HP  f = U "tools/Holmake/poly" f;
fun Tu  f = U "src/thm" f;

structure Systeml = struct
  val HOLDIR = HOL; val release = "polyml-rs"; val version = 0;
end;
structure Path = OS.Path;

pr "\nKERNEL_PRELUDE_START\n";
PMu "quotation_dtype.sml"; PMu "poly/PrettyImpl.sml";
PMu "poly/Exn.sig"; PMu "poly/Exn.sml";
PMu "Uref.sig"; PMu "Uref.sml";
PMu "UTF8.sig"; PMu "UTF8.sml";
PMu "HOLPP.sig"; PMu "HOLPP.sml";
PMu "OldPP.sig"; PMu "OldPP.sml";
PMu "poly/Arbnumcore.sig"; PMu "poly/Arbnumcore.sml";
PMu "Arbnum.sig"; PMu "Arbnum.sml";
H "HOLFS_dtype.sml";
H "HFS_NameMunge.sig"; HP "HFS_NameMunge.sml";
H "HOLFileSys.sig"; H "HOLFileSys.sml";
PMu "poly/MD5.sig"; PMu "poly/MD5.sml";
PMu "poly/Susp.sig"; PMu "poly/Susp.sml";
PMu "poly/Thread_Attributes.sml"; PMu "poly/Thread_Data.sml";
PMu "poly/Unsynchronized.sml"; PMu "poly/ConcIsaLib.sml";
PMu "poly/Multithreading.sml"; PMu "poly/Synchronized.sml";
PMu "HOLquotation.sig"; PMu "HOLquotation.sml";
PMu "poly/MLSYSPortable.sml";
PMu "Portable.sig"; PMu "Portable.sml";
PMu "Redblackmap.sig"; PMu "Redblackmap.sml";
PMu "Redblackset.sig"; PMu "Redblackset.sml";
PMu "HOLset.sig"; PMu "HOLset.sml";
PMu "Table.sml"; PMu "Symtab.sml"; PMu "Inttab.sml";
PMu "locn.sig"; PMu "locn.sml";
PMu "poly/CoreReplVARS.sml";
PMu "poly/concurrent/Sref.sig"; PMu "poly/concurrent/Sref.sml";
PKu "Feedback_dtype.sml";
PKu "Globals.sig"; PKu "Globals.sml";
PKu "Feedback.sig"; PKu "Feedback.sml";
PKu "Lib.sig"; PKu "Lib.sml";
PKu "Count.sig"; PKu "Count.sml";
PKu "Nonce.sig"; PKu "Nonce.sml";
PKu "Dep.sig"; PKu "Dep.sml";
PKu "Tag.sig"; PKu "Tag.sml";
TPu "Binarymap.sig"; TPu "Binarymap.sml";
TPu "Listsort.sig"; TPu "Listsort.sml";
PKu "KernelSig.sig"; PKu "KernelSig.sml";
PKu "FinalType-sig.sml"; PKu "FinalTerm-sig.sml";
PKu "FinalThm-sig.sml"; PKu "FinalNet-sig.sml";
PKu "FinalTag-sig.sml";
TPu "Binaryset.sig"; TPu "Binaryset.sml";
PMu "UnicodeChars.sig"; PMu "UnicodeChars.sml";
PKu "Lexis.sig"; PKu "Lexis.sml";
K0u "Subst.sig"; K0u "Subst.sml";
K0u "KernelTypes.sml";
K0u "Type.sig"; K0u "Type.sml";
K0u "Term.sig"; K0u "Term.sml";
Tu "Compute.sig"; Tu "Compute.sml";
Tu "std-thmsig.ML"; Tu "std-thm.ML";
pr "KERNEL_PRELUDE_DONE\n";

(* sanity: kernel actually works *)
val () = let val bt = Type.mk_type("bool",[])
             val v  = Term.mk_var("p", bt)
             val th = Thm.REFL v
         in pr ("KERNEL_SANITY hyps=" ^ Int.toString (List.length (Thm.hyp th)) ^ "\n") end;

pr "EXPORTING /tmp/hol4_kernel\n";
val () = PolyML.export("/tmp/hol4_kernel", PolyML.rootFunction);
pr "KERNEL_CHECKPOINT_DONE\n";
