(* PARALLEL THEOREM PROVING — the multiplication table derived from the
   Peano axioms by genuine LCF kernel inference, one worker per goal,
   distributed by Isabelle's OWN futures scheduler (Par_List) on the
   polyml-rs parallel runtime.

   Each goal (a, b) is proved by a VERIFIED EVALUATOR written LCF-style:
   `mult_eval (a, b)` derives `⊢ oeq (mult A B) (lit (a*b))` (A, B unary
   numerals) by recursion — every step is a kernel-checked instantiation
   of the ntbase axioms (mult_0_right / mult_Suc_right / add_0 / add_Suc)
   chained with oeq_trans through Suc_cong / add_cong_rS congruences. No
   oracle, no reflection: the kernel certifies every cell.

   The goals are independent, so Par_List fans them across worker
   threads; under POLY_PARALLEL=1 those run on real cores. Each result
   is audited: 0 hypotheses + proposition aconv the intended statement
   built INDEPENDENTLY of the prover. A negative probe confirms the
   audit rejects a wrong table entry.

   Runs as a delta on the with_ntbase splice tier (the classical
   foundation + division/congruence base).

   NEXT DREAM (for whoever picks this up): the cells here are
   independent facts. The richer demo is a parallel-verified LATTICE —
   workers prove a Fibonacci value table, and the audit cross-checks
   ADJACENT cells with Cassini's identity AS A THEOREM (already in the
   tower: isabelle_fibonacci.sml). Then the consistency of the parallel
   work is itself kernel-checked: parallelism distributing goals whose
   mathematical structure stitches them back into one certified object. *)

val () = out "PAR_PROVING_BEGIN\n";

(* Unary numeral: lit k = Suc^k Zero. *)
fun lit 0 = ZeroC | lit k = suc (lit (k - 1));

(* add_eval (a, b) : ⊢ oeq (add (lit a) (lit b)) (lit (a+b)),
   by recursion on a via add_0 / add_Suc + Suc congruence. *)
fun add_eval (0, b) = add0S_at (lit b)
  | add_eval (a, b) =
      let
        val step = addSucS_at (lit (a - 1), lit b);
        val ih = add_eval (a - 1, b);
        val sc = Suc_cong OF [ih];
      in
        oeq_trans OF [step, sc]
      end;

(* mult_eval (a, b) : ⊢ oeq (mult (lit a) (lit b)) (lit (a*b)),
   by recursion on b via mult_0_right / mult_Suc_right, the IH lifted
   through the add congruence, then the verified addition. *)
fun mult_eval (a, 0) = mult0rS_at (lit a)
  | mult_eval (a, b) =
      let
        val step = multSrS_at (lit a, lit (b - 1));
        val ih = mult_eval (a, b - 1);
        val congr =
          add_cong_rS (lit a, mult (lit a) (lit (b - 1)), lit (a * (b - 1))) ih;
        val addp = add_eval (a, a * (b - 1));
      in
        oeq_trans OF [oeq_trans OF [step, congr], addp]
      end;

(* The intended statement, built independently of the prover. *)
fun intended (a, b) = jT (oeq (mult (lit a) (lit b)) (lit (a * b)));

(* Warm-up + sanity: one corner cell, audited. *)
val warm = mult_eval (12, 12);
val r_warm = checkS2 ("mult 12 12 = 144", warm, intended (12, 12));

(* NEGATIVE probe: the audit must REJECT a wrong table entry. *)
val bogus_ok =
  not ((Thm.prop_of (mult_eval (3, 4))) aconv
       (jT (oeq (mult (lit 3) (lit 4)) (lit 13))));
val () = out (if bogus_ok then "PROBE_OK audit rejects 3*4=13\n"
              else "PROBE_FAIL bogus accepted\n");

(* THE PARALLEL TABLE: every cell of the 12 x 12 multiplication table,
   one future per cell, on Isabelle's own scheduler. *)
val () = Multithreading.max_threads_update 0;
val () = out ("max_threads = " ^ Int.toString (Multithreading.max_threads ()) ^ "\n");

val n_table = 12;
val goals =
  List.concat (List.tabulate (n_table, fn i =>
    List.tabulate (n_table, fn j => (i + 1, j + 1))));

val t0 = Time.now ();
val results = Par_List.map (fn (a, b) => (a, b, mult_eval (a, b))) goals;
val t1 = Time.now ();

(* Audit every theorem: 0-hyp + aconv the independent statement. *)
val sound =
  List.foldl
    (fn ((a, b, th), acc) =>
        if null (Thm.hyps_of th) andalso (Thm.prop_of th) aconv intended (a, b)
        then acc + 1 else acc)
    0 results;

val () = out ("SOUND_CELLS " ^ Int.toString sound ^ "/" ^
              Int.toString (length goals) ^ "\n");
val () = out ("TABLE_ELAPSED_MS " ^
              LargeInt.toString (Time.toMilliseconds (t1 - t0)) ^ "\n");
val () = out "PAR_PROVING_DONE\n";
