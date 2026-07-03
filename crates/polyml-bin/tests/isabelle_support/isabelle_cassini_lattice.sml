(* THE CASSINI LATTICE — parallel-verified Fibonacci, where the
   consistency of the parallel work is itself kernel-checked.

   Last night's multiplication table was 144 INDEPENDENT theorems: the
   audit that says "they're all correct" is harness code. Here the
   mathematics does the stitching. Two parallel phases:

   PHASE 1 (cells): workers prove `⊢ fib n ≡ F_n` for n = 0..15 by a
   verified evaluator over the fib defining axioms (every step a
   kernel-checked instantiation, the additions closed by a verified
   add evaluator on unary numerals).

   PHASE 2 (windows): for each window of three consecutive cells,
   a worker instantiates the GENERAL Cassini identity (cassini_a/b,
   proved by induction in isabelle_fibonacci.sml) at that index and
   TRANSPORTS the three cell theorems into it — producing a concrete
   window theorem like `⊢ 34·89 = 55² + 1` whose proof runs through
   the general identity, NOT through evaluation. Each window consumes
   cells proved by DIFFERENT workers: parallel work stitched across
   thread boundaries by inference, the kernel arbitrating every seam.

   Every cell sits in up to three overlapping windows; a single wrong
   value would make two windows underivable. The audit cross-checks
   each window's literals by independent SML arithmetic — closing the
   loop between the kernel's derivation and ordinary computation.

   Runs as a delta appended to isabelle_fibonacci.sml on the
   with_nt_helpers tier (ONE theory lineage — the base arithmetic
   lemmas are re-instantiated onto ctxtF2, per the standard
   final-context discipline).                                          *)

val () = out "CASSINI_LATTICE_BEGIN\n";

(* Proof-term RECORDING off (the kernel still CHECKS every inference —
   this drops only the retained proof-tree data structure). The deep
   oeq_trans chains over unary additions otherwise retain hundreds of
   MB of proof terms and grind the run into GC (the established remedy
   from the Bertrand campaign). *)
val () = Proofterm.proofs := 0;

(* ---- base-lemma instantiators, re-derived on the fibonacci context ---- *)
fun lit 0 = ZeroC | lit k = suc (lit (k - 1));

fun oeqreflF_at t =
  beta_norm (Drule.infer_instantiate ctxtF2 [(("a", 0), ctermF2 t)] oeq_refl_v);
fun add0F_at t =
  beta_norm (Drule.infer_instantiate ctxtF2 [(("n", 0), ctermF2 t)] add_0_v);
fun addSucF_at (mt, nt) =
  beta_norm (Drule.infer_instantiate ctxtF2
    [(("m", 0), ctermF2 mt), (("n", 0), ctermF2 nt)] add_Suc_v);

(* add_eval (a, b) : ⊢ oeq (add (lit a) (lit b)) (lit (a+b)) — linear in a. *)
fun add_eval (0, b) = add0F_at (lit b)
  | add_eval (a, b) =
      let
        val step = addSucF_at (lit (a - 1), lit b);
        val ih = add_eval (a - 1, b);
        val sc = Suc_cong OF [ih];
      in
        oeq_trans OF [step, sc]
      end;

(* dbl_eval j : ⊢ oeq (dbl (lit j)) (lit (2j)). *)
fun dbl_eval 0 = dbl0_2
  | dbl_eval j =
      let
        val step = dblS2 (lit (j - 1));
        val ih = dbl_eval (j - 1);
        val sc = Suc_cong OF [Suc_cong OF [ih]];
      in
        oeq_trans OF [step, sc]
      end;

(* Fibonacci values in SML — the INDEPENDENT arithmetic the audit uses. *)
fun fibv 0 = 0 | fibv 1 = 1 | fibv n = fibv (n - 1) + fibv (n - 2);

(* ---- PHASE 1: cell theorems, ⊢ oeq (fib (lit n)) (lit F_n) ----
   Built ITERATIVELY (a worker's cost is one linear chain, not an
   exponential recursion). *)
fun fib_cell n =
  let
    fun up (k, prev2, prev1) =           (* prev2 : cell (k-2), prev1 : cell (k-1) *)
      if k > n then (if n = 0 then fib_0 else prev1)
      else
        let
          val inst = beta_norm (Drule.infer_instantiate ctxtF2
                [(("kF0", 0), ctermF2 (lit (k - 2)))] fib_SS_v);
          (* ⊢ oeq (fib (lit k)) (add (fib (lit (k-1))) (fib (lit (k-2)))) *)
          val a1 = fib (lit (k - 1)) and a2 = fib (lit (k - 2));
          val base = oeqreflF_at (add a1 a2);
          val c1 = transport (fn w => oeq (add a1 a2) (add w a2))
                     (a1, lit (fibv (k - 1))) prev1 base;
          val c2 = transport (fn w => oeq (add a1 a2) (add (lit (fibv (k - 1))) w))
                     (a2, lit (fibv (k - 2))) prev2 c1;
          val av = add_eval (fibv (k - 1), fibv (k - 2));
          val cell = oeq_trans OF [oeq_trans OF [inst, c2], av];
        in
          up (k + 1, prev1, cell)
        end;
  in
    if n = 0 then fib_0 else if n = 1 then fib_1
    else up (2, fib_0, fib_1)
  end;

val n_cells = 16;                        (* cells 0..15 *)
val () = Multithreading.max_threads_update 0;
val () = out ("max_threads = " ^ Int.toString (Multithreading.max_threads ()) ^ "\n");

val tc0 = Time.now ();
val cells = Vector.fromList
  (Par_List.map fib_cell (List.tabulate (n_cells, fn i => i)));
val tc1 = Time.now ();

(* Audit the cells: 0-hyp + aconv statements built independently. *)
val cells_sound =
  List.foldl
    (fn (n, acc) =>
        let val th = Vector.sub (cells, n) in
          if null (Thm.hyps_of th) andalso
             (Thm.prop_of th) aconv jT (oeq (fib (lit n)) (lit (fibv n)))
          then acc + 1 else acc
        end)
    0 (List.tabulate (n_cells, fn i => i));
val () = out ("SOUND_CELLS " ^ Int.toString cells_sound ^ "/" ^
              Int.toString n_cells ^ "\n");
val () = out ("CELLS_ELAPSED_MS " ^
              LargeInt.toString (Time.toMilliseconds (tc1 - tc0)) ^ "\n");

(* ---- PHASE 2: window theorems — Cassini instantiated at each index,
   the three cell theorems transported in. Windows consume cells proved
   by DIFFERENT phase-1 workers. ---- *)

(* Even window j: from cassini_a, derive
   ⊢ oeq (add (mult (lit F_2j) (lit F_2j+2)) one) (sq (lit F_2j+1)). *)
fun window_a j =
  let
    val m = 2 * j;
    val inst = beta_norm (Drule.infer_instantiate ctxtF2
          [(("k", 0), ctermF2 (lit j))] cassini_a); (* jT (Aprop (dbl (lit j))) *)
    val t1 = transport Aprop (dbl (lit j), lit m) (dbl_eval j) inst;
    val fm = fib (lit m) and fm1 = fib (lit (m + 1)) and fm2 = fib (lit (m + 2));
    val (vm, vm1, vm2) = (fibv m, fibv (m + 1), fibv (m + 2));
    val t2 = transport (fn w => oeq (add (mult w fm2) one) (sq fm1))
               (fm, lit vm) (Vector.sub (cells, m)) t1;
    val t3 = transport (fn w => oeq (add (mult (lit vm) w) one) (sq fm1))
               (fm2, lit vm2) (Vector.sub (cells, m + 2)) t2;
    val t4 = transport (fn w => oeq (add (mult (lit vm) (lit vm2)) one) (sq w))
               (fm1, lit vm1) (Vector.sub (cells, m + 1)) t3;
  in
    t4
  end;

(* Odd window j: from cassini_b, derive
   ⊢ oeq (mult (lit F_2j+1) (lit F_2j+3)) (add (sq (lit F_2j+2)) one). *)
fun window_b j =
  let
    val m = 2 * j;
    val inst = beta_norm (Drule.infer_instantiate ctxtF2
          [(("k", 0), ctermF2 (lit j))] cassini_b); (* jT (Bprop (dbl (lit j))) *)
    val t1 = transport Bprop (dbl (lit j), lit m) (dbl_eval j) inst;
    val f1 = fib (lit (m + 1)) and f2 = fib (lit (m + 2)) and f3 = fib (lit (m + 3));
    val (v1, v2, v3) = (fibv (m + 1), fibv (m + 2), fibv (m + 3));
    val t2 = transport (fn w => oeq (mult w f3) (add (sq f2) one))
               (f1, lit v1) (Vector.sub (cells, m + 1)) t1;
    val t3 = transport (fn w => oeq (mult (lit v1) w) (add (sq f2) one))
               (f3, lit v3) (Vector.sub (cells, m + 3)) t2;
    val t4 = transport (fn w => oeq (mult (lit v1) (lit v3)) (add (sq w) one))
               (f2, lit v2) (Vector.sub (cells, m + 2)) t3;
  in
    t4
  end;

datatype window = WA of int | WB of int;
val windows =
  List.tabulate (7, WA) @ List.tabulate (7, WB);  (* indices up to 15 *)

val tw0 = Time.now ();
val window_thms =
  Par_List.map (fn WA j => (WA j, window_a j) | WB j => (WB j, window_b j))
    windows;
val tw1 = Time.now ();

(* Audit each window: 0-hyp, aconv the independently-built statement,
   AND the literals satisfy Cassini numerically in SML integers. *)
fun window_intended (WA j) =
      let val m = 2 * j;
          val (vm, vm1, vm2) = (fibv m, fibv (m + 1), fibv (m + 2));
      in (jT (oeq (add (mult (lit vm) (lit vm2)) one) (sq (lit vm1))),
          vm * vm2 + 1 = vm1 * vm1)
      end
  | window_intended (WB j) =
      let val m = 2 * j;
          val (v1, v2, v3) = (fibv (m + 1), fibv (m + 2), fibv (m + 3));
      in (jT (oeq (mult (lit v1) (lit v3)) (add (sq (lit v2)) one)),
          v1 * v3 = v2 * v2 + 1)
      end;

val windows_sound =
  List.foldl
    (fn ((w, th), acc) =>
        let val (intended, arith_ok) = window_intended w in
          if null (Thm.hyps_of th) andalso (Thm.prop_of th) aconv intended
             andalso arith_ok
          then acc + 1 else acc
        end)
    0 window_thms;
val () = out ("SOUND_WINDOWS " ^ Int.toString windows_sound ^ "/" ^
              Int.toString (length windows) ^ "\n");
val () = out ("WINDOWS_ELAPSED_MS " ^
              LargeInt.toString (Time.toMilliseconds (tw1 - tw0)) ^ "\n");

(* NEGATIVE probe: a wrong-constant window statement must NOT match —
   the +1 replaced by +2 in the first even window. *)
val probe_lattice =
  let
    val th = window_a 1;                 (* ⊢ 1·3 + 1 = 2² *)
    val bogus = jT (oeq (add (mult (lit (fibv 2)) (lit (fibv 4))) (suc one))
                        (sq (lit (fibv 3))));
  in
    not ((Thm.prop_of th) aconv bogus)
  end;
val () = out (if probe_lattice then "PROBE_OK lattice audit rejects +2 variant\n"
              else "PROBE_FAIL bogus window accepted\n");

val () =
  if cells_sound = n_cells andalso windows_sound = length windows
     andalso probe_lattice
  then out "LATTICE_CLOSED\n"
  else out "LATTICE_BROKEN\n";
val () = out "CASSINI_LATTICE_DONE\n";
