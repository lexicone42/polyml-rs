(* diff-corpus FUZZ DRIVER: fuzz_array  (domain = Array / ArraySlice)  (2026-06-17)
   ================================================================
   The STRUCTURE complement to the arithmetic fuzz (fuzz_int/word/real/...).
   A DETERMINISTIC generative differential fuzz over the Array and ArraySlice
   Basis structures. A hand-rolled LCG PRNG (seed = 0w1) drives operand
   generation; the SAME pure-SML code runs IDENTICALLY on upstream PolyML and
   on our `poly run`, so both consume the EXACT same random sequence and any
   @@<label>=<value> divergence is a faithfulness bug in OUR port.

   KEY BUG-HUNTING PRINCIPLE: test MULTIPLE SURFACES of the same operation —
   a value built/accessed one way hits a different code path than another:
     * build identical contents three ways (array+update loop / fromList /
       tabulate), and freeze two ways (Array.foldr (::) [] vs Array.vector then
       Vector.foldr) — cross-check they agree.
     * round-trips: update then sub; Array<->Vector; slice then vector.
     * bulk ops: copy / copyVec / modify / modifyi / app / appi / foldl / foldr /
       foldli / foldri / find / findi / exists / all / collate.
     * ArraySlice windows that mutate ONLY their range (neighbours unchanged).
   Plus ALGEBRAIC LAWS emitted as @@law_* self-checks (ride along free).

   DETERMINISM: identical LCG => identical input sequence => any divergence is
   ours. Sections run in a FIXED order; do NOT reorder/insert draws.

   TOTAL stringification: arrays are frozen to a canonical list-of-ints string;
   any raise (Subscript/Size/Overflow/...) becomes a COMPARABLE TOKEN via `wrap`,
   so both sides raising the same class AGREE (not a divergence).

   NOTE on basis surface: `Array.fromVector` is NOT present on this checkpoint's
   basis, so the Vector->Array bridge is done via Array.tabulate over the vector
   (an equivalent surface). `Array.vector` (Array->Vector) IS present and used. *)

(* ===== SHARED FUZZ HEADER ===== *)
(* ---- ref-force helper: defeats inline specialization (forces RTS/boxed path) ---- *)
fun I x = let val r = ref x in !r end;

(* ---- the LCG (Knuth/MMIX constants); default-int config => `word` is 63-bit ---- *)
val s = ref (0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
(* a non-negative draw from the high bits (drop low-bit LCG weakness) *)
fun nxt () = Word.toInt (Word.>> (step (), 0w11));
(* a fresh bit *)
fun bit () = Word.toInt (Word.andb (step (), 0w1));
(* random in [0, n)  (n > 0) *)
fun upto n = nxt () mod n;

(* ---- emit one labelled result line (the @@ tag the harness diffs) ---- *)
fun emit (label, v) = print ("@@" ^ label ^ "=" ^ v ^ "\n");

(* ---- TOTAL deterministic wrapper: any raise becomes a COMPARABLE TOKEN ---- *)
fun wrap f = (f ())
      handle Subscript => "SUB"
           | Size      => "SIZE"
           | Empty     => "EMPTY"
           | Div       => "DIV"
           | Overflow  => "OVF"
           | Chr       => "CHR"
           | Option    => "OPT"
           | _         => "EXN";

fun B b  = Bool.toString b;      (* bool    -> "true"/"false" *)
fun N n  = Int.toString n;       (* int     -> decimal *)
(* ===== END SHARED HEADER ===== *)

(* ---- canonical freeze: an int array -> a deterministic "[e0,e1,...]" string.
   This is the comparable VALUE for a (mutable) array. ---- *)
fun listToString xs = "[" ^ String.concatWith "," (List.map N xs) ^ "]";
fun arrFreeze (a : int array) : string =
  listToString (Array.foldr (fn (x, acc) => x :: acc) [] a);
fun arrToList (a : int array) : int list = Array.foldr (fn (x, acc) => x :: acc) [] a;
(* an alternative freeze surface: via Array.vector then Vector.foldr *)
fun arrFreezeViaVec (a : int array) : string =
  listToString (Vector.foldr (fn (x, acc) => x :: acc) [] (Array.vector a));
fun vecFreeze (v : int vector) : string =
  listToString (Vector.foldr (fn (x, acc) => x :: acc) [] v);

(* ---- random int list of length 0..maxlen, elements in a small range so
   duplicates / equality cases hit often ---- *)
fun rlist maxlen =
  List.tabulate (upto (maxlen + 1), fn _ => upto 20 - 10);  (* elements in -10..9 *)

(* build an array from a list three different ways; return the array.
   surface 0: Array.array(n,init) + update loop
   surface 1: Array.fromList
   surface 2: Array.tabulate(n, list-index) *)
fun buildArr (xs : int list) (surface : int) : int array =
  case surface of
      0 => let val n = List.length xs
               val a = Array.array (if n = 0 then 0 else n, 0)
               fun set (i, []) = ()
                 | set (i, y :: ys) = (Array.update (a, i, y); set (i + 1, ys))
           in set (0, xs); a end
    | 1 => Array.fromList xs
    | _ => let val v = Vector.fromList xs
           in Array.tabulate (List.length xs, fn i => Vector.sub (v, i)) end;

(* ===================================================================== *)
(* SECTION A:  build-3-ways + freeze-2-ways cross-check, length surfaces  *)
(* ===================================================================== *)
val nBuild = 250;
fun runBuild () =
  let
    fun loop i =
      if i >= nBuild then ()
      else
        let
          val xs = rlist 12
          val a0 = buildArr xs 0
          val a1 = buildArr xs 1
          val a2 = buildArr xs 2
          val si = N i
          val f0 = arrFreeze a0
          val f1 = arrFreeze a1
          val f2 = arrFreeze a2
          val fv = arrFreezeViaVec a1
        in
          (* the three build surfaces must produce identical contents *)
          emit ("arrbuild3_eq_" ^ si, B (f0 = f1 andalso f1 = f2));
          (* the two freeze surfaces must agree *)
          emit ("arrfreeze2_eq_" ^ si, B (f1 = fv));
          (* emit the canonical content so a content divergence is visible *)
          emit ("arrcontent_" ^ si, f1);
          (* length via Array.length vs length of frozen list — two surfaces *)
          emit ("arrlen_" ^ si, N (Array.length a1));
          emit ("arrlen_list_" ^ si, N (List.length (arrToList a1)));
          emit ("law_len_eq_" ^ si, B (Array.length a1 = List.length xs));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION B:  sub / update round-trips, in/out-of-range indices          *)
(* ===================================================================== *)
val nSub = 200;
fun runSub () =
  let
    fun loop i =
      if i >= nSub then ()
      else
        let
          val xs = rlist 10
          val a = buildArr xs 1
          val len = Array.length a
          val si = N i
          (* index possibly out of range: 0..len+1 and -1 *)
          val idx = (upto (len + 3)) - 1   (* -1 .. len+1 *)
          val v = upto 1000 - 500
        in
          (* read at idx (wrap SUB if oob) *)
          emit ("arrsub_" ^ si, wrap (fn () => N (Array.sub (a, idx))));
          (* cross-surface read: List.nth of the frozen list *)
          emit ("arrsub_nth_" ^ si, wrap (fn () => N (List.nth (arrToList a, idx))));
          (* update at idx then read back; if oob, both raise SUB *)
          emit ("arrupd_rt_" ^ si,
                wrap (fn () => (Array.update (a, idx, v); N (Array.sub (a, idx)))));
          (* after the (possibly successful) update, the whole content *)
          emit ("arrupd_content_" ^ si, arrFreeze a);
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION C:  copy / copyVec (region semantics, di offsets, oob)         *)
(* ===================================================================== *)
val nCopy = 180;
fun runCopy () =
  let
    fun loop i =
      if i >= nCopy then ()
      else
        let
          val xs = rlist 8
          val src = buildArr xs 1
          val slen = Array.length src
          val si = N i
          (* dst of size slen..slen+5, di in 0..(dstlen) so some go oob *)
          val extra = upto 6
          val dstlen = slen + extra
          val di = upto (dstlen + 2)   (* may exceed -> SUB *)
        in
          (* copy src into a fresh same-size array, content equal *)
          emit ("arrcopy_same_" ^ si,
                wrap (fn () =>
                  let val d = Array.array (if slen = 0 then 0 else slen, ~99)
                  in Array.copy {src = src, dst = d, di = 0}; arrFreeze d end));
          (* copy with di offset into a larger zeroed array *)
          emit ("arrcopy_off_" ^ si,
                wrap (fn () =>
                  let val d = Array.array (if dstlen = 0 then 0 else dstlen, 0)
                  in Array.copy {src = src, dst = d, di = di}; arrFreeze d end));
          (* copyVec: same but source is a Vector *)
          emit ("arrcopyVec_off_" ^ si,
                wrap (fn () =>
                  let val v = Array.vector src
                      val d = Array.array (if dstlen = 0 then 0 else dstlen, 0)
                  in Array.copyVec {src = v, dst = d, di = di}; arrFreeze d end));
          (* in-place self-copy di=0 is identity *)
          emit ("arrcopy_self_" ^ si,
                wrap (fn () => (Array.copy {src = src, dst = src, di = 0}; arrFreeze src)));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION D:  modify / modifyi / app / appi (index correctness)          *)
(* ===================================================================== *)
val nMod = 180;
fun runMod () =
  let
    fun loop i =
      if i >= nMod then ()
      else
        let
          val xs = rlist 10
          val si = N i
          (* modify (+1) vs a map-rebuild *)
          val am = buildArr xs 1
          val () = Array.modify (fn x => x + 1) am
          val rebuilt = listToString (List.map (fn x => x + 1) xs)
          val () = emit ("arrmod_" ^ si, arrFreeze am)
          val () = emit ("arrmod_eq_" ^ si, B (arrFreeze am = rebuilt))
          (* modifyi (i*x) vs tabulate(len, fn i => i * xs[i]) *)
          val ami = buildArr xs 1
          val () = Array.modifyi (fn (j, x) => j * x) ami
          val expect = listToString (List.tabulate (List.length xs, fn j => j * List.nth (xs, j)))
          val () = emit ("arrmodi_" ^ si, arrFreeze ami)
          val () = emit ("arrmodi_eq_" ^ si, B (arrFreeze ami = expect))
          (* app: accumulate into ref list, compare to frozen (reversed) *)
          val aa = buildArr xs 1
          val racc = ref ([] : int list)
          val () = Array.app (fn x => racc := x :: !racc) aa
          val () = emit ("arrapp_" ^ si, listToString (List.rev (!racc)))
          val () = emit ("arrapp_eq_" ^ si, B (List.rev (!racc) = arrToList aa))
          (* appi: accumulate i*x, compare to foldli i*x sum *)
          val ai = buildArr xs 1
          val rsum = ref 0
          val () = Array.appi (fn (j, x) => rsum := !rsum + j * x) ai
          val foldsum = Array.foldli (fn (j, x, acc) => acc + j * x) 0 ai
          val () = emit ("arrappi_" ^ si, N (!rsum))
          val () = emit ("arrappi_eq_" ^ si, B (!rsum = foldsum))
        in loop (i + 1) end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION E:  foldl / foldr / foldli / foldri, ordering laws             *)
(* ===================================================================== *)
val nFold = 180;
fun runFold () =
  let
    fun loop i =
      if i >= nFold then ()
      else
        let
          val xs = rlist 12
          val a = buildArr xs 1
          val si = N i
          val sl = Array.foldl (op +) 0 a
          val sr = Array.foldr (op +) 0 a
          (* foldl (::) [] reverses; foldr (::) [] preserves *)
          val rev = Array.foldl (fn (x, acc) => x :: acc) [] a
          val ident = Array.foldr (fn (x, acc) => x :: acc) [] a
        in
          emit ("arrfoldl_sum_" ^ si, N sl);
          emit ("arrfoldr_sum_" ^ si, N sr);
          emit ("law_foldsum_eq_" ^ si, B (sl = sr));         (* + commutes *)
          emit ("arrfoldl_rev_" ^ si, listToString rev);
          emit ("arrfoldr_id_" ^ si, listToString ident);
          emit ("law_foldl_isrev_" ^ si, B (rev = List.rev (arrToList a)));
          emit ("law_foldr_isid_" ^ si, B (ident = arrToList a));
          (* foldli / foldri index-weighted sums *)
          emit ("arrfoldli_" ^ si, N (Array.foldli (fn (j, x, acc) => acc + j * x) 0 a));
          emit ("arrfoldri_" ^ si, N (Array.foldri (fn (j, x, acc) => acc + j * x) 0 a));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION F:  find / findi / exists / all / collate                      *)
(* ===================================================================== *)
val nFind = 180;
fun runFind () =
  let
    fun loop i =
      if i >= nFind then ()
      else
        let
          val xs = rlist 12
          val a = buildArr xs 1
          val si = N i
          (* threshold predicate *)
          val t = upto 20 - 10
          fun p x = x > t
          val fnd = Array.find p a
          val ex = Array.exists p a
          val al = Array.all p a
          (* manual first-match by scan over the list *)
          val manual = List.find p (arrToList a)
          (* a SECOND random array for collate (RTS-ish lexicographic) *)
          val ys = rlist 12
          val b = buildArr ys 1
        in
          emit ("arrfind_" ^ si, case fnd of SOME x => N x | NONE => "NONE");
          emit ("law_find_match_" ^ si, B (fnd = manual));
          (* findi: index correctness — index is into the array *)
          emit ("arrfindi_" ^ si,
                case Array.findi (fn (j, x) => p x) a of
                    SOME (j, x) => N j ^ ":" ^ N x | NONE => "NONE");
          emit ("arrexists_" ^ si, B ex);
          emit ("law_exists_find_" ^ si, B (ex = (case fnd of SOME _ => true | NONE => false)));
          emit ("arrall_" ^ si, B al);
          emit ("law_all_notexists_" ^ si, B (al = not (Array.exists (fn x => not (p x)) a)));
          emit ("arrcollate_" ^ si,
                case Array.collate Int.compare (a, b) of
                    LESS => "LT" | EQUAL => "EQ" | GREATER => "GT");
          (* cross-check collate against List.collate on the frozen lists *)
          emit ("law_collate_" ^ si,
                B (Array.collate Int.compare (a, b)
                   = List.collate Int.compare (arrToList a, arrToList b)));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION G:  Array <-> Vector bridge                                    *)
(* ===================================================================== *)
val nBridge = 150;
fun runBridge () =
  let
    fun loop i =
      if i >= nBridge then ()
      else
        let
          val xs = rlist 12
          val a = buildArr xs 1
          val si = N i
          val v = Array.vector a       (* Array -> Vector *)
          (* Vector -> Array (no Array.fromVector here): tabulate over the vector *)
          val a2 = Array.tabulate (Vector.length v, fn j => Vector.sub (v, j))
        in
          emit ("arr2vec_" ^ si, vecFreeze v);
          emit ("law_arr2vec_eq_" ^ si, B (vecFreeze v = arrFreeze a));
          emit ("vec2arr_rt_" ^ si, B (arrFreeze a2 = arrFreeze a));   (* round-trip *)
          emit ("law_veclen_" ^ si, B (Vector.length v = Array.length a));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION H:  ArraySlice — slice/subslice/full, sub/length, oob          *)
(*   foldl/foldr/foldli/foldri/app/appi over the window, vector, copy,    *)
(*   modify (mutates only the window), getItem, collate, base.            *)
(* ===================================================================== *)
val nSlice = 220;
fun runSlice () =
  let
    fun loop i =
      if i >= nSlice then ()
      else
        let
          val xs = rlist 12
          val a = buildArr xs 1
          val len = Array.length a
          val si = N i
          (* slice params: start 0..len, length NONE or SOME k (k may overrun) *)
          val start = upto (len + 2)              (* 0 .. len+1 (oob possible) *)
          val useNone = (bit () = 0)
          val k = upto (len + 2)                  (* 0 .. len+1 *)
          val si_idx = (upto (len + 3)) - 1       (* slice-relative sub index, may be oob *)
          fun mkSlice () =
            if useNone then ArraySlice.slice (a, start, NONE)
            else ArraySlice.slice (a, start, SOME k)
          (* the expected window as a list (for cross-checking), totalized *)
          fun expectWindow () =
            let val xl = arrToList a
                val avail = len - start
                val take = if useNone then avail else (if k <= avail then k else ~1)
            in if start < 0 orelse start > len orelse take < 0 then []  (* oob marker *)
               else List.take (List.drop (xl, start), take)
            end
        in
          (* slice creation (oob => SUB) and its length *)
          emit ("as_len_" ^ si, wrap (fn () => N (ArraySlice.length (mkSlice ()))));
          (* foldl sum over the window vs expected list sum *)
          emit ("as_foldl_" ^ si,
                wrap (fn () => N (ArraySlice.foldl (op +) 0 (mkSlice ()))));
          emit ("as_foldl_eq_" ^ si,
                wrap (fn () =>
                  B (ArraySlice.foldl (op +) 0 (mkSlice ())
                     = List.foldl (op +) 0 (expectWindow ()))));
          (* foldr (::) [] over the window = the window list, in order *)
          emit ("as_window_" ^ si,
                wrap (fn () => listToString (ArraySlice.foldr (fn (x, acc) => x :: acc) [] (mkSlice ()))));
          emit ("as_window_eq_" ^ si,
                wrap (fn () =>
                  B (ArraySlice.foldr (fn (x, acc) => x :: acc) [] (mkSlice ()) = expectWindow ())));
          (* foldli / foldri index-weighted (index is slice-relative) *)
          emit ("as_foldli_" ^ si,
                wrap (fn () => N (ArraySlice.foldli (fn (j, x, acc) => acc + j * x) 0 (mkSlice ()))));
          emit ("as_foldri_" ^ si,
                wrap (fn () => N (ArraySlice.foldri (fn (j, x, acc) => acc + j * x) 0 (mkSlice ()))));
          (* sub at a slice-relative index possibly oob (si_idx drawn above) *)
          emit ("as_sub_" ^ si, wrap (fn () => N (ArraySlice.sub (mkSlice (), si_idx))));
          (* vector of the slice = the window as a vector *)
          emit ("as_vector_" ^ si, wrap (fn () => vecFreeze (ArraySlice.vector (mkSlice ()))));
          (* getItem head *)
          emit ("as_getItem_" ^ si,
                wrap (fn () => case ArraySlice.getItem (mkSlice ()) of
                                   SOME (x, _) => N x | NONE => "NONE"));
          emit ("as_isEmpty_" ^ si, wrap (fn () => B (ArraySlice.isEmpty (mkSlice ()))));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION I:  ArraySlice mutation windows — modify/modifyi/copy/copyVec  *)
(*   must mutate ONLY the slice range; neighbours unchanged.              *)
(* ===================================================================== *)
val nSliceMut = 150;
fun runSliceMut () =
  let
    fun loop i =
      if i >= nSliceMut then ()
      else
        let
          val xs0 = rlist 12
          (* ensure a non-empty list so the window is well-defined; if empty,
             substitute a fixed singleton (keeps draws balanced: rlist already
             consumed its draws) *)
          val xs = if List.null xs0 then [0] else xs0
          val len = List.length xs
          val si = N i
          (* in-range window so the mutation is well-defined *)
          val start = upto len                          (* 0 .. len-1 *)
          val avail = len - start
          val k = upto (avail + 1)                      (* 0 .. avail *)
          (* modify (+100) on the window; neighbours must be untouched *)
          val am = buildArr xs 1
          val sm = ArraySlice.slice (am, start, SOME k)
          val () = ArraySlice.modify (fn x => x + 100) sm
          val () = emit ("as_modify_" ^ si, arrFreeze am)
          (* expected: xs with [start, start+k) bumped by 100 *)
          val expect =
            listToString (List.tabulate (len, fn j =>
              let val e = List.nth (xs, j)
              in if j >= start andalso j < start + k then e + 100 else e end))
          val () = emit ("as_modify_eq_" ^ si, B (arrFreeze am = expect))
          (* modifyi: window-relative index *)
          val ami = buildArr xs 1
          val smi = ArraySlice.slice (ami, start, SOME k)
          val () = ArraySlice.modifyi (fn (j, x) => x + j) smi
          val expecti =
            listToString (List.tabulate (len, fn j =>
              let val e = List.nth (xs, j)
              in if j >= start andalso j < start + k then e + (j - start) else e end))
          val () = emit ("as_modifyi_" ^ si, arrFreeze ami)
          val () = emit ("as_modifyi_eq_" ^ si, B (arrFreeze ami = expecti))
          (* ArraySlice.copy: copy a window into a fresh array region *)
          val ac = buildArr xs 1
          val sc = ArraySlice.slice (ac, start, SOME k)
          val dst = Array.array (len + 2, 0)
          val () = ArraySlice.copy {src = sc, dst = dst, di = 1}
          val () = emit ("as_copy_" ^ si, arrFreeze dst)
          (* ArraySlice.copyVec from a VectorSlice into an array *)
          val dst2 = Array.array (len + 2, 0)
          val vs = VectorSlice.slice (Vector.fromList xs, start, SOME k)
          val () = ArraySlice.copyVec {src = vs, dst = dst2, di = 1}
          val () = emit ("as_copyVec_" ^ si, arrFreeze dst2)
          (* subslice of a window, then sum *)
          val asub = buildArr xs 1
          val sfull = ArraySlice.slice (asub, start, SOME k)
          val sub_start = upto (k + 1)
          val () = emit ("as_subslice_" ^ si,
                         wrap (fn () =>
                           N (ArraySlice.foldl (op +) 0
                                (ArraySlice.subslice (sfull, sub_start, NONE)))))
        in loop (i + 1) end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION J:  fixed corner cases (named) — empty/singleton/boundaries    *)
(* ===================================================================== *)
fun runCorners () =
  let in
    (* empty array surfaces *)
    emit ("c_empty_len", N (Array.length (Array.fromList ([] : int list))));
    emit ("c_empty_foldl", N (Array.foldl (op +) 0 (Array.fromList ([] : int list))));
    emit ("c_empty_freeze", arrFreeze (Array.fromList ([] : int list)));
    emit ("c_empty_sub", wrap (fn () => N (Array.sub (Array.fromList ([] : int list), 0))));
    (* singleton *)
    emit ("c_single_sub", wrap (fn () => N (Array.sub (Array.fromList [42], 0))));
    emit ("c_single_sub_oob", wrap (fn () => N (Array.sub (Array.fromList [42], 1))));
    (* negative size => Size *)
    emit ("c_neg_size", wrap (fn () => N (Array.length (Array.array (~1, 0)))));
    emit ("c_neg_tab", wrap (fn () => N (Array.length (Array.tabulate (~1, fn i => i)))));
    (* tabulate 0 *)
    emit ("c_tab0", N (Array.length (Array.tabulate (0, fn i => i))));
    (* sub at -1 *)
    emit ("c_sub_neg", wrap (fn () => N (Array.sub (Array.fromList [1,2,3], ~1))));
    (* update oob *)
    emit ("c_upd_oob", wrap (fn () => let val a = Array.array (3, 0) in Array.update (a, 3, 1); "NO" end));
    emit ("c_upd_neg", wrap (fn () => let val a = Array.array (3, 0) in Array.update (a, ~1, 1); "NO" end));
    (* copy where dst too small => Subscript *)
    emit ("c_copy_small",
          wrap (fn () =>
            let val src = Array.fromList [1,2,3] val dst = Array.array (2, 0)
            in Array.copy {src = src, dst = dst, di = 0}; "NO" end));
    emit ("c_copy_di_oob",
          wrap (fn () =>
            let val src = Array.fromList [1,2,3] val dst = Array.array (3, 0)
            in Array.copy {src = src, dst = dst, di = 1}; "NO" end));
    (* copyVec too small *)
    emit ("c_copyVec_small",
          wrap (fn () =>
            let val v = Vector.fromList [1,2,3] val dst = Array.array (2, 0)
            in Array.copyVec {src = v, dst = dst, di = 0}; "NO" end));
    (* ArraySlice corners *)
    emit ("c_as_slice_oob",
          wrap (fn () => N (ArraySlice.length (ArraySlice.slice (Array.fromList [1,2,3], 1, SOME 5)))));
    emit ("c_as_slice_start_oob",
          wrap (fn () => N (ArraySlice.length (ArraySlice.slice (Array.fromList [1,2,3], 4, NONE)))));
    emit ("c_as_full_empty",
          N (ArraySlice.length (ArraySlice.full (Array.fromList ([] : int list)))));
    emit ("c_as_sub_oob",
          wrap (fn () =>
            let val sl = ArraySlice.slice (Array.fromList [1,2,3,4], 1, SOME 2)
            in N (ArraySlice.sub (sl, 2)) end));
    emit ("c_as_base",
          let val a = Array.fromList [0,0,0,0,0]
              val sl = ArraySlice.slice (a, 2, SOME 2)
              val (_, off, n) = ArraySlice.base sl
          in N off ^ ":" ^ N n end);
    (* array of arrays: ref identity vs structural — fromList of arrays.
       (= on arrays is reference equality; two equal-content arrays are NOT =.) *)
    emit ("c_arr_eq_refl", let val a = Array.fromList [1,2,3] in B (a = a) end);
    emit ("c_arr_eq_distinct",
          let val a = Array.fromList [1,2,3] val b = Array.fromList [1,2,3] in B (a = b) end);
    (* a tabulate function with side effects observes deterministic order via index *)
    emit ("c_tab_indexsum",
          N (Array.foldl (op +) 0 (Array.tabulate (10, fn i => i * i))))
  end;

(* run all sections (fixed order => deterministic LCG consumption) *)
val () = runBuild ();
val () = runSub ();
val () = runCopy ();
val () = runMod ();
val () = runFold ();
val () = runFind ();
val () = runBridge ();
val () = runSlice ();
val () = runSliceMut ();
val () = runCorners ();
