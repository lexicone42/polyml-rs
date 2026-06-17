(* diff-corpus GENERATIVE-DIFFERENTIAL FUZZ DRIVER: fuzz_vector  (domain = Vector / VectorSlice)
   ================================================================================
   The STRUCTURE complement to the arithmetic fuzz (fuzz_int/word/real/intinf/convert).
   Numbers are done; this generatively fuzzes the immutable Vector + VectorSlice
   Basis structures vs the upstream PolyML oracle.

   DETERMINISM (mandatory — CI re-runs this): a hand-rolled LCG (seed 0w1, the same
   Knuth/MMIX constants as fuzz_int.sml) drives operand generation. The IDENTICAL
   pure-SML code runs on upstream PolyML and on our `poly run`, so both consume the
   EXACT same random sequence => any @@<label>=<value> divergence is a faithfulness
   bug in OUR port. Sections run in a FIXED order; never reorder/insert draws.

   KEY BUG-HUNTING PRINCIPLE: test MULTIPLE SURFACES of the same operation, because
   a vector built/accessed one way hits a different code path than another. We build
   identical contents three ways (fromList / tabulate / Array.vector-bridge) and
   cross-check; we fold/map/find via several routes; we compare slice ops against the
   underlying sub-range computed independently.

   TOTALITY: every result is stringified deterministically and any raise (Subscript,
   Size, ...) becomes a COMPARABLE TOKEN, so both sides raising the same class AGREE
   (not a divergence). Vectors are immutable so the frozen value (foldr (::) []) is
   directly comparable.

   Algebraic laws ride along as @@law_* self-checks: a law false on BOTH sides is a
   shared spec quirk; a law differing between sides is caught as a normal divergence. *)

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

(* ---- stringify helpers ---- *)
fun B b = Bool.toString b;       (* bool -> "true"/"false" *)
fun N n = Int.toString n;        (* int  -> decimal *)
(* canonical string of an int list: "[a,b,c]" *)
fun L xs = "[" ^ String.concatWith "," (List.map Int.toString xs) ^ "]";
fun ordstr ord = (case ord of LESS => "LT" | EQUAL => "EQ" | GREATER => "GT");

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
(* ===== END SHARED HEADER ===== *)

(* ===================================================================== *)
(* operand generation: random int lists of length 0..MAXLEN with elements
   in a small range (so duplicate / equality cases hit).                  *)
(* ===================================================================== *)
val MAXLEN = 8;             (* lists of length 0..MAXLEN *)
val ELEMRANGE = 20;         (* elements in 0..ELEMRANGE-1 *)

fun relem () = upto ELEMRANGE;
fun rlist () = List.tabulate (upto (MAXLEN + 1), fn _ => relem ());

(* freeze a vector to its canonical int list (the comparable value) *)
fun freeze (v : int vector) : int list = Vector.foldr (op ::) [] v;

(* the three build surfaces of the SAME contents *)
fun buildFromList xs = Vector.fromList xs;
fun buildTabulate  xs =
  let val a = Vector.fromList xs   (* reference for tabulate to read from *)
  in Vector.tabulate (List.length xs, fn i => Vector.sub (a, i)) end;
fun buildBridge xs = Array.vector (Array.fromList xs);  (* Array<->Vector bridge *)

(* ===================================================================== *)
(* SECTION A: BUILD 3 ways + length surfaces + sub round-trips           *)
(* ===================================================================== *)
val nBuild = 200;

fun runBuild () =
  let
    fun loop i =
      if i >= nBuild then () else
      let
        val xs = rlist ()
        val si = N i
        val v1 = buildFromList xs
        val v2 = buildTabulate  xs
        val v3 = buildBridge    xs
        (* all three must freeze to the same list, equal to xs *)
        val eq3 = (freeze v1 = xs) andalso (freeze v2 = xs) andalso (freeze v3 = xs)
        (* length agreement across three surfaces *)
        val lenOK = (Vector.length v1 = List.length xs)
                    andalso (Vector.length v2 = List.length xs)
                    andalso (Vector.length v3 = List.length xs)
        (* a random index incl out-of-range: sub value vs List.nth, both wrapped *)
        val idx = upto (MAXLEN + 3)   (* may exceed length => SUB on both *)
        val subv  = wrap (fn () => N (Vector.sub (v1, idx)))
        val nthv  = wrap (fn () => N (List.nth (xs, idx)))
      in
        emit ("vecbuild3_eq_" ^ si, B eq3);
        emit ("veclen_ok_" ^ si, B lenOK);
        emit ("vecfreeze_" ^ si, L (freeze v1));
        emit ("vecsub_" ^ si ^ "_" ^ N idx, subv);
        emit ("vecsub_vs_nth_" ^ si, B (subv = nthv));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION B: tabulate (incl negative n => SIZE) + index correctness     *)
(* ===================================================================== *)
val nTab = 120;

fun runTab () =
  let
    fun loop i =
      if i >= nTab then () else
      let
        val si = N i
        (* mostly valid lengths, occasionally negative to hit SIZE *)
        val n = if upto 5 = 0 then ~(upto 4) - 1 else upto (MAXLEN + 1)
        (* tabulate with a position-dependent function *)
        val tv = wrap (fn () => L (freeze (Vector.tabulate (n, fn k => k * 3 + 1))))
        (* manual build of the same (when n >= 0) *)
        val mv = wrap (fn () => L (List.tabulate (n, fn k => k * 3 + 1)))
      in
        emit ("vectab_" ^ si ^ "_n" ^ N n, tv);
        emit ("vectab_vs_manual_" ^ si, B (tv = mv));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION C: map / mapi index correctness (two surfaces)                *)
(* ===================================================================== *)
val nMap = 150;

fun runMap () =
  let
    fun loop i =
      if i >= nMap then () else
      let
        val xs = rlist ()
        val si = N i
        val v = buildFromList xs
        (* map f via Vector.map vs via fromList o List.map *)
        val f = (fn x => x * 2 + 1)
        val m1 = freeze (Vector.map f v)
        val m2 = List.map f xs
        (* mapi: (i,x) -> i + x ; cross-check vs tabulate(len, fn i => i + sub) *)
        val mi1 = freeze (Vector.mapi (fn (k, x) => k + x) v)
        val mi2 = freeze (Vector.tabulate (Vector.length v, fn k => k + Vector.sub (v, k)))
      in
        emit ("vecmap_" ^ si, L m1);
        emit ("vecmap_vs_listmap_" ^ si, B (m1 = m2));
        emit ("vecmapi_" ^ si, L mi1);
        emit ("vecmapi_vs_tab_" ^ si, B (mi1 = mi2));
        emit ("law_map_len_" ^ si, B (List.length m1 = List.length xs));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION D: foldl / foldr / foldli / foldri                            *)
(* ===================================================================== *)
val nFold = 150;

fun runFold () =
  let
    fun loop i =
      if i >= nFold then () else
      let
        val xs = rlist ()
        val si = N i
        val v = buildFromList xs
        val suml = Vector.foldl (op +) 0 v
        val sumr = Vector.foldr (op +) 0 v
        (* foldl (::) [] = reversed; foldr (::) [] = in-order *)
        val revd  = Vector.foldl (op ::) [] v
        val ino   = Vector.foldr (op ::) [] v
        (* foldli / foldri sum of i*x — index correctness *)
        val fli = Vector.foldli (fn (k, x, a) => a + k * x) 0 v
        val fri = Vector.foldri (fn (k, x, a) => a + k * x) 0 v
        (* manual i*x sum *)
        val manli = let fun g (k, acc) = if k >= List.length xs then acc
                                         else g (k + 1, acc + k * List.nth (xs, k))
                    in g (0, 0) end
      in
        emit ("vecfoldl_sum_" ^ si, N suml);
        emit ("vecfoldr_sum_" ^ si, N sumr);
        emit ("law_foldlr_sum_eq_" ^ si, B (suml = sumr));   (* + is commutative *)
        emit ("vecfoldl_rev_" ^ si, L revd);
        emit ("law_foldl_is_rev_" ^ si, B (revd = List.rev xs));
        emit ("vecfoldr_id_" ^ si, L ino);
        emit ("law_foldr_is_id_" ^ si, B (ino = xs));
        emit ("vecfoldli_" ^ si, N fli);
        emit ("vecfoldri_" ^ si, N fri);
        emit ("law_foldlri_eq_" ^ si, B (fli = fri));
        emit ("law_foldli_manual_" ^ si, B (fli = manli));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION E: find / findi / exists / all                                *)
(* ===================================================================== *)
val nFind = 150;

fun runFind () =
  let
    fun loop i =
      if i >= nFind then () else
      let
        val xs = rlist ()
        val si = N i
        val v = buildFromList xs
        val thr = relem ()                      (* threshold predicate target *)
        val p = (fn x => x = thr)
        (* find vs first match by scan *)
        val fv = (case Vector.find p v of SOME y => N y | NONE => "NONE")
        val scanv = (case List.find p xs of SOME y => N y | NONE => "NONE")
        (* findi returns (index, value) *)
        val fiv = (case Vector.findi (fn (_, x) => p x) v of
                       SOME (k, y) => N k ^ ":" ^ N y | NONE => "NONE")
        (* manual first index of p *)
        val maniv = let fun g k = if k >= List.length xs then "NONE"
                                  else if p (List.nth (xs, k)) then N k ^ ":" ^ N (List.nth (xs, k))
                                  else g (k + 1)
                    in g 0 end
        val exv = Vector.exists p v
        val allv = Vector.all (fn x => x < ELEMRANGE) v   (* always true by gen *)
      in
        emit ("vecfind_" ^ si, fv);
        emit ("law_find_eq_scan_" ^ si, B (fv = scanv));
        emit ("vecfindi_" ^ si, fiv);
        emit ("law_findi_manual_" ^ si, B (fiv = maniv));
        emit ("vecexists_" ^ si, B exv);
        emit ("law_exists_isfind_" ^ si, B (exv = (Option.isSome (Vector.find p v))));
        emit ("vecall_inrange_" ^ si, B allv);
        emit ("law_all_not_exists_" ^ si,
              B (Vector.all p v = not (Vector.exists (fn x => not (p x)) v)));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION F: concat + functional update + appi                          *)
(* ===================================================================== *)
val nCat = 120;

fun runCat () =
  let
    val accRef = ref ([] : int list)   (* for appi accumulation *)
    fun loop i =
      if i >= nCat then () else
      let
        val xs = rlist ()
        val ys = rlist ()
        val zs = rlist ()
        val si = N i
        val v1 = buildFromList xs
        val v2 = buildFromList ys
        val v3 = buildFromList zs
        (* concat vs fromList of appended freeze *)
        val cat = freeze (Vector.concat [v1, v2, v3])
        val manualcat = xs @ ys @ zs
        (* functional update at random index incl out-of-range *)
        val idx = upto (MAXLEN + 2)
        val nv  = relem ()
        val upd = wrap (fn () => L (freeze (Vector.update (v1, idx, nv))))
        (* manual: same as xs but element idx replaced (when in range) *)
        val manupd = wrap (fn () =>
              if idx < 0 orelse idx >= List.length xs then raise Subscript
              else L (List.tabulate (List.length xs,
                        fn k => if k = idx then nv else List.nth (xs, k))))
        (* appi: accumulate (i*100 + x) into accRef, then compare to manual *)
        val () = accRef := []
        val () = Vector.appi (fn (k, x) => accRef := (k * 100 + x) :: !accRef) v1
        val appiGot = List.rev (!accRef)
        val appiWant = List.tabulate (List.length xs, fn k => k * 100 + List.nth (xs, k))
        (* app: accumulate x into accRef, compare to xs *)
        val () = accRef := []
        val () = Vector.app (fn x => accRef := x :: !accRef) v1
        val appGot = List.rev (!accRef)
      in
        emit ("veccat_" ^ si, L cat);
        emit ("law_cat_manual_" ^ si, B (cat = manualcat));
        emit ("law_cat_len_" ^ si,
              B (List.length cat = List.length xs + List.length ys + List.length zs));
        emit ("vecupd_" ^ si ^ "_" ^ N idx, upd);
        emit ("law_upd_manual_" ^ si, B (upd = manupd));
        emit ("vecappi_" ^ si, B (appiGot = appiWant));
        emit ("vecapp_" ^ si, B (appGot = xs));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION G: VectorSlice — slice / subslice / sub / length / folds /    *)
(*            map / app / appi / vector / concat / getItem / isEmpty     *)
(* ===================================================================== *)
val nSlice = 200;

fun runSlice () =
  let
    val accRef = ref ([] : int list)
    fun loop i =
      if i >= nSlice then () else
      let
        val xs = rlist ()
        val si = N i
        val v = buildFromList xs
        val len = List.length xs
        (* random slice start/len, sometimes out-of-range => SUB *)
        val start = upto (MAXLEN + 2)
        val haveLen = bit () = 0
        val slen = upto (MAXLEN + 2)
        val sl = wrap (fn () =>
              let val s' = if haveLen then VectorSlice.slice (v, start, SOME slen)
                                      else VectorSlice.slice (v, start, NONE)
              in "OK" end)
        (* the expected sub-range of xs (the canonical comparison) when the slice
           is valid; we compute it the same way SML would: drop start, take slen
           (or all the rest). When invalid (start/slen out of bounds), the SML
           slice raises Subscript. *)
        fun expectedRange () =
          let
            (* validity per the Basis: 0 <= start <= len, and if SOME n then
               0 <= n <= len-start. *)
            val _ = if start < 0 orelse start > len then raise Subscript else ()
            val take_n = if haveLen
                         then (if slen < 0 orelse slen > len - start then raise Subscript
                               else slen)
                         else len - start
          in List.take (List.drop (xs, start), take_n) end
        val expRange = wrap (fn () => L (expectedRange ()))
        (* build the actual slice (may raise) and freeze it via foldr *)
        fun mkSlice () = if haveLen then VectorSlice.slice (v, start, SOME slen)
                                    else VectorSlice.slice (v, start, NONE)
        val actFreeze = wrap (fn () => L (VectorSlice.foldr (op ::) [] (mkSlice ())))
        (* slice length *)
        val slLen = wrap (fn () => N (VectorSlice.length (mkSlice ())))
        (* VectorSlice.vector of the slice = the sub-range as a vector *)
        val slVec = wrap (fn () => L (freeze (VectorSlice.vector (mkSlice ()))))
        (* folds over the slice: sum + reversed *)
        val slSumL = wrap (fn () => N (VectorSlice.foldl (op +) 0 (mkSlice ())))
        val slSumR = wrap (fn () => N (VectorSlice.foldr (op +) 0 (mkSlice ())))
        (* slice sub at a random in-window index incl out-of-range *)
        val subIdx = upto (MAXLEN + 2)
        val slSub = wrap (fn () => N (VectorSlice.sub (mkSlice (), subIdx)))
        (* expected slice-sub = nth of the expected range *)
        val slSubExp = wrap (fn () => N (List.nth (expectedRange (), subIdx)))
        (* VectorSlice.map (+1) over the slice — returns a vector *)
        val slMap = wrap (fn () => L (freeze
                                        (VectorSlice.map (fn x => x + 1) (mkSlice ()))))
        val slMapExp = wrap (fn () => L (List.map (fn x => x + 1) (expectedRange ())))
        (* isEmpty *)
        val slEmpty = wrap (fn () => B (VectorSlice.isEmpty (mkSlice ())))
        (* getItem reconstruction of the whole slice *)
        val slGet = wrap (fn () =>
              let fun rebuild sl =
                    case VectorSlice.getItem sl of
                        NONE => []
                      | SOME (x, rest) => x :: rebuild rest
              in L (rebuild (mkSlice ())) end)
        (* appi over the slice: index is slice-relative *)
        val () = accRef := []
        val slAppi = wrap (fn () =>
              (VectorSlice.appi (fn (k, x) => accRef := (k * 100 + x) :: !accRef) (mkSlice ());
               B (List.rev (!accRef)
                  = List.tabulate (List.length (expectedRange ()),
                       fn k => k * 100 + List.nth (expectedRange (), k)))))
        (* base: (underlying, start, len) *)
        val slBase = wrap (fn () =>
              let val (bv, bi, bn) = VectorSlice.base (mkSlice ())
              in N (Vector.length bv) ^ ":" ^ N bi ^ ":" ^ N bn end)
        (* findi over slice: slice-relative index *)
        val slFindi = wrap (fn () =>
              case VectorSlice.findi (fn (_, x) => x = relem ()) (mkSlice ()) of
                  SOME (k, y) => N k ^ ":" ^ N y | NONE => "NONE")
      in
        emit ("vsfreeze_" ^ si, actFreeze);
        emit ("law_vs_eq_range_" ^ si, B (actFreeze = expRange));
        emit ("vslen_" ^ si, slLen);
        emit ("law_vslen_eq_rangelen_" ^ si,
              B (slLen = wrap (fn () => N (List.length (expectedRange ())))));
        emit ("vsvector_" ^ si, slVec);
        emit ("law_vsvector_eq_range_" ^ si, B (slVec = expRange));
        emit ("vssuml_" ^ si, slSumL);
        emit ("law_vssum_lr_" ^ si, B (slSumL = slSumR));
        emit ("vssub_" ^ si ^ "_" ^ N subIdx, slSub);
        emit ("law_vssub_eq_nth_" ^ si, B (slSub = slSubExp));
        emit ("vsmap_" ^ si, slMap);
        emit ("law_vsmap_eq_" ^ si, B (slMap = slMapExp));
        emit ("vsempty_" ^ si, slEmpty);
        emit ("vsget_" ^ si, slGet);
        emit ("law_vsget_eq_range_" ^ si, B (slGet = expRange));
        emit ("vsappi_" ^ si, slAppi);
        emit ("vsbase_" ^ si, slBase);
        emit ("vsfindi_" ^ si, slFindi);
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION H: VectorSlice.subslice + VectorSlice.concat + full           *)
(* ===================================================================== *)
val nSub = 120;

fun runSubslice () =
  let
    fun loop i =
      if i >= nSub then () else
      let
        val xs = rlist ()
        val ys = rlist ()
        val si = N i
        val v = buildFromList xs
        val w = buildFromList ys
        val len = List.length xs
        (* full slice round-trips to xs *)
        val fullF = L (VectorSlice.foldr (op ::) [] (VectorSlice.full v))
        (* subslice of full(v): start s2, length sl2, sometimes oob => SUB *)
        val s2 = upto (MAXLEN + 2)
        val sl2 = upto (MAXLEN + 2)
        fun mkSub () = VectorSlice.subslice (VectorSlice.full v, s2, SOME sl2)
        val subF = wrap (fn () => L (VectorSlice.foldr (op ::) [] (mkSub ())))
        fun expSub () =
          let val _ = if s2 < 0 orelse s2 > len then raise Subscript else ()
              val _ = if sl2 < 0 orelse sl2 > len - s2 then raise Subscript else ()
          in List.take (List.drop (xs, s2), sl2) end
        val subExp = wrap (fn () => L (expSub ()))
        (* concat two full slices = xs @ ys *)
        val catF = L (VectorSlice.foldr (op ::) []
                       (VectorSlice.full (VectorSlice.concat
                         [VectorSlice.full v, VectorSlice.full w])))
        (* concat directly returns a vector; freeze it *)
        val catVec = L (freeze (VectorSlice.concat [VectorSlice.full v, VectorSlice.full w]))
      in
        emit ("vsfull_" ^ si, fullF);
        emit ("law_vsfull_eq_" ^ si, B (fullF = L xs));
        emit ("vssubslice_" ^ si, subF);
        emit ("law_vssubslice_eq_" ^ si, B (subF = subExp));
        emit ("vsconcat_" ^ si, catVec);
        emit ("law_vsconcat_eq_" ^ si, B (catVec = L (xs @ ys)));
        emit ("vsconcat_full_eq_" ^ si, B (catF = catVec));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION I: Vector <-> Array <-> List bridges                          *)
(*   NOTE: Array.fromVector is NOT in this (stage-0) basis on EITHER side,*)
(*   so we bridge vector->array via tabulate over Vector.sub.            *)
(* ===================================================================== *)
val nBridge = 120;

(* array built from a vector's contents (portable substitute for fromVector) *)
fun arrOfVec v = Array.tabulate (Vector.length v, fn i => Vector.sub (v, i));

fun runBridge () =
  let
    fun loop i =
      if i >= nBridge then () else
      let
        val xs = rlist ()
        val si = N i
        val v = buildFromList xs
        (* array(of vec) then Array.vector round-trips contents *)
        val rt1 = freeze (Array.vector (arrOfVec v))
        (* Array.vector(Array.fromList xs) = v contents *)
        val rt2 = freeze (Array.vector (Array.fromList xs))
        (* Vector.fromList (Array.foldr (::) [] (array of v)) round-trips *)
        val rt3 = freeze (Vector.fromList
                    (Array.foldr (op ::) [] (arrOfVec v)))
        (* Array.foldl/foldr/modify cross-checks on the bridged array *)
        val a = arrOfVec v
        val arrSum = Array.foldl (op +) 0 a
        val () = Array.modify (fn x => x + 1) a
        val rt4 = freeze (Array.vector a)   (* each element +1 *)
        val want4 = List.map (fn x => x + 1) xs
      in
        emit ("bridge_arr_rt_" ^ si, L rt1);
        emit ("law_bridge_arr_rt_" ^ si, B (rt1 = xs));
        emit ("law_bridge_arrlist_" ^ si, B (rt2 = xs));
        emit ("law_bridge_full_" ^ si, B (rt3 = xs));
        emit ("law_bridge_arrsum_" ^ si, B (arrSum = List.foldl (op +) 0 xs));
        emit ("law_bridge_modify_" ^ si, B (rt4 = want4));
        loop (i + 1)
      end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION J: fixed corner cases (empty / singleton / boundary indices)  *)
(* ===================================================================== *)
fun runCorners () =
  let
    val e  = Vector.fromList ([] : int list)
    val s1 = Vector.fromList [42]
    val big = Vector.fromList [0,1,2,3,4,5,6,7,8,9]
  in
    emit ("corner_empty_len", N (Vector.length e));
    emit ("corner_empty_freeze", L (freeze e));
    emit ("corner_empty_sub0", wrap (fn () => N (Vector.sub (e, 0))));
    emit ("corner_empty_foldl", N (Vector.foldl (op +) 0 e));
    emit ("corner_empty_map", L (freeze (Vector.map (fn x => x + 1) e)));
    emit ("corner_empty_find", (case Vector.find (fn _ => true) e of SOME _ => "SOME" | NONE => "NONE"));
    emit ("corner_empty_exists", B (Vector.exists (fn _ => true) e));
    emit ("corner_empty_all", B (Vector.all (fn _ => false) e));
    emit ("corner_single_sub0", N (Vector.sub (s1, 0)));
    emit ("corner_single_sub1", wrap (fn () => N (Vector.sub (s1, 1))));
    emit ("corner_single_subneg", wrap (fn () => N (Vector.sub (s1, ~1))));
    emit ("corner_single_upd0", L (freeze (Vector.update (s1, 0, 99))));
    emit ("corner_single_upd_orig", N (Vector.sub (s1, 0)));   (* immutable: unchanged *)
    emit ("corner_tab_neg", wrap (fn () => N (Vector.length (Vector.tabulate (~1, fn k => k)))));
    emit ("corner_tab_zero", N (Vector.length (Vector.tabulate (0, fn k => k))));
    emit ("corner_sub_last", N (Vector.sub (big, 9)));
    emit ("corner_sub_len", wrap (fn () => N (Vector.sub (big, 10))));
    emit ("corner_sub_neg", wrap (fn () => N (Vector.sub (big, ~1))));
    emit ("corner_update_last", L (freeze (Vector.update (big, 9, 999))));
    emit ("corner_update_len", wrap (fn () => N (Vector.length (Vector.update (big, 10, 0)))));
    emit ("corner_concat_empties", N (Vector.length (Vector.concat [e, e, e])));
    emit ("corner_concat_mix", L (freeze (Vector.concat [e, s1, e, big, e])));
    (* slice corners *)
    emit ("corner_vs_full_empty", N (VectorSlice.length (VectorSlice.full e)));
    emit ("corner_vs_slice_atend", N (VectorSlice.length (VectorSlice.slice (big, 10, SOME 0))));
    emit ("corner_vs_slice_atend_bad", wrap (fn () => N (VectorSlice.length (VectorSlice.slice (big, 11, NONE)))));
    emit ("corner_vs_slice_full_len", N (VectorSlice.length (VectorSlice.slice (big, 0, NONE))));
    emit ("corner_vs_slice_overlen", wrap (fn () => N (VectorSlice.length (VectorSlice.slice (big, 5, SOME 6)))));
    emit ("corner_vs_isempty_atend", B (VectorSlice.isEmpty (VectorSlice.slice (big, 10, SOME 0))));
    emit ("corner_vs_getitem_empty", (case VectorSlice.getItem (VectorSlice.slice (big, 0, SOME 0)) of SOME _ => "SOME" | NONE => "NONE"));
    emit ("corner_vs_subslice_empty", N (VectorSlice.length (VectorSlice.subslice (VectorSlice.full big, 3, SOME 0))));
    emit ("corner_vs_concat_empty", N (Vector.length (VectorSlice.concat ([] : int VectorSlice.slice list))));
    (* char vector surface (non-int element type) *)
    emit ("corner_charvec_sub", Char.toString (Vector.sub (Vector.fromList [#"x", #"y", #"z"], 2)));
    emit ("corner_charvec_freeze",
          String.implode (Vector.foldr (op ::) [] (Vector.fromList [#"h", #"i"])))
  end;

(* ===================================================================== *)
(* run all sections in a FIXED order (deterministic LCG consumption)     *)
(* ===================================================================== *)
val () = runBuild ();
val () = runTab ();
val () = runMap ();
val () = runFold ();
val () = runFind ();
val () = runCat ();
val () = runSlice ();
val () = runSubslice ();
val () = runBridge ();
val () = runCorners ();
