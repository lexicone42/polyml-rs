(* diff-corpus GENERATIVE-DIFFERENTIAL FUZZ DRIVER: fuzz_list  (domain = List / ListPair)  (2026-06-17)
   ====================================================================================
   The STRUCTURE complement to the arithmetic fuzz (fuzz_{int,word,real,intinf,convert}.sml).
   A DETERMINISTIC LCG (seed = 0w1) drives operand generation; the SAME pure-SML code runs
   IDENTICALLY on upstream PolyML and our `poly run`, so both consume the EXACT same random
   sequence and any @@<label>=<value> divergence is a faithfulness bug in OUR port.

   Domain: the List structure (rev, @, concat, take, drop, nth, tabulate, fold{l,r}, map,
   mapPartial, filter, partition, find, exists, all, app, collate, getItem, last, length,
   revAppend, concatWith-via-implode) plus ListPair (zip/zipEq, unzip, map/mapEq, app/appEq,
   fold{l,r}{,Eq}, all/allEq, exists) on equal AND unequal lengths.

   THE KEY BUG-HUNTING PRINCIPLE: test MULTIPLE SURFACES of each op — a length computed via
   List.length vs a fold vs explicit recursion hits different code paths; an append via @ vs
   List.concat vs foldr op:: vs List.revAppend(rev a, b) hits different paths. Divergences
   between surfaces on the SAME side are caught as algebraic-law @@ lines; divergences between
   sides are caught by the harness diff.

   DETERMINISM: results stringified totally; anything that can raise is wrapped so an exception
   becomes a COMPARABLE TOKEN (SUB/SIZE/EMPTY/OPT/EXN) — both sides raising the same class AGREE.
   Section order is FIXED. Lists are int lists (elements small so dup/equality cases hit). *)

(* ===== SHARED FUZZ HEADER ===== *)
(* ---- ref-force helper: defeats inline specialization (forces RTS/boxed path) ---- *)
fun I x = let val r = ref x in !r end;

(* ---- the LCG (Knuth/MMIX constants); default-int config => `word` is 63-bit ---- *)
val s = ref (0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
fun nxt () = Word.toInt (Word.>> (step (), 0w11));
fun bit () = Word.toInt (Word.andb (step (), 0w1));
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
           | ListPair.UnequalLengths => "UNEQ"
           | _         => "EXN";

fun B b = Bool.toString b;
fun N n = Int.toString n;
(* ===== END SHARED HEADER ===== *)

(* ---- list-specific helpers ---- *)
(* canonical rendering of an int list: comma-joined inside brackets (TOTAL) *)
fun L xs = "[" ^ String.concatWith "," (List.map N xs) ^ "]";
(* render an int*int pair list *)
fun LP xs = "[" ^ String.concatWith "," (List.map (fn (a,b) => "(" ^ N a ^ "," ^ N b ^ ")") xs) ^ "]";
(* render an ordering *)
fun ORD c = (case c of LESS => "LT" | EQUAL => "EQ" | GREATER => "GT");
(* render an int option *)
fun OPT NONE = "NONE" | OPT (SOME v) = "SOME " ^ N v;

(* random list of length 0..maxlen with elements in 0..elrange-1 (small => dups) *)
fun rlist (maxlen, elrange) =
  List.tabulate (upto (maxlen + 1), fn _ => upto elrange);

(* a small predicate on ints chosen at random, returned as a function.
   Deterministic: the choice draws from the LCG. *)
fun rpred () =
  let val k = upto 4
      val m = 1 + upto 5
  in case k of
        0 => (fn x => x mod 2 = 0)
      | 1 => (fn x => x mod m = 0)
      | 2 => (fn x => x >= m)
      | _ => (fn x => x < m)
  end;

(* a small unary int->int function chosen at random *)
fun rfun () =
  let val k = upto 4
      val m = 1 + upto 7
  in case k of
        0 => (fn x => x + m)
      | 1 => (fn x => x * 2)
      | 2 => (fn x => x - m)
      | _ => (fn x => x * m + 1)
  end;

(* ===================================================================== *)
(* SECTION A:  length / rev — multiple surfaces + laws                     *)
(* ===================================================================== *)
val nA = 120;
fun runA () =
  let
    fun loop i =
      if i >= nA then ()
      else
        let
          val xs = rlist (12, 6)
          val si = N i
          (* length via three surfaces *)
          val lenL = List.length xs
          val lenF = List.foldl (fn (_, n) => n + 1) 0 xs
          fun reclen [] = 0 | reclen (_ :: t) = 1 + reclen t
          val lenR = reclen xs
          (* rev via two surfaces *)
          val r1 = List.rev xs
          val r2 = List.foldl (fn (x, a) => x :: a) [] xs
        in
          emit ("a_len_" ^ si, N lenL);
          emit ("a_lenfold_" ^ si, N lenF);
          emit ("a_lenrec_" ^ si, N lenR);
          emit ("a_rev_" ^ si, L r1);
          emit ("a_revfold_" ^ si, L r2);
          (* LAWS (ride along free; same on both sides unless our port differs) *)
          emit ("law_len_3surf_" ^ si, B (lenL = lenF andalso lenF = lenR));
          emit ("law_rev_2surf_" ^ si, B (r1 = r2));
          emit ("law_rev_rev_" ^ si, B (List.rev r1 = xs));
          emit ("law_rev_len_" ^ si, B (List.length r1 = lenL));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION B:  @ (append) — THREE surfaces + associativity + length law    *)
(* ===================================================================== *)
val nB = 120;
fun runB () =
  let
    fun loop i =
      if i >= nB then ()
      else
        let
          val a = rlist (8, 6)
          val b = rlist (8, 6)
          val c = rlist (8, 6)
          val si = N i
          (* append surfaces *)
          val ap1 = a @ b
          val ap2 = List.concat [a, b]
          val ap3 = List.foldr (op ::) b a
          val ap4 = List.revAppend (List.rev a, b)
        in
          emit ("b_app_" ^ si, L ap1);
          emit ("b_concat_" ^ si, L ap2);
          emit ("b_foldrcons_" ^ si, L ap3);
          emit ("b_revapp_" ^ si, L ap4);
          emit ("law_app_4surf_" ^ si,
                B (ap1 = ap2 andalso ap2 = ap3 andalso ap3 = ap4));
          emit ("law_app_assoc_" ^ si, B ((a @ b) @ c = a @ (b @ c)));
          emit ("law_app_len_" ^ si,
                B (List.length (a @ b) = List.length a + List.length b));
          emit ("law_app_nil_r_" ^ si, B (a @ [] = a));
          emit ("law_app_nil_l_" ^ si, B ([] @ a = a));
          (* rev distributes over @ (anti-homomorphism) *)
          emit ("law_rev_app_" ^ si, B (List.rev (a @ b) = List.rev b @ List.rev a));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION C:  concat (list-of-lists) — vs nested @ fold                   *)
(* ===================================================================== *)
val nC = 100;
fun runC () =
  let
    fun loop i =
      if i >= nC then ()
      else
        let
          val k = upto 5  (* number of sublists 0..4 *)
          val lol = List.tabulate (k, fn _ => rlist (5, 6))
          val si = N i
          val ccat = List.concat lol
          val cfold = List.foldr (op @) [] lol
          val totlen = List.foldl (fn (l, n) => n + List.length l) 0 lol
        in
          emit ("c_concat_" ^ si, L ccat);
          emit ("c_concatfold_" ^ si, L cfold);
          emit ("law_concat_2surf_" ^ si, B (ccat = cfold));
          emit ("law_concat_len_" ^ si, B (List.length ccat = totlen));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION D:  nth / last / hd / tl — value + boundary (SUB/EMPTY)         *)
(* ===================================================================== *)
val nD = 130;
fun runD () =
  let
    fun loop i =
      if i >= nD then ()
      else
        let
          val xs = rlist (10, 8)
          val len = List.length xs
          (* index in -1 .. len+1 to straddle the boundary *)
          val idx = upto (len + 3) - 1
          val si = N i
        in
          emit ("d_nth_" ^ si, wrap (fn () => N (List.nth (xs, idx))));
          (* cross-surface: nth via explode/take-drop equivalent — drop idx then hd *)
          emit ("d_nth_alt_" ^ si,
                wrap (fn () => N (List.hd (List.drop (xs, idx)))));
          emit ("d_last_" ^ si, wrap (fn () => N (List.last xs)));
          emit ("d_hd_" ^ si, wrap (fn () => N (List.hd xs)));
          emit ("d_tllen_" ^ si, wrap (fn () => N (List.length (List.tl xs))));
          emit ("d_idx_" ^ si, N idx);
          (* LAW: last xs = nth(xs, len-1) when nonempty *)
          emit ("law_last_nth_" ^ si,
                wrap (fn () =>
                  if len = 0 then "EMPTY-OK"
                  else B (List.last xs = List.nth (xs, len - 1))));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION E:  take / drop — boundary (SUB) + take@drop=xs law             *)
(* ===================================================================== *)
val nE = 130;
fun runE () =
  let
    fun loop i =
      if i >= nE then ()
      else
        let
          val xs = rlist (10, 8)
          val len = List.length xs
          val k = upto (len + 3)  (* 0 .. len+2 ; k>len => SUB *)
          val si = N i
          val tk = wrap (fn () => L (List.take (xs, k)))
          val dr = wrap (fn () => L (List.drop (xs, k)))
        in
          emit ("e_take_" ^ si, tk);
          emit ("e_drop_" ^ si, dr);
          emit ("e_k_" ^ si, N k);
          (* LAW: take(xs,k) @ drop(xs,k) = xs  (only when k<=len, else both SUB) *)
          emit ("law_takedrop_" ^ si,
                wrap (fn () => B (List.take (xs, k) @ List.drop (xs, k) = xs)));
          (* LAW: length(take) + length(drop) = len  (when k<=len) *)
          emit ("law_takedrop_len_" ^ si,
                wrap (fn () =>
                  N (List.length (List.take (xs, k)) + List.length (List.drop (xs, k)))));
          (* negative k => Subscript *)
          emit ("e_take_neg_" ^ si, wrap (fn () => L (List.take (xs, ~1))));
          emit ("e_drop_neg_" ^ si, wrap (fn () => L (List.drop (xs, ~1))));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION F:  tabulate — value + negative (SIZE) + cross-surface          *)
(* ===================================================================== *)
val nF = 80;
fun runF () =
  let
    fun loop i =
      if i >= nF then ()
      else
        let
          val n = upto 12
          val f = rfun ()
          val si = N i
          val t1 = wrap (fn () => L (List.tabulate (n, f)))
          (* explicit build of the same: rev of a foldl over 0..n-1 *)
          fun build j acc = if j >= n then List.rev acc else build (j + 1) (f j :: acc)
          val t2 = wrap (fn () => L (build 0 []))
        in
          emit ("f_tab_" ^ si, t1);
          emit ("f_tabalt_" ^ si, t2);
          emit ("law_tab_2surf_" ^ si, B (t1 = t2));
          emit ("f_tabneg_" ^ si, wrap (fn () => L (List.tabulate (~1, f))));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION G:  map / mapPartial — surfaces + length + composition laws     *)
(* ===================================================================== *)
val nG = 110;
fun runG () =
  let
    fun loop i =
      if i >= nG then ()
      else
        let
          val xs = rlist (12, 8)
          val f = rfun ()
          val g = rfun ()
          val p = rpred ()
          val si = N i
          val m1 = List.map f xs
          val m2 = List.foldr (fn (x, a) => f x :: a) [] xs
          (* mapPartial vs (map f o filter p) *)
          val mp1 = List.mapPartial (fn x => if p x then SOME (f x) else NONE) xs
          val mp2 = List.map f (List.filter p xs)
        in
          emit ("g_map_" ^ si, L m1);
          emit ("g_mapfold_" ^ si, L m2);
          emit ("law_map_2surf_" ^ si, B (m1 = m2));
          emit ("law_map_len_" ^ si, B (List.length m1 = List.length xs));
          (* composition: map g (map f xs) = map (g o f) xs *)
          emit ("law_map_compose_" ^ si,
                B (List.map g (List.map f xs) = List.map (g o f) xs));
          emit ("g_mapPartial_" ^ si, L mp1);
          emit ("law_mapPartial_eq_" ^ si, B (mp1 = mp2));
          (* mapPartial all-NONE => [] *)
          emit ("law_mapPartial_none_" ^ si,
                N (List.length (List.mapPartial (fn _ => NONE) xs)));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION H:  filter / partition — surfaces + complement law              *)
(* ===================================================================== *)
val nH = 110;
fun runH () =
  let
    fun loop i =
      if i >= nH then ()
      else
        let
          val xs = rlist (14, 6)
          val p = rpred ()
          val si = N i
          val fl = List.filter p xs
          val (pt, pf) = List.partition p xs
        in
          emit ("h_filter_" ^ si, L fl);
          emit ("h_part_t_" ^ si, L pt);
          emit ("h_part_f_" ^ si, L pf);
          (* LAW: filter p = #1 (partition p) *)
          emit ("law_filter_part_" ^ si, B (fl = pt));
          (* LAW: #2 (partition p) = filter (not o p) *)
          emit ("law_part_complement_" ^ si,
                B (pf = List.filter (fn x => not (p x)) xs));
          (* LAW: |filter p| + |filter ~p| = |xs| *)
          emit ("law_part_len_" ^ si,
                B (List.length pt + List.length pf = List.length xs));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION I:  foldl / foldr — order-sensitive + identity laws             *)
(* ===================================================================== *)
val nI = 110;
fun runI () =
  let
    fun loop i =
      if i >= nI then ()
      else
        let
          val xs = rlist (12, 9)
          val si = N i
          (* commutative op: foldl and foldr agree *)
          val sl = List.foldl (op +) 0 xs
          val sr = List.foldr (op +) 0 xs
          (* non-commutative string accumulation: order matters *)
          val ol = List.foldl (fn (x, a) => a ^ N x ^ ".") "" xs
          val orr = List.foldr (fn (x, a) => a ^ N x ^ ".") "" xs
          (* foldl (::) [] = rev ; foldr (::) [] = identity *)
          val fl_cons = List.foldl (op ::) [] xs
          val fr_cons = List.foldr (op ::) [] xs
        in
          emit ("i_foldl_sum_" ^ si, N sl);
          emit ("i_foldr_sum_" ^ si, N sr);
          emit ("i_foldl_ord_" ^ si, ol);
          emit ("i_foldr_ord_" ^ si, orr);
          emit ("law_fold_sum_eq_" ^ si, B (sl = sr));
          emit ("law_foldl_cons_rev_" ^ si, B (fl_cons = List.rev xs));
          emit ("law_foldr_cons_id_" ^ si, B (fr_cons = xs));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION J:  find / exists / all — cross-relations                       *)
(* ===================================================================== *)
val nJ = 110;
fun runJ () =
  let
    fun loop i =
      if i >= nJ then ()
      else
        let
          val xs = rlist (12, 8)
          val p = rpred ()
          val si = N i
          val fnd = List.find p xs
          val ex = List.exists p xs
          val al = List.all p xs
        in
          emit ("j_find_" ^ si, OPT fnd);
          emit ("j_exists_" ^ si, B ex);
          emit ("j_all_" ^ si, B al);
          (* LAW: exists p = isSome (find p) *)
          emit ("law_exists_find_" ^ si, B (ex = Option.isSome fnd));
          (* LAW: all p = not (exists (not o p)) *)
          emit ("law_all_exists_" ^ si,
                B (al = not (List.exists (fn x => not (p x)) xs)));
          (* LAW: if find p = SOME v then p v *)
          emit ("law_find_sat_" ^ si,
                (case fnd of NONE => "NONE-OK" | SOME v => B (p v)));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION K:  app / getItem — reconstruction surfaces                     *)
(* ===================================================================== *)
val nK = 90;
fun runK () =
  let
    fun loop i =
      if i >= nK then ()
      else
        let
          val xs = rlist (12, 9)
          val si = N i
          (* app accumulating into a ref list (reversed), compare to rev xs *)
          val r = ref ([] : int list)
          val () = List.app (fn x => r := x :: !r) xs
          val appAcc = !r
          (* getItem repeatedly to reconstruct the list *)
          fun rebuild acc l =
            case List.getItem l of
                NONE => List.rev acc
              | SOME (h, t) => rebuild (h :: acc) t
          val rebuilt = rebuild [] xs
        in
          emit ("k_app_acc_" ^ si, L appAcc);
          emit ("k_getitem_rebuild_" ^ si, L rebuilt);
          emit ("law_app_rev_" ^ si, B (appAcc = List.rev xs));
          emit ("law_getitem_id_" ^ si, B (rebuilt = xs));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION L:  collate — vs manual lexicographic compare                   *)
(* ===================================================================== *)
val nL = 110;
fun runL () =
  let
    (* reference lexicographic compare for int lists *)
    fun lex ([], []) = EQUAL
      | lex ([], _ :: _) = LESS
      | lex (_ :: _, []) = GREATER
      | lex (x :: xs, y :: ys) =
          (case Int.compare (x, y) of EQUAL => lex (xs, ys) | c => c)
    fun loop i =
      if i >= nL then ()
      else
        let
          val a = rlist (8, 4)  (* small element range => more EQ-prefix cases *)
          val b = rlist (8, 4)
          val si = N i
          val c1 = List.collate Int.compare (a, b)
          val c2 = lex (a, b)
        in
          emit ("l_collate_" ^ si, ORD c1);
          emit ("l_lexref_" ^ si, ORD c2);
          emit ("law_collate_lex_" ^ si, B (c1 = c2));
          (* collate is antisymmetric: collate(a,b) = LESS <=> collate(b,a) = GREATER *)
          emit ("law_collate_antisym_" ^ si,
                B ((c1 = LESS) = (List.collate Int.compare (b, a) = GREATER)));
          (* collate(a,a) = EQUAL *)
          emit ("law_collate_refl_" ^ si, B (List.collate Int.compare (a, a) = EQUAL));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION M:  ListPair zip/unzip — round-trip + truncation + Eq variants  *)
(* ===================================================================== *)
val nM = 120;
fun runM () =
  let
    fun loop i =
      if i >= nM then ()
      else
        let
          val a = rlist (10, 9)
          val b = rlist (10, 9)
          val si = N i
          val z = ListPair.zip (a, b)
          val zlen = List.length z
          val (ua, ub) = ListPair.unzip z
          val minlen = Int.min (List.length a, List.length b)
        in
          emit ("m_zip_" ^ si, LP z);
          emit ("m_ziplen_" ^ si, N zlen);
          (* LAW: length(zip) = min(len a, len b) *)
          emit ("law_zip_minlen_" ^ si, B (zlen = minlen));
          (* LAW: unzip(zip(a,b)) = (take(a,min), take(b,min)) *)
          emit ("law_unzip_zip_a_" ^ si, B (ua = List.take (a, minlen)));
          emit ("law_unzip_zip_b_" ^ si, B (ub = List.take (b, minlen)));
          (* zipEq raises UnequalLengths on mismatch (wrap) *)
          emit ("m_zipEq_" ^ si, wrap (fn () => N (List.length (ListPair.zipEq (a, b)))));
          (* unzip then re-zip is idempotent on the truncated form *)
          emit ("law_zip_unzip_zip_" ^ si,
                B (ListPair.zip (ua, ub) = z));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION N:  ListPair map / app / fold / all / exists (+ Eq variants)    *)
(* ===================================================================== *)
val nN = 120;
fun runN () =
  let
    fun loop i =
      if i >= nN then ()
      else
        let
          val a = rlist (10, 9)
          val b = rlist (10, 9)
          val si = N i
          val minlen = Int.min (List.length a, List.length b)
          (* map: ListPair.map vs map over the zip *)
          val pm1 = ListPair.map (fn (x, y) => x + y) (a, b)
          val pm2 = List.map (fn (x, y) => x + y) (ListPair.zip (a, b))
          (* foldl/foldr *)
          val pfl = ListPair.foldl (fn (x, y, s) => s + x - y) 0 (a, b)
          val pfr = ListPair.foldr (fn (x, y, s) => s + x - y) 0 (a, b)
          (* app accumulating *)
          val r = ref 0
          val () = ListPair.app (fn (x, y) => r := !r + x * y) (a, b)
          (* all / exists *)
          val pall = ListPair.all (fn (x, y) => x <= y) (a, b)
          val pex = ListPair.exists (fn (x, y) => x = y) (a, b)
        in
          emit ("n_map_" ^ si, L pm1);
          emit ("law_pmap_zip_" ^ si, B (pm1 = pm2));
          emit ("law_pmap_len_" ^ si, B (List.length pm1 = minlen));
          emit ("n_foldl_" ^ si, N pfl);
          emit ("n_foldr_" ^ si, N pfr);
          emit ("n_app_" ^ si, N (!r));
          emit ("n_all_" ^ si, B pall);
          emit ("n_exists_" ^ si, B pex);
          (* Eq variants: raise UnequalLengths unless len a = len b (wrap) *)
          emit ("n_mapEq_" ^ si,
                wrap (fn () => L (ListPair.mapEq (fn (x, y) => x + y) (a, b))));
          emit ("n_foldlEq_" ^ si,
                wrap (fn () => N (ListPair.foldlEq (fn (x, y, s) => s + x + y) 0 (a, b))));
          emit ("n_allEq_" ^ si,
                wrap (fn () => B (ListPair.allEq (fn (x, y) => x <= y) (a, b))));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION O:  fixed CORNER cases (empty / singleton / boundaries)        *)
(*   named, deterministic, no LCG — pure spec corners on both sides.       *)
(* ===================================================================== *)
fun runCorners () =
  let
    val e : int list = []
    val one = [42]
    val xs = [1, 2, 3, 4, 5]
  in
    (* empty-list behaviours *)
    emit ("o_hd_empty", wrap (fn () => N (List.hd e)));
    emit ("o_tl_empty", wrap (fn () => N (List.length (List.tl e))));
    emit ("o_last_empty", wrap (fn () => N (List.last e)));
    emit ("o_nth_empty", wrap (fn () => N (List.nth (e, 0))));
    emit ("o_getitem_empty", (case List.getItem e of NONE => "NONE" | SOME _ => "SOME"));
    emit ("o_rev_empty", L (List.rev e));
    emit ("o_app_empty", L (e @ e));
    emit ("o_concat_empty", N (List.length (List.concat ([] : int list list))));
    emit ("o_take0_empty", wrap (fn () => L (List.take (e, 0))));
    emit ("o_drop0_empty", wrap (fn () => L (List.drop (e, 0))));
    emit ("o_take1_empty", wrap (fn () => L (List.take (e, 1))));
    emit ("o_filter_empty", L (List.filter (fn _ => true) e));
    emit ("o_find_empty", OPT (List.find (fn _ => true) e));
    emit ("o_exists_empty", B (List.exists (fn _ => true) e));
    emit ("o_all_empty", B (List.all (fn _ => false) e));
    (* singleton *)
    emit ("o_hd_one", wrap (fn () => N (List.hd one)));
    emit ("o_last_one", wrap (fn () => N (List.last one)));
    emit ("o_tl_one", L (List.tl one));
    emit ("o_nth_one", wrap (fn () => N (List.nth (one, 0))));
    emit ("o_nth_one_over", wrap (fn () => N (List.nth (one, 1))));
    emit ("o_rev_one", L (List.rev one));
    (* take/drop full and over on a 5-list *)
    emit ("o_take_full", wrap (fn () => L (List.take (xs, 5))));
    emit ("o_drop_full", wrap (fn () => L (List.drop (xs, 5))));
    emit ("o_take_over", wrap (fn () => L (List.take (xs, 6))));
    emit ("o_drop_over", wrap (fn () => L (List.drop (xs, 6))));
    emit ("o_take_neg", wrap (fn () => L (List.take (xs, ~1))));
    emit ("o_drop_neg", wrap (fn () => L (List.drop (xs, ~1))));
    emit ("o_nth_last", wrap (fn () => N (List.nth (xs, 4))));
    emit ("o_nth_over", wrap (fn () => N (List.nth (xs, 5))));
    emit ("o_nth_neg", wrap (fn () => N (List.nth (xs, ~1))));
    (* tabulate corners *)
    emit ("o_tab0", wrap (fn () => N (List.length (List.tabulate (0, fn i => i)))));
    emit ("o_tab_neg", wrap (fn () => N (List.length (List.tabulate (~1, fn i => i)))));
    emit ("o_tab_big", wrap (fn () => N (List.foldl (op +) 0 (List.tabulate (1000, fn i => i)))));
    (* ListPair empty / mismatch corners *)
    emit ("o_zip_emptyL", N (List.length (ListPair.zip (e, [1, 2, 3]))));
    emit ("o_zip_emptyB", N (List.length (ListPair.zip (e, e))));
    emit ("o_zipEq_emptyB", wrap (fn () => N (List.length (ListPair.zipEq (e, e)))));
    emit ("o_zipEq_mismatch", wrap (fn () => N (List.length (ListPair.zipEq ([1], e)))));
    emit ("o_unzip_empty",
          (let val (a, b) = ListPair.unzip ([] : (int * int) list)
           in N (List.length a + List.length b) end));
    (* collate corners *)
    emit ("o_collate_emptyboth", ORD (List.collate Int.compare (e, e)));
    emit ("o_collate_emptyL", ORD (List.collate Int.compare (e, [1])));
    emit ("o_collate_prefix", ORD (List.collate Int.compare ([1, 2], [1, 2, 3])))
  end;

(* run all sections (order FIXED => deterministic LCG consumption) *)
val () = runA ();
val () = runB ();
val () = runC ();
val () = runD ();
val () = runE ();
val () = runF ();
val () = runG ();
val () = runH ();
val () = runI ();
val () = runJ ();
val () = runK ();
val () = runL ();
val () = runM ();
val () = runN ();
val () = runCorners ();
