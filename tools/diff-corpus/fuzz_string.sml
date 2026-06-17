(* diff-corpus FUZZ DRIVER: fuzz_string  (domain = String/Char/Substring/CharVector)  (2026-06-17)
   ====================================================================================
   A DETERMINISTIC generative-differential fuzz over the TEXT structures — the
   structure complement to the arithmetic fuzz (fuzz_{int,word,real,intinf,convert}).
   A hand-rolled LCG PRNG (seed = 0w1, identical to fuzz_int.sml) drives operand
   generation; the SAME pure-SML code runs IDENTICALLY on upstream PolyML and on
   our `poly run`, so both consume the EXACT same random sequence and any
   @@<label>=<value> divergence is a faithfulness bug in OUR port.

   KEY BUG-HUNTING PRINCIPLE: test MULTIPLE SURFACES of the same operation,
   because a value built/accessed one way hits a different code path than another
   (this is what found the PolySubtractArbitrary negation bug). Each section
   builds/accesses the same logical value several ways and cross-checks.

   DETERMINISM:
   - Identical LCG => identical input sequence on both sides.
   - Sections run in a FIXED order; do NOT reorder/insert draws.
   - Stringify is TOTAL: every value renders deterministically; anything that can
     raise is wrapped so the exception becomes a COMPARABLE TOKEN (both sides
     raising the same class AGREE, not a divergence).
   - String CONTENT is emitted via String.toString (C-escaped) so the @@ line stays
     ASCII-printable AND our >=0x80-rejecting SOURCE lexer is never tripped; all
     high/control chars are generated at RUNTIME via Char.chr, never written raw. *)

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

(* ---- TOTAL deterministic wrapper: any raise becomes a COMPARABLE TOKEN. ---- *)
fun wrap f = (f ())
      handle Subscript => "SUB"
           | Size      => "SIZE"
           | Empty     => "EMPTY"
           | Div       => "DIV"
           | Overflow  => "OVF"
           | Chr       => "CHR"
           | Option    => "OPT"
           | _         => "EXN";

(* ---- printable, lexer-safe string emission ---- *)
fun S xs = String.toString xs;   (* string  -> C-escaped printable string *)
fun B b  = Bool.toString b;      (* bool    -> "true"/"false" *)
fun N n  = Int.toString n;       (* int     -> decimal *)
(* random char built at runtime (covers 0..255, lexer-safe) *)
fun rchar () = Char.chr (upto 256);
(* random string of length 0..maxlen of runtime-generated chars *)
fun rstr maxlen = String.implode (List.tabulate (upto (maxlen+1), fn _ => rchar ()));
(* ===== END SHARED HEADER ===== *)

(* ---- extra helpers specific to the string domain ---- *)

(* render an order relation as a stable token *)
fun ordTok LESS = "LT" | ordTok EQUAL = "EQ" | ordTok GREATER = "GT";

(* render a char as its ordinal (deterministic, lexer-safe) *)
fun cOrd c = N (Char.ord c);

(* render an int option *)
fun optI NONE = "NONE" | optI (SOME n) = "SOME(" ^ N n ^ ")";
(* render a char option as ordinal *)
fun optC NONE = "NONE" | optC (SOME c) = "SOME(" ^ cOrd c ^ ")";
(* render a string option (C-escaped) *)
fun optS NONE = "NONE" | optS (SOME x) = "SOME(" ^ S x ^ ")";

(* render a list of strings (each C-escaped), pipe-joined inside brackets *)
fun listS xs = "[" ^ String.concatWith "|" (List.map S xs) ^ "]";
(* render a list of chars as ordinals *)
fun listC xs = "[" ^ String.concatWith "," (List.map cOrd xs) ^ "]";

(* a biased string generator: sometimes restrict alphabet so equal/prefix/
   substring/collate cases actually FIRE (a pure 0..255 alphabet almost never
   collides). pick mode by a draw. *)
fun rstrBiased maxlen =
  let val mode = upto 4
      val alpha =
        case mode of
            0 => 256                 (* full byte range *)
          | 1 => 4                   (* tiny alphabet 0..3 (lots of dups) *)
          | 2 => 26                  (* a..z-ish (ords 97..122) *)
          | _ => 128                 (* ASCII *)
      val base = case mode of 2 => 97 | _ => 0
      val len = upto (maxlen + 1)
  in String.implode (List.tabulate (len, fn _ => Char.chr (base + upto alpha))) end;

(* ===================================================================== *)
(* SECTION A:  BUILD the same string 5 ways, compare for equality + bytes *)
(*   ^  vs  String.concat  vs  implode(explode a @ explode b)  vs         *)
(*   CharVector.tabulate  vs  Substring.concat                            *)
(* ===================================================================== *)

val nA = 220;

fun runA () =
  let
    fun loop i =
      if i >= nA then ()
      else
        let
          val a = rstrBiased 12
          val b = rstrBiased 12
          val si = N i
          val s1 = a ^ b
          val s2 = String.concat [a, b]
          val s3 = String.implode (String.explode a @ String.explode b)
          val s4 = CharVector.tabulate
                     (String.size a + String.size b,
                      fn k => if k < String.size a then String.sub (a, k)
                              else String.sub (b, k - String.size a))
          val s5 = Substring.concat [Substring.full a, Substring.full b]
          val allEq = (s1 = s2) andalso (s2 = s3) andalso (s3 = s4) andalso (s4 = s5)
        in
          (* the single most discriminating cross-surface check *)
          emit ("strbuild5_eq_" ^ si, B allEq);
          (* and the actual bytes from each surface (catches a path that builds a
             DIFFERENT-but-self-consistent value on one side) *)
          emit ("strbuild5_v1_" ^ si, S s1);
          emit ("strbuild5_v4_" ^ si, S s4);   (* CharVector.tabulate surface *)
          emit ("strbuild5_v5_" ^ si, S s5);   (* Substring.concat surface *)
          (* size of the concatenation, three surfaces *)
          emit ("law_size_concat_" ^ si,
                B (String.size s1 = String.size a + String.size b));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION B:  size / sub / explode-implode / CharVector.length           *)
(* ===================================================================== *)

val nB = 220;

fun runB () =
  let
    fun loop i =
      if i >= nB then ()
      else
        let
          val a = rstrBiased 14
          val si = N i
          val sz = String.size a
          val chars = String.explode a
          (* three surfaces of size *)
          val sz2 = List.length chars
          val sz3 = CharVector.length a
        in
          emit ("size3_" ^ si, B (sz = sz2 andalso sz2 = sz3));
          emit ("size_" ^ si, N sz);
          (* round-trip law *)
          emit ("law_explode_implode_" ^ si, B (String.implode chars = a));
          (* sub at a random index, possibly out of range => SUB token.
             Cross-check String.sub against List.nth(explode). *)
          let
            val idx = if sz = 0 then 0 else upto (sz + 2)
            val viaSub  = wrap (fn () => cOrd (String.sub (a, idx)))
            val viaNth  = wrap (fn () => cOrd (List.nth (chars, idx)))
            val viaCV   = wrap (fn () => cOrd (CharVector.sub (a, idx)))
          in
            emit ("subidx_" ^ si, N idx);
            emit ("sub_str_" ^ si, viaSub);
            emit ("sub_nth_" ^ si, viaNth);
            emit ("sub_cv_" ^ si, viaCV);
            (* the three sub surfaces must agree (value AND exception class) *)
            emit ("sub3_agree_" ^ si, B (viaSub = viaNth andalso viaNth = viaCV))
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION C:  compare / collate / relational operators consistency       *)
(*   String.compare (RTS byte-compare) vs  < <= = > >=  vs                 *)
(*   String.collate Char.compare (must agree, both byte-lexicographic)     *)
(* ===================================================================== *)

val nC = 240;

fun runC () =
  let
    fun loop i =
      if i >= nC then ()
      else
        let
          val a = rstrBiased 10
          val b = rstrBiased 10
          val si = N i
          val cmp = String.compare (a, b)
          val col = String.collate Char.compare (a, b)
        in
          emit ("cmp_" ^ si, ordTok cmp);
          emit ("collate_" ^ si, ordTok col);
          (* compare and collate MUST agree (both byte-lexicographic) *)
          emit ("law_cmp_collate_" ^ si, B (cmp = col));
          (* each relational operator must agree with String.compare *)
          emit ("law_lt_" ^ si, B ((cmp = LESS) = (a < b)));
          emit ("law_le_" ^ si, B (((cmp = LESS) orelse (cmp = EQUAL)) = (a <= b)));
          emit ("law_gt_" ^ si, B ((cmp = GREATER) = (a > b)));
          emit ("law_ge_" ^ si, B (((cmp = GREATER) orelse (cmp = EQUAL)) = (a >= b)));
          emit ("law_eq_" ^ si, B ((cmp = EQUAL) = (a = b)));
          (* the actual relation, for content-level diffing too *)
          emit ("rel_" ^ si,
                (if a < b then "lt" else if a = b then "eq" else "gt"));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION D:  substring / extract / Substring round-trips                *)
(*   String.substring vs Substring.string(Substring.substring) vs         *)
(*   String.extract  — three surfaces, value + SUB token                   *)
(* ===================================================================== *)

val nD = 240;

fun runD () =
  let
    fun loop i =
      if i >= nD then ()
      else
        let
          val a = rstrBiased 16
          val si = N i
          val sz = String.size a
          (* random window, deliberately sometimes out of range *)
          val st = upto (sz + 2)
          val ln = upto (sz + 2)
          val viaStr  = wrap (fn () => S (String.substring (a, st, ln)))
          val viaSS   = wrap (fn () => S (Substring.string (Substring.substring (a, st, ln))))
          val viaExt  = wrap (fn () => S (String.extract (a, st, SOME ln)))
          val viaSExt = wrap (fn () => S (Substring.string (Substring.extract (a, st, SOME ln))))
        in
          emit ("subwin_" ^ si, N st ^ "," ^ N ln);
          emit ("substr_str_" ^ si, viaStr);
          emit ("substr_ss_" ^ si, viaSS);
          emit ("substr_ext_" ^ si, viaExt);
          emit ("substr_sext_" ^ si, viaSExt);
          (* all four surfaces of the same window must agree (value + exn class) *)
          emit ("substr4_agree_" ^ si,
                B (viaStr = viaSS andalso viaSS = viaExt andalso viaExt = viaSExt));
          (* extract with NONE length: from st to end, two surfaces *)
          let
            val e1 = wrap (fn () => S (String.extract (a, st, NONE)))
            val e2 = wrap (fn () => S (Substring.string (Substring.extract (a, st, NONE))))
          in
            emit ("extract_none_" ^ si, e1);
            emit ("extract_none_agree_" ^ si, B (e1 = e2))
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION E:  str / concat / concatWith / implode of singletons          *)
(* ===================================================================== *)

val nE = 200;

fun runE () =
  let
    fun loop i =
      if i >= nE then ()
      else
        let
          val c = rchar ()
          val si = N i
          (* String.str c  vs  String.implode [c]  vs  CharVector.tabulate(1,..) *)
          val one1 = String.str c
          val one2 = String.implode [c]
          val one3 = CharVector.tabulate (1, fn _ => c)
        in
          emit ("str1_agree_" ^ si, B (one1 = one2 andalso one2 = one3));
          emit ("str1_val_" ^ si, S one1);
          (* concat of a random list of parts, two surfaces:
             String.concat parts  vs  foldr op^ "" parts *)
          let
            val nparts = upto 5
            val parts = List.tabulate (nparts, fn _ => rstrBiased 6)
            val cc1 = String.concat parts
            val cc2 = List.foldr (op ^) "" parts
            val cw1 = String.concatWith "," parts
            (* manual join with separator *)
            val cw2 = (case parts of
                          [] => ""
                        | p :: rest => List.foldl (fn (x, acc) => acc ^ "," ^ x) p rest)
          in
            emit ("concat_agree_" ^ si, B (cc1 = cc2));
            emit ("concat_val_" ^ si, S cc1);
            emit ("concatWith_agree_" ^ si, B (cw1 = cw2));
            emit ("concatWith_val_" ^ si, S cw1);
            (* law: size of concat = sum of sizes *)
            emit ("law_concat_size_" ^ si,
                  B (String.size cc1 = List.foldl (fn (x, acc) => acc + String.size x) 0 parts))
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION F:  tokens / fields  (relationship: tokens drops empties)      *)
(* ===================================================================== *)

val nF = 200;

fun runF () =
  let
    (* build a string over a tiny alphabet that INCLUDES a chosen delimiter,
       so tokens/fields actually split. *)
    fun loop i =
      if i >= nF then ()
      else
        let
          val si = N i
          (* delimiter is one of a few common separators *)
          val delim = String.sub (",.; |", upto 5)
          val isD = fn ch => ch = delim
          (* alphabet: delimiter + a couple letters, length 0..16 *)
          val len = upto 17
          val a = String.implode
                    (List.tabulate
                       (len, fn _ =>
                         case upto 4 of
                             0 => delim
                           | 1 => #"a"
                           | 2 => #"b"
                           | _ => delim))
          val toks = String.tokens isD a
          val flds = String.fields isD a
          (* tokens = fields with empties removed *)
          val fldsNonEmpty = List.filter (fn x => x <> "") flds
        in
          emit ("tokens_" ^ si, listS toks);
          emit ("fields_" ^ si, listS flds);
          emit ("tokens_count_" ^ si, N (List.length toks));
          emit ("fields_count_" ^ si, N (List.length flds));
          (* LAW: tokens = (fields with empty strings dropped) *)
          emit ("law_tokens_fields_" ^ si, B (toks = fldsNonEmpty));
          (* Substring.tokens/fields must agree with the String versions *)
          let
            val ssToks = List.map Substring.string (Substring.tokens isD (Substring.full a))
            val ssFlds = List.map Substring.string (Substring.fields isD (Substring.full a))
          in
            emit ("ss_tokens_agree_" ^ si, B (ssToks = toks));
            emit ("ss_fields_agree_" ^ si, B (ssFlds = flds))
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION G:  translate / map  (two surfaces each)                       *)
(* ===================================================================== *)

val nG = 200;

fun runG () =
  let
    fun loop i =
      if i >= nG then ()
      else
        let
          val a = rstrBiased 14
          val si = N i
          (* translate doubling each char: String.translate vs manual fold *)
          val dbl = fn ch => String.str ch ^ String.str ch
          val t1 = String.translate dbl a
          val t2 = String.concat (List.map dbl (String.explode a))
          (* translate that can DROP (return "") or EXPAND, exercising variable
             output width *)
          val vary = fn ch => if Char.ord ch mod 3 = 0 then ""
                              else if Char.ord ch mod 3 = 1 then String.str ch
                              else String.str ch ^ String.str ch
          val tv1 = String.translate vary a
          val tv2 = String.concat (List.map vary (String.explode a))
          (* map toUpper: String.map vs implode o map *)
          val m1 = String.map Char.toUpper a
          val m2 = String.implode (List.map Char.toUpper (String.explode a))
          (* map toLower *)
          val l1 = String.map Char.toLower a
          val l2 = String.implode (List.map Char.toLower (String.explode a))
        in
          emit ("translate_dbl_agree_" ^ si, B (t1 = t2));
          emit ("translate_dbl_val_" ^ si, S t1);
          emit ("law_translate_dbl_size_" ^ si, B (String.size t1 = 2 * String.size a));
          emit ("translate_vary_agree_" ^ si, B (tv1 = tv2));
          emit ("translate_vary_val_" ^ si, S tv1);
          emit ("map_up_agree_" ^ si, B (m1 = m2));
          emit ("map_up_val_" ^ si, S m1);
          emit ("map_lo_agree_" ^ si, B (l1 = l2));
          emit ("law_map_size_" ^ si, B (String.size m1 = String.size a));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION H:  isPrefix / isSuffix / isSubstring against a^b              *)
(* ===================================================================== *)

val nH = 200;

fun runH () =
  let
    fun loop i =
      if i >= nH then ()
      else
        let
          val a = rstrBiased 8
          val b = rstrBiased 8
          val si = N i
          val ab = a ^ b
        in
          (* construction guarantees: prefix a, suffix b, substring of both *)
          emit ("law_isPrefix_" ^ si, B (String.isPrefix a ab));
          emit ("law_isSuffix_" ^ si, B (String.isSuffix b ab));
          emit ("law_isSub_a_" ^ si, B (String.isSubstring a ab));
          emit ("law_isSub_b_" ^ si, B (String.isSubstring b ab));
          emit ("law_isPrefix_empty_" ^ si, B (String.isPrefix "" ab));
          emit ("law_isSub_empty_" ^ si, B (String.isSubstring "" ab));
          (* the actual values for a free random query string c, for content diffs *)
          let val c = rstrBiased 6 in
            emit ("isPrefix_" ^ si, B (String.isPrefix c ab));
            emit ("isSuffix_" ^ si, B (String.isSuffix c ab));
            emit ("isSub_" ^ si, B (String.isSubstring c ab))
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION I:  Substring surfaces — full/substring/extract, getc,         *)
(*   splitAt, size, compare vs String.compare                             *)
(* ===================================================================== *)

val nI_ = 200;

fun runI_ () =
  let
    (* reconstruct a substring char-by-char via getc *)
    fun viaGetc ss =
      case Substring.getc ss of
          NONE => []
        | SOME (c, rest) => c :: viaGetc rest
    fun loop i =
      if i >= nI_ then ()
      else
        let
          val a = rstrBiased 16
          val si = N i
          val sz = String.size a
          val ss = Substring.full a
        in
          (* Substring.size = String.size *)
          emit ("ss_size_" ^ si, B (Substring.size ss = sz));
          (* getc reconstruction = explode *)
          emit ("ss_getc_recon_" ^ si, B (viaGetc ss = String.explode a));
          (* splitAt at a random point (out of range => SUB) *)
          let
            val k = upto (sz + 2)
            val res = wrap (fn () =>
                        let val (l, r) = Substring.splitAt (ss, k)
                        in S (Substring.string l) ^ "##" ^ S (Substring.string r) end)
            (* law: when in range, l^r reconstructs a *)
            val recon = wrap (fn () =>
                        let val (l, r) = Substring.splitAt (ss, k)
                        in B (Substring.string l ^ Substring.string r = a) end)
          in
            emit ("ss_splitAt_k_" ^ si, N k);
            emit ("ss_splitAt_" ^ si, res);
            emit ("ss_splitAt_recon_" ^ si, recon)
          end;
          (* Substring.compare vs String.compare on the same two contents *)
          let
            val b = rstrBiased 10
            val ssCmp = Substring.compare (Substring.full a, Substring.full b)
            val strCmp = String.compare (a, b)
          in
            emit ("ss_compare_agree_" ^ si, B (ssCmp = strCmp))
          end;
          (* Substring.slice with optional length (out of range => SUB) *)
          let
            val st = upto (sz + 2)
            val haveLen = bit () = 0
            val res =
              if haveLen then
                wrap (fn () => S (Substring.string (Substring.slice (ss, st, SOME (upto (sz + 2))))))
              else
                wrap (fn () => S (Substring.string (Substring.slice (ss, st, NONE))))
          in
            emit ("ss_slice_" ^ si, res)
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION J:  Char level — ord/chr round-trip, toString/escape,          *)
(*   compare consistency with <, toUpper/toLower, predicate classes,      *)
(*   sweep over ALL bytes 0..255                                          *)
(* ===================================================================== *)

fun runJ () =
  let
    (* exhaustive sweep 0..255 — deterministic, no LCG draws *)
    fun sweep i =
      if i > 255 then ()
      else
        let
          val c = Char.chr i
          val si = N i
        in
          (* ord/chr round-trip *)
          emit ("char_roundtrip_" ^ si, B (Char.ord (Char.chr i) = i));
          (* Char.toString (C-escape) — should match String.toString of the 1-char string *)
          emit ("char_toString_" ^ si, Char.toString c);
          emit ("char_toString_agree_" ^ si, B (Char.toString c = String.toString (String.str c)));
          (* predicate classes *)
          emit ("char_isAlpha_" ^ si, B (Char.isAlpha c));
          emit ("char_isDigit_" ^ si, B (Char.isDigit c));
          emit ("char_isAlphaNum_" ^ si, B (Char.isAlphaNum c));
          emit ("char_isSpace_" ^ si, B (Char.isSpace c));
          emit ("char_isPunct_" ^ si, B (Char.isPunct c));
          emit ("char_isGraph_" ^ si, B (Char.isGraph c));
          emit ("char_isPrint_" ^ si, B (Char.isPrint c));
          emit ("char_isCntrl_" ^ si, B (Char.isCntrl c));
          emit ("char_isUpper_" ^ si, B (Char.isUpper c));
          emit ("char_isLower_" ^ si, B (Char.isLower c));
          emit ("char_isHexDigit_" ^ si, B (Char.isHexDigit c));
          emit ("char_isAscii_" ^ si, B (Char.isAscii c));
          (* case conversions (ordinals) *)
          emit ("char_toUpper_" ^ si, cOrd (Char.toUpper c));
          emit ("char_toLower_" ^ si, cOrd (Char.toLower c));
          (* Char.compare consistency with < on chars: compare a few neighbours *)
          let
            val d = Char.chr ((i + 1) mod 256)
            val cc = Char.compare (c, d)
          in
            emit ("char_cmp_lt_" ^ si, B ((cc = LESS) = (c < d)))
          end;
          sweep (i + 1)
        end
  in sweep 0 end;

(* ===================================================================== *)
(* SECTION K:  Char.fromString / String.fromString / toString round-trip *)
(*   (escape encode then decode must recover the original)                *)
(* ===================================================================== *)

val nK = 200;

fun runK () =
  let
    fun loop i =
      if i >= nK then ()
      else
        let
          val a = rstrBiased 14
          val si = N i
          (* String.toString then String.fromString must recover a (it is the
             canonical escape/unescape pair) *)
          val encoded = String.toString a
          val decoded = String.fromString encoded
        in
          emit ("law_str_escape_roundtrip_" ^ si, B (decoded = SOME a));
          (* the encoded form itself (already ASCII) for content diffing *)
          emit ("str_toString_" ^ si, encoded);
          (* Char round-trip: toString c then fromString recovers c *)
          let
            val c = rchar ()
            val cenc = Char.toString c
            val cdec = Char.fromString cenc
          in
            emit ("law_char_escape_roundtrip_" ^ si, B (cdec = SOME c));
            emit ("char_toString_val_" ^ si, cenc)
          end;
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION L:  fixed CORNER cases (empty, singleton, boundary indices,    *)
(*   max-byte, control bytes) — named, non-random                          *)
(* ===================================================================== *)

fun runL () =
  let
    val empty = ""
    val one = "x"
    (* a string with the full set of "interesting" bytes built at runtime *)
    val mixed = String.implode (List.tabulate (256, fn i => Char.chr i))
    val hi = String.implode [Char.chr 0, Char.chr 127, Char.chr 128, Char.chr 200, Char.chr 255]
  in
    (* empty string ops *)
    emit ("corner_empty_size", N (String.size empty));
    emit ("corner_empty_sub", wrap (fn () => cOrd (String.sub (empty, 0))));
    emit ("corner_empty_substr0", wrap (fn () => S (String.substring (empty, 0, 0))));
    emit ("corner_empty_explode", listC (String.explode empty));
    emit ("corner_empty_rev_concat", S (empty ^ empty));
    emit ("corner_empty_compare", ordTok (String.compare (empty, empty)));
    emit ("corner_empty_lt_one", ordTok (String.compare (empty, one)));
    emit ("corner_empty_isPrefix", B (String.isPrefix empty one));
    emit ("corner_empty_isSub", B (String.isSubstring empty empty));
    (* singleton ops *)
    emit ("corner_one_sub0", cOrd (String.sub (one, 0)));
    emit ("corner_one_sub1", wrap (fn () => cOrd (String.sub (one, 1))));
    emit ("corner_one_substr_full", S (String.substring (one, 0, 1)));
    emit ("corner_one_extract_end", S (String.extract (one, 1, NONE)));
    (* mixed 0..255: size, last byte, escape round-trip *)
    emit ("corner_mixed_size", N (String.size mixed));
    emit ("corner_mixed_last", cOrd (String.sub (mixed, 255)));
    emit ("corner_mixed_first", cOrd (String.sub (mixed, 0)));
    emit ("corner_mixed_escape_roundtrip", B (String.fromString (String.toString mixed) = SOME mixed));
    emit ("corner_mixed_escape", String.toString mixed);
    (* high bytes: compare order is by UNSIGNED byte value *)
    emit ("corner_hi_escape", String.toString hi);
    emit ("corner_hi_size", N (String.size hi));
    emit ("corner_hi_compare_128_127", ordTok (String.compare (String.str (Char.chr 128), String.str (Char.chr 127))));
    emit ("corner_hi_compare_255_0", ordTok (String.compare (String.str (Char.chr 255), String.str (Char.chr 0))));
    (* boundary substrings: at exactly size, zero length, out by one *)
    emit ("corner_substr_at_end", wrap (fn () => S (String.substring (one, 1, 0))));
    emit ("corner_substr_over", wrap (fn () => S (String.substring (one, 0, 2))));
    emit ("corner_substr_neg_via_extract", wrap (fn () => S (String.extract (one, 2, NONE))));
    (* Chr exception: Char.chr out of range *)
    emit ("corner_chr_256", wrap (fn () => cOrd (Char.chr 256)));
    emit ("corner_chr_neg1", wrap (fn () => cOrd (Char.chr ~1)));
    (* concatWith corners *)
    emit ("corner_concatWith_empty", "[" ^ String.concatWith "," [] ^ "]");
    emit ("corner_concatWith_singleton", String.concatWith "," ["solo"]);
    emit ("corner_concat_empties", "[" ^ String.concat ["", "", ""] ^ "]");
    (* tokens/fields on all-delimiters and empty *)
    emit ("corner_tokens_alldelim", N (List.length (String.tokens (fn c => c = #",") ",,,")));
    emit ("corner_fields_alldelim", N (List.length (String.fields (fn c => c = #",") ",,,")));
    emit ("corner_tokens_empty", N (List.length (String.tokens (fn c => c = #",") "")));
    emit ("corner_fields_empty", N (List.length (String.fields (fn c => c = #",") "")));
    (* translate empty *)
    emit ("corner_translate_empty", "[" ^ String.translate (fn c => String.str c) empty ^ "]");
    (* map empty *)
    emit ("corner_map_empty", "[" ^ String.map Char.toUpper empty ^ "]");
    (* fromString of various escapes *)
    emit ("corner_fromString_tab", optI (Option.map String.size (String.fromString "a\\tb")));
    emit ("corner_fromString_dec", optI (Option.map (fn x => Char.ord (String.sub (x, 0))) (String.fromString "\\127")));
    emit ("corner_fromString_bad", optS (String.fromString "a\\q"));
    emit ("corner_char_fromString_dec", optC (Char.fromString "\\200"));
    emit ("corner_char_fromString_caret", optC (Char.fromString "\\^A"));   (* control escape *)
    (* Substring.base round-trips *)
    let val (bs, bi, bn) = Substring.base (Substring.substring (mixed, 10, 5)) in
      emit ("corner_ss_base", N bi ^ "/" ^ N bn ^ "/" ^ B (bs = mixed))
    end
  end;

(* ===================================================================== *)
(* run all sections — FIXED order => deterministic LCG consumption        *)
(* ===================================================================== *)
val () = runA ();
val () = runB ();
val () = runC ();
val () = runD ();
val () = runE ();
val () = runF ();
val () = runG ();
val () = runH ();
val () = runI_ ();
val () = runJ ();
val () = runK ();
val () = runL ();
