(* diff-corpus category: text_edge — Char/String/Substring/CharVector edge cases
   beyond strings.sml, string_ops2.sml, substring.sml, char_pred.sml,
   char_escapes.sml. Targets: Chr-exception boundaries (chr/succ/pred), the full
   escape-sequence matrix for fromString/fromCString (\ddd \uXXXX \^X \a\b\f\v\r),
   String/Char.scan, String.collate all three orders, String.translate/map/tokens
   /fields delimiter corners, extract/substring Subscript boundaries, CharVector,
   and Substring concatWith/splitAt/getc chaining. ASCII-only, deterministic. *)

(* --- Char.chr / ord / succ / pred boundary exceptions (Chr) --- *)
val () = print ("@@chr_0=" ^ Int.toString (Char.ord (Char.chr 0)) ^ "\n");
val () = print ("@@chr_255=" ^ Int.toString (Char.ord (Char.chr 255)) ^ "\n");
val () = print ("@@chr_256=" ^ ((Int.toString (Char.ord (Char.chr 256))) handle Chr => "CAUGHT_Chr" | _ => "OTHER") ^ "\n");
val () = print ("@@chr_neg=" ^ ((Int.toString (Char.ord (Char.chr ~1))) handle Chr => "CAUGHT_Chr" | _ => "OTHER") ^ "\n");
val () = print ("@@chr_big=" ^ ((Int.toString (Char.ord (Char.chr 1000))) handle Chr => "CAUGHT_Chr" | _ => "OTHER") ^ "\n");
val () = print ("@@succ_at_max=" ^ ((Int.toString (Char.ord (Char.succ (Char.chr 255)))) handle Chr => "CAUGHT_Chr" | _ => "OTHER") ^ "\n");
val () = print ("@@succ_254=" ^ Int.toString (Char.ord (Char.succ (Char.chr 254))) ^ "\n");
val () = print ("@@pred_at_min=" ^ ((Int.toString (Char.ord (Char.pred (Char.chr 0)))) handle Chr => "CAUGHT_Chr" | _ => "OTHER") ^ "\n");
val () = print ("@@pred_1=" ^ Int.toString (Char.ord (Char.pred (Char.chr 1))) ^ "\n");
val () = print ("@@minchar=" ^ Int.toString (Char.ord Char.minChar) ^ "\n");
val () = print ("@@maxchar=" ^ Int.toString (Char.ord Char.maxChar) ^ "\n");
val () = print ("@@maxord=" ^ Int.toString Char.maxOrd ^ "\n");

(* --- Char.toLower / toUpper across non-letters and high bytes --- *)
val () = print ("@@tolower_at=" ^ Int.toString (Char.ord (Char.toLower #"@")) ^ "\n");
val () = print ("@@toupper_brace=" ^ Int.toString (Char.ord (Char.toUpper #"{")) ^ "\n");
val () = print ("@@tolower_high=" ^ Int.toString (Char.ord (Char.toLower (Char.chr 200))) ^ "\n");
val () = print ("@@toupper_high=" ^ Int.toString (Char.ord (Char.toUpper (Char.chr 230))) ^ "\n");

(* --- Char.contains / notContains corners --- *)
val () = print ("@@contains_first=" ^ Bool.toString (Char.contains "abc" #"a") ^ "\n");
val () = print ("@@contains_last=" ^ Bool.toString (Char.contains "abc" #"c") ^ "\n");
val () = print ("@@notContains_empty=" ^ Bool.toString (Char.notContains "" #"a") ^ "\n");

(* --- Char.fromString escape matrix --- *)
val () = print ("@@cfs_alarm=" ^ (case Char.fromString "\\a" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_bs=" ^ (case Char.fromString "\\b" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_vt=" ^ (case Char.fromString "\\v" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_ff=" ^ (case Char.fromString "\\f" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_cr=" ^ (case Char.fromString "\\r" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_ctrlA=" ^ (case Char.fromString "\\^A" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_ctrlAt=" ^ (case Char.fromString "\\^@" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_dec=" ^ (case Char.fromString "\\065" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_uXXXX=" ^ (case Char.fromString "\\u0041" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_backslash=" ^ (case Char.fromString "\\\\" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_quote=" ^ (case Char.fromString "\\\"" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfs_dec256=" ^ (case Char.fromString "\\256" of SOME c => "SOME:" ^ Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");

(* --- Char.fromCString C-escape matrix (octal, hex, \?) --- *)
val () = print ("@@cfcs_oct=" ^ (case Char.fromCString "\\101" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfcs_hex=" ^ (case Char.fromCString "\\x41" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfcs_q=" ^ (case Char.fromCString "\\?" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");
val () = print ("@@cfcs_squote=" ^ (case Char.fromCString "\\'" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");

(* --- Char.toString / toCString of specials --- *)
val () = print ("@@cts_high200=" ^ Char.toString (Char.chr 200) ^ "\n");
val () = print ("@@ctcs_high200=" ^ Char.toCString (Char.chr 200) ^ "\n");
val () = print ("@@ctcs_squote=" ^ Char.toCString #"'" ^ "\n");

(* --- Char.fromString / fromCString round trip over all 256 --- *)
val () = print ("@@cfs_rt256=" ^ (let fun ok c = (case Char.fromString (Char.toString c) of SOME r => r = c | NONE => false) in Bool.toString (List.all ok (List.tabulate (256, Char.chr))) end) ^ "\n");
val () = print ("@@cfcs_rt256=" ^ (let fun ok c = (case Char.fromCString (Char.toCString c) of SOME r => r = c | NONE => false) in Bool.toString (List.all ok (List.tabulate (256, Char.chr))) end) ^ "\n");

(* --- String.fromString escape forms: \uXXXX, \^X, \ddd, gap, formatting fail --- *)
val () = print ("@@sfs_u=" ^ (case String.fromString "x\\u0042y" of SOME s => s | NONE => "NONE") ^ "\n");
val () = print ("@@sfs_ctrl=" ^ (case String.fromString "\\^A\\^Z" of SOME s => Int.toString (size s) ^ ":" ^ Int.toString (Char.ord (String.sub (s,0))) ^ "," ^ Int.toString (Char.ord (String.sub (s,1))) | NONE => "NONE") ^ "\n");
val () = print ("@@sfs_dec=" ^ (case String.fromString "\\065\\066" of SOME s => s | NONE => "NONE") ^ "\n");
val () = print ("@@sfs_gap=" ^ (case String.fromString "ab\\ \\cd" of SOME s => s | NONE => "NONE") ^ "\n");
val () = print ("@@sfs_gap_nl=" ^ (case String.fromString "ab\\\n\\cd" of SOME s => s | NONE => "NONE") ^ "\n");
val () = print ("@@sfs_bad=" ^ (case String.fromString "ab\\qcd" of SOME s => "SOME:" ^ s | NONE => "NONE") ^ "\n");
val () = print ("@@sfs_lone_bs=" ^ (case String.fromString "ab\\" of SOME s => "SOME:" ^ Int.toString (size s) | NONE => "NONE") ^ "\n");

(* --- String.scan / Char.scan via StringCvt --- *)
val () = print ("@@strscan=" ^ (case StringCvt.scanString String.scan "ab\\tcd" of SOME s => Int.toString (size s) | NONE => "NONE") ^ "\n");
val () = print ("@@charscan=" ^ (case StringCvt.scanString Char.scan "\\065" of SOME c => Int.toString (Char.ord c) | NONE => "NONE") ^ "\n");

(* --- String.compare / collate: all three orders --- *)
val () = print ("@@cmp_lt=" ^ (case String.compare ("abc","abd") of LESS=>"LESS"|EQUAL=>"EQUAL"|GREATER=>"GREATER") ^ "\n");
val () = print ("@@cmp_gt=" ^ (case String.compare ("abd","abc") of LESS=>"LESS"|EQUAL=>"EQUAL"|GREATER=>"GREATER") ^ "\n");
val () = print ("@@cmp_eq_empty=" ^ (case String.compare ("","") of LESS=>"LESS"|EQUAL=>"EQUAL"|GREATER=>"GREATER") ^ "\n");
val () = print ("@@coll_gt=" ^ (case String.collate Char.compare ("abd","abc") of LESS=>"LESS"|EQUAL=>"EQUAL"|GREATER=>"GREATER") ^ "\n");
val () = print ("@@coll_eq=" ^ (case String.collate Char.compare ("abc","abc") of LESS=>"LESS"|EQUAL=>"EQUAL"|GREATER=>"GREATER") ^ "\n");
val () = print ("@@coll_highbyte=" ^ (case String.collate Char.compare (String.str (Char.chr 200), String.str (Char.chr 65)) of LESS=>"LESS"|EQUAL=>"EQUAL"|GREATER=>"GREATER") ^ "\n");

(* --- String.translate / map with high bytes and expansion --- *)
val () = print ("@@translate_high=" ^ String.translate (fn c => if Char.ord c > 127 then "#" else String.str c) (String.implode [#"a", Char.chr 200, #"b"]) ^ "\n");
val () = print ("@@map_id=[" ^ String.map (fn c => c) "xyz" ^ "]\n");

(* --- String.tokens / fields: leading/trailing/consecutive --- *)
val () = print ("@@tok_count=" ^ Int.toString (length (String.tokens (fn c => c = #",") ",a,,b,")) ^ "\n");
val () = print ("@@fld_count=" ^ Int.toString (length (String.fields (fn c => c = #",") ",a,,b,")) ^ "\n");
val () = print ("@@fld_single=[" ^ String.concatWith "|" (String.fields (fn c => c = #",") "abc") ^ "]\n");
val () = print ("@@tok_alldelim=" ^ Int.toString (length (String.tokens (fn c => c = #",") ",,,")) ^ "\n");

(* --- String.extract / substring boundary + Subscript --- *)
val () = print ("@@extract_endzero=[" ^ String.extract ("abc", 3, SOME 0) ^ "]\n");
val () = print ("@@extract_neg=" ^ ((String.extract ("abc", ~1, NONE)) handle Subscript => "Subscript" | _ => "OTHER") ^ "\n");
val () = print ("@@extract_overlen=" ^ ((String.extract ("abc", 1, SOME 5)) handle Subscript => "Subscript" | _ => "OTHER") ^ "\n");
val () = print ("@@substring_full=[" ^ String.substring ("abc", 0, 3) ^ "]\n");
val () = print ("@@substring_neg_len=" ^ ((String.substring ("abc", 0, ~1)) handle Subscript => "Subscript" | _ => "OTHER") ^ "\n");
val () = print ("@@sub_oob=" ^ ((Int.toString (Char.ord (String.sub ("abc", 3)))) handle Subscript => "Subscript" | _ => "OTHER") ^ "\n");
val () = print ("@@str_str=[" ^ String.str (Char.chr 90) ^ "]\n");

(* --- String.implode / explode round trip incl high bytes --- *)
val () = print ("@@implode_high=" ^ Int.toString (List.length (String.explode (String.implode [Char.chr 0, Char.chr 200, Char.chr 255]))) ^ "\n");
val () = print ("@@explode_rt_all=" ^ (let val s = String.implode (List.tabulate (256, Char.chr)) in Bool.toString (String.implode (String.explode s) = s) end) ^ "\n");

(* --- CharVector ops --- *)
val () = print ("@@cv_tab=" ^ CharVector.tabulate (4, fn i => Char.chr (97 + i)) ^ "\n");
val () = print ("@@cv_map=" ^ CharVector.map Char.toUpper "abc" ^ "\n");
val () = print ("@@cv_foldl=" ^ Int.toString (CharVector.foldl (fn (c,a) => a + Char.ord c) 0 "AB") ^ "\n");
val () = print ("@@cv_foldr=" ^ CharVector.foldr (fn (c,a) => String.str c ^ a) "" "abc" ^ "\n");
val () = print ("@@cv_len=" ^ Int.toString (CharVector.length "hello") ^ "\n");

(* --- Substring: concatWith, splitAt, getc chaining, full/slice corners --- *)
val () = print ("@@ss_concatWith=" ^ Substring.concatWith "-" [Substring.full "a", Substring.full "", Substring.full "c"] ^ "\n");
val () = print ("@@ss_splitAt=" ^ (let val (a,b) = Substring.splitAt (Substring.full "abcdef", 4) in Substring.string a ^ "|" ^ Substring.string b end) ^ "\n");
val () = print ("@@ss_splitAt_zero=" ^ (let val (a,b) = Substring.splitAt (Substring.full "abc", 0) in "[" ^ Substring.string a ^ "][" ^ Substring.string b ^ "]" end) ^ "\n");
val () = print ("@@ss_splitAt_bad=" ^ ((let val (a,b) = Substring.splitAt (Substring.full "abc", 5) in Substring.string a end) handle Subscript => "Subscript" | _ => "OTHER") ^ "\n");
val () = print ("@@ss_getc_chain=" ^ (case Substring.getc (Substring.full "xy") of SOME (c, rest) => String.str c ^ ":" ^ Int.toString (Substring.size rest) | NONE => "NONE") ^ "\n");
val () = print ("@@ss_isEmpty_t=" ^ Bool.toString (Substring.isEmpty (Substring.full "")) ^ "\n");
val () = print ("@@ss_isEmpty_f=" ^ Bool.toString (Substring.isEmpty (Substring.full "x")) ^ "\n");
val () = print ("@@ss_sub=" ^ Int.toString (Char.ord (Substring.sub (Substring.extract ("zabcz", 1, SOME 3), 1))) ^ "\n");
val () = print ("@@ss_sub_oob=" ^ ((Int.toString (Char.ord (Substring.sub (Substring.full "ab", 5)))) handle Subscript => "Subscript" | _ => "OTHER") ^ "\n");
