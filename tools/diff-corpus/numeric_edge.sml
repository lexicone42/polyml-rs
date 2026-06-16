(* diff-corpus category: numeric_edge — numeric edge cases BEYOND the existing
   corpus (intinf/fixedint/int_overflow2/int_radix/words/largeword/word8/...).
   New coverage targeted here:
     - IntInf.sign / sameSign / abs / min / max / compare on big values
     - IntInf.divMod vs quotRem SIGN conventions on ALL four sign combos
       (existing corpus only had neg-dividend / neg-divisor singletons)
     - IntInf.pow corners: pow(0,0), pow(1,big), pow(0,n), neg base even/odd,
       very large exp (2^200), and negative-exponent behavior
     - very large IntInf arithmetic (2^200 +/- */ mod) and log2 at 2^200
     - IntInf.fromString / scan in BIN/OCT/HEX radices, fmt round-trips
     - Word.fmt / Word.scan (NO Word-radix coverage existed) BIN/OCT/HEX
     - Word shift-by-0 identity, Word.min/max, Word.fromInt of minInt
     - Int.sameSign/sign extra combos, Int.abs/min/max on big-in-range vals
   All outputs are deterministic & platform-stable (no addresses/timing). *)

(* ---- IntInf sign / abs / min / max / compare ---- *)
val () = print ("@@ii_sign_posbig=" ^ Int.toString (IntInf.sign (IntInf.pow(2,80))) ^ "\n");
val () = print ("@@ii_sign_negbig=" ^ Int.toString (IntInf.sign (~(IntInf.pow(2,80)))) ^ "\n");
val () = print ("@@ii_sign_zero=" ^ Int.toString (IntInf.sign (IntInf.fromInt 0)) ^ "\n");
val () = print ("@@ii_samesign_negs=" ^ Bool.toString (IntInf.sameSign(~(IntInf.pow(2,70)), IntInf.fromInt ~1)) ^ "\n");
val () = print ("@@ii_samesign_mixed=" ^ Bool.toString (IntInf.sameSign(IntInf.pow(2,70), IntInf.fromInt ~1)) ^ "\n");
val () = print ("@@ii_samesign_zero_pos=" ^ Bool.toString (IntInf.sameSign(IntInf.fromInt 0, IntInf.pow(2,70))) ^ "\n");
val () = print ("@@ii_abs_negbig=" ^ IntInf.toString (IntInf.abs (~(IntInf.pow(2,90)))) ^ "\n");
val () = print ("@@ii_abs_posbig=" ^ IntInf.toString (IntInf.abs (IntInf.pow(2,90))) ^ "\n");
val () = print ("@@ii_min_bigs=" ^ IntInf.toString (IntInf.min(IntInf.pow(2,80), ~(IntInf.pow(2,79)))) ^ "\n");
val () = print ("@@ii_max_bigs=" ^ IntInf.toString (IntInf.max(IntInf.pow(2,80), ~(IntInf.pow(2,79)))) ^ "\n");

(* ---- IntInf.divMod vs quotRem on all four sign combinations ----
   divMod: result floors toward -inf, remainder has sign of divisor.
   quotRem: result truncates toward 0, remainder has sign of dividend. *)
val () = let val (q,r)=IntInf.divMod(IntInf.fromInt 17, IntInf.fromInt 5) in print ("@@ii_divmod_pp=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.divMod(IntInf.fromInt ~17, IntInf.fromInt 5) in print ("@@ii_divmod_np=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.divMod(IntInf.fromInt 17, IntInf.fromInt ~5) in print ("@@ii_divmod_pn=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.divMod(IntInf.fromInt ~17, IntInf.fromInt ~5) in print ("@@ii_divmod_nn=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.quotRem(IntInf.fromInt 17, IntInf.fromInt 5) in print ("@@ii_quotrem_pp=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.quotRem(IntInf.fromInt ~17, IntInf.fromInt 5) in print ("@@ii_quotrem_np=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.quotRem(IntInf.fromInt 17, IntInf.fromInt ~5) in print ("@@ii_quotrem_pn=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.quotRem(IntInf.fromInt ~17, IntInf.fromInt ~5) in print ("@@ii_quotrem_nn=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
(* big-operand divMod/quotRem with negatives crossing the 2^63 boundary *)
val () = let val (q,r)=IntInf.divMod(~(IntInf.pow(2,80)) - 3, IntInf.fromInt 7) in print ("@@ii_divmod_bignp=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;
val () = let val (q,r)=IntInf.quotRem(~(IntInf.pow(2,80)) - 3, IntInf.fromInt 7) in print ("@@ii_quotrem_bignp=" ^ IntInf.toString q ^ "," ^ IntInf.toString r ^ "\n") end;

(* ---- IntInf.pow corners ---- *)
val () = print ("@@ii_pow_0_0=" ^ IntInf.toString (IntInf.pow(0,0)) ^ "\n");
val () = print ("@@ii_pow_1_big=" ^ IntInf.toString (IntInf.pow(1, 1000)) ^ "\n");
val () = print ("@@ii_pow_0_n=" ^ IntInf.toString (IntInf.pow(0, 5)) ^ "\n");
val () = print ("@@ii_pow_negbase_even=" ^ IntInf.toString (IntInf.pow(~2, 10)) ^ "\n");
val () = print ("@@ii_pow_negbase_odd=" ^ IntInf.toString (IntInf.pow(~2, 11)) ^ "\n");
val () = print ("@@ii_pow_2_200=" ^ IntInf.toString (IntInf.pow(2, 200)) ^ "\n");
val () = print ("@@ii_pow_neg_exp=" ^ ((IntInf.toString (IntInf.pow(2, ~1))) handle Domain => "Domain" | Div => "Div" | Size => "Size" | Overflow => "Overflow" | _ => "OTHER") ^ "\n");
val () = print ("@@ii_pow_neg1_neg_exp=" ^ ((IntInf.toString (IntInf.pow(~1, ~3))) handle Domain => "Domain" | Div => "Div" | _ => "OTHER") ^ "\n");

(* ---- very large IntInf arithmetic around 2^200 ---- *)
val () = print ("@@ii_2p200_plus1=" ^ IntInf.toString (IntInf.pow(2,200) + 1) ^ "\n");
val () = print ("@@ii_2p200_times3=" ^ IntInf.toString (IntInf.pow(2,200) * 3) ^ "\n");
val () = print ("@@ii_2p200_div_2p100=" ^ IntInf.toString (IntInf.pow(2,200) div IntInf.pow(2,100)) ^ "\n");
val () = print ("@@ii_2p200_mod_7=" ^ IntInf.toString (IntInf.pow(2,200) mod IntInf.fromInt 7) ^ "\n");
val () = print ("@@ii_log2_2p200=" ^ Int.toString (IntInf.log2 (IntInf.pow(2,200))) ^ "\n");
val () = print ("@@ii_log2_2p200_minus1=" ^ Int.toString (IntInf.log2 (IntInf.pow(2,200) - 1)) ^ "\n");

(* ---- IntInf.fromString / scan / fmt in radices ---- *)
val () = print ("@@ii_fromString_big=" ^ (case IntInf.fromString "340282366920938463463374607431768211456" of SOME n => IntInf.toString n | NONE => "NONE") ^ "\n");
val () = print ("@@ii_fromString_neg=" ^ (case IntInf.fromString "~12345678901234567890" of SOME n => IntInf.toString n | NONE => "NONE") ^ "\n");
val () = print ("@@ii_fromString_garbage=" ^ (case IntInf.fromString "nope" of SOME n => IntInf.toString n | NONE => "NONE") ^ "\n");
val () = print ("@@ii_scan_hex_big=" ^ (case StringCvt.scanString (IntInf.scan StringCvt.HEX) "FFFFFFFFFFFFFFFFFF" of SOME n => IntInf.toString n | NONE => "NONE") ^ "\n");
val () = print ("@@ii_scan_bin=" ^ (case StringCvt.scanString (IntInf.scan StringCvt.BIN) "1111111111111111" of SOME n => IntInf.toString n | NONE => "NONE") ^ "\n");
val () = print ("@@ii_scan_oct=" ^ (case StringCvt.scanString (IntInf.scan StringCvt.OCT) "7777777777" of SOME n => IntInf.toString n | NONE => "NONE") ^ "\n");
val () = print ("@@ii_fmt_hex_big=" ^ IntInf.fmt StringCvt.HEX (IntInf.pow(2,100)) ^ "\n");
val () = print ("@@ii_fmt_bin_255=" ^ IntInf.fmt StringCvt.BIN (IntInf.fromInt 255) ^ "\n");
val () = print ("@@ii_radix_roundtrip=" ^ Bool.toString (StringCvt.scanString (IntInf.scan StringCvt.HEX) (IntInf.fmt StringCvt.HEX (IntInf.pow(2,123)+45)) = SOME (IntInf.pow(2,123)+45)) ^ "\n");

(* ---- Word.fmt / Word.scan (no Word-radix coverage existed) ---- *)
val () = print ("@@w_fmt_bin=" ^ Word.fmt StringCvt.BIN (Word.fromInt 10) ^ "\n");
val () = print ("@@w_fmt_oct=" ^ Word.fmt StringCvt.OCT (Word.fromInt 64) ^ "\n");
val () = print ("@@w_fmt_hex=" ^ Word.fmt StringCvt.HEX (Word.fromInt 43981) ^ "\n");
val () = print ("@@w_fmt_dec=" ^ Word.fmt StringCvt.DEC (Word.fromInt 12345) ^ "\n");
val () = print ("@@w_scan_hex=" ^ (case StringCvt.scanString (Word.scan StringCvt.HEX) "DEADBEEF" of SOME w => Word.toString w | NONE => "NONE") ^ "\n");
val () = print ("@@w_scan_bin=" ^ (case StringCvt.scanString (Word.scan StringCvt.BIN) "1010" of SOME w => Word.toString w | NONE => "NONE") ^ "\n");
val () = print ("@@w_scan_dec=" ^ (case StringCvt.scanString (Word.scan StringCvt.DEC) "255" of SOME w => Word.toString w | NONE => "NONE") ^ "\n");
val () = print ("@@w_fmt_neg1_hex=" ^ Word.fmt StringCvt.HEX (Word.fromInt ~1) ^ "\n");

(* ---- Word shift-by-0 identity, min/max, fromInt of minInt ---- *)
val () = print ("@@w_shl_by0=" ^ Word.toString (Word.<< (0wxABCD, 0w0)) ^ "\n");
val () = print ("@@w_lsr_by0=" ^ Word.toString (Word.>> (0wxABCD, 0w0)) ^ "\n");
val () = print ("@@w_asr_by0=" ^ Word.toString (Word.~>> (Word.fromInt ~1, 0w0)) ^ "\n");
val () = print ("@@w_min_wrap=" ^ Word.toString (Word.min (0w5, Word.fromInt ~1)) ^ "\n");
val () = print ("@@w_max_wrap=" ^ Word.toString (Word.max (0w5, Word.fromInt ~1)) ^ "\n");
val () = print ("@@w_fromInt_minint_toString=" ^ Word.toString (Word.fromInt (valOf Int.minInt)) ^ "\n");
val () = print ("@@w_fromInt_minint_toIntX=" ^ Int.toString (Word.toIntX (Word.fromInt (valOf Int.minInt))) ^ "\n");

(* ---- Int.sign / sameSign / abs / min / max extra combos ---- *)
val () = print ("@@int_sign_pos=" ^ Int.toString (Int.sign 99) ^ "\n");
val () = print ("@@int_samesign_pos_neg=" ^ Bool.toString (Int.sameSign (7, ~7)) ^ "\n");
val () = print ("@@int_samesign_zero_zero=" ^ Bool.toString (Int.sameSign (0, 0)) ^ "\n");
val () = print ("@@int_samesign_neg_zero=" ^ Bool.toString (Int.sameSign (~7, 0)) ^ "\n");
val () = print ("@@int_abs_big=" ^ Int.toString (Int.abs (~4611686018427387903)) ^ "\n");
val () = print ("@@int_min_max=" ^ Int.toString (Int.min (~5, 5)) ^ "," ^ Int.toString (Int.max (~5, 5)) ^ "\n");
