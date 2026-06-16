(* diff-corpus category: real_edge — Real/Real32 special-value & edge behavior
   (gaps beyond real64/real32/real_arith2/real_classify/real_fmt/realint/
    math_identities/mathconst, added 2026-06-16).
   Focus: fmt/toString on inf/nan, fromString/scan, the full toLargeInt
   rounding-mode matrix, copySign/nextAfter/signBit/sameSign edge inputs,
   split/toManExp round-trips on specials, Math.* on edge inputs, and the
   Real32 mirrors of all of the above. *)

(* ---- Real.fmt / Real.toString on infinities and NaN (NOT covered before) ---- *)
val () = print ("@@fmt_gen_posinf=" ^ Real.fmt (StringCvt.GEN (SOME 6)) Real.posInf ^ "\n");
val () = print ("@@fmt_gen_neginf=" ^ Real.fmt (StringCvt.GEN (SOME 6)) Real.negInf ^ "\n");
val () = print ("@@fmt_fix_posinf=" ^ Real.fmt (StringCvt.FIX (SOME 4)) Real.posInf ^ "\n");
val () = print ("@@fmt_sci_neginf=" ^ Real.fmt (StringCvt.SCI (SOME 4)) Real.negInf ^ "\n");
val () = print ("@@fmt_gen_nan=" ^ Real.fmt (StringCvt.GEN (SOME 6)) (0.0/0.0) ^ "\n");
val () = print ("@@fmt_fix_nan=" ^ Real.fmt (StringCvt.FIX (SOME 2)) (0.0/0.0) ^ "\n");
val () = print ("@@fmt_exact_posinf=" ^ Real.fmt StringCvt.EXACT Real.posInf ^ "\n");
val () = print ("@@tostring_posinf=" ^ Real.toString Real.posInf ^ "\n");
val () = print ("@@tostring_neginf=" ^ Real.toString Real.negInf ^ "\n");
val () = print ("@@tostring_nan=" ^ Real.toString (0.0/0.0) ^ "\n");

(* ---- Real.fromString / Real.scan (NOT covered before) ---- *)
val () = print ("@@fromstring_plain=" ^ Real.fmt (StringCvt.FIX (SOME 4)) (Option.getOpt (Real.fromString "3.5", ~9.0)) ^ "\n");
val () = print ("@@fromstring_neg=" ^ Real.fmt (StringCvt.FIX (SOME 4)) (Option.getOpt (Real.fromString "~2.25", ~9.0)) ^ "\n");
val () = print ("@@fromstring_exp=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Option.getOpt (Real.fromString "1.5e3", ~9.0)) ^ "\n");
val () = print ("@@fromstring_negexp=" ^ Real.fmt (StringCvt.SCI (SOME 3)) (Option.getOpt (Real.fromString "1.0E~3", ~9.0)) ^ "\n");
val () = print ("@@fromstring_leadws=" ^ Real.fmt (StringCvt.FIX (SOME 2)) (Option.getOpt (Real.fromString "   4.0", ~9.0)) ^ "\n");
val () = print ("@@fromstring_bad=" ^ Bool.toString (Option.isSome (Real.fromString "abc")) ^ "\n");
val () = print ("@@fromstring_empty=" ^ Bool.toString (Option.isSome (Real.fromString "")) ^ "\n");
val () = print ("@@fromstring_inf=" ^ (case Real.fromString "inf" of SOME r => Bool.toString (Real.isFinite r) | NONE => "NONE") ^ "\n");
val () = print ("@@scan_trailing=" ^ (case Real.scan Substring.getc (Substring.full "  -2.5xyz") of SOME (r, rest) => Real.fmt (StringCvt.FIX (SOME 2)) r ^ "|" ^ Substring.string rest | NONE => "NONE") ^ "\n");
val () = print ("@@scan_int_only=" ^ (case Real.scan Substring.getc (Substring.full "42 rest") of SOME (r, rest) => Real.fmt (StringCvt.FIX (SOME 1)) r ^ "|" ^ Substring.string rest | NONE => "NONE") ^ "\n");
val () = print ("@@fromstring_roundtrip=" ^ Bool.toString (Real.== (Option.valOf (Real.fromString (Real.fmt StringCvt.EXACT 3.140625)), 3.140625)) ^ "\n");

(* ---- Real.toLargeInt: full rounding-mode matrix on .5 boundaries ---- *)
val () = print ("@@tli_nearest_2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST 2.5) ^ "\n");
val () = print ("@@tli_nearest_3p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST 3.5) ^ "\n");
val () = print ("@@tli_nearest_neg2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST (~2.5)) ^ "\n");
val () = print ("@@tli_neginf_2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEGINF 2.5) ^ "\n");
val () = print ("@@tli_neginf_neg2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEGINF (~2.5)) ^ "\n");
val () = print ("@@tli_posinf_2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_POSINF 2.5) ^ "\n");
val () = print ("@@tli_posinf_neg2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_POSINF (~2.5)) ^ "\n");
val () = print ("@@tli_zero_2p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_ZERO 2.5) ^ "\n");
val () = print ("@@tli_zero_neg3p5=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_ZERO (~3.5)) ^ "\n");
val () = print ("@@tli_nan_raises=" ^ ((LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST (0.0/0.0))) handle Domain => "DOMAIN" | Overflow => "OVERFLOW" | _ => "OTHER") ^ "\n");
val () = print ("@@tli_inf_raises=" ^ ((LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST Real.posInf)) handle Domain => "DOMAIN" | Overflow => "OVERFLOW" | _ => "OTHER") ^ "\n");

(* ---- copySign / signBit / sameSign edge inputs ---- *)
val () = print ("@@copysign_nan_src=" ^ Bool.toString (Real.signBit (Real.copySign (0.0/0.0, ~1.0))) ^ "\n");
val () = print ("@@copysign_inf_neg=" ^ Real.toString (Real.copySign (Real.posInf, ~1.0)) ^ "\n");
val () = print ("@@copysign_from_negzero=" ^ Bool.toString (Real.signBit (Real.copySign (5.0, ~0.0))) ^ "\n");
val () = print ("@@copysign_pos_to_neg=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Real.copySign (~7.5, 2.0)) ^ "\n");
val () = print ("@@signbit_nan=" ^ Bool.toString (Real.signBit (0.0/0.0)) ^ "\n");
val () = print ("@@samesign_nan_pos=" ^ ((Bool.toString (Real.sameSign (0.0/0.0, 1.0))) handle Domain => "DOMAIN" | _ => "OTHER") ^ "\n");
val () = print ("@@samesign_negzero_pos=" ^ Bool.toString (Real.sameSign (~0.0, 1.0)) ^ "\n");
val () = print ("@@samesign_inf=" ^ Bool.toString (Real.sameSign (Real.posInf, Real.negInf)) ^ "\n");

(* ---- nextAfter edge inputs ---- *)
val () = print ("@@nextafter_zero_up_minpos=" ^ Bool.toString (Real.== (Real.nextAfter (0.0, 1.0), Real.minPos)) ^ "\n");
val () = print ("@@nextafter_eq=" ^ Real.toString (Real.nextAfter (5.0, 5.0)) ^ "\n");
val () = print ("@@nextafter_nan=" ^ Bool.toString (Real.isNan (Real.nextAfter (0.0/0.0, 1.0))) ^ "\n");
val () = print ("@@nextafter_max_up_inf=" ^ Bool.toString (Real.== (Real.nextAfter (Real.maxFinite, Real.posInf), Real.posInf)) ^ "\n");
val () = print ("@@nextafter_inf_down=" ^ Bool.toString (Real.== (Real.nextAfter (Real.posInf, 0.0), Real.maxFinite)) ^ "\n");

(* ---- ?= / != / unordered matrix ---- *)
val () = print ("@@qm_inf_inf=" ^ Bool.toString (Real.?= (Real.posInf, Real.posInf)) ^ "\n");
val () = print ("@@qm_nan_nan=" ^ Bool.toString (Real.?= (0.0/0.0, 0.0/0.0)) ^ "\n");
val () = print ("@@neq_diff=" ^ Bool.toString (Real.!= (1.0, 2.0)) ^ "\n");
val () = print ("@@neq_negzero=" ^ Bool.toString (Real.!= (~0.0, 0.0)) ^ "\n");
val () = print ("@@unordered_nan=" ^ Bool.toString (Real.unordered (0.0/0.0, 1.0)) ^ "\n");
val () = print ("@@unordered_finite=" ^ Bool.toString (Real.unordered (1.0, 2.0)) ^ "\n");

(* ---- split / toManExp / fromManExp round-trips incl. specials ---- *)
val () = print ("@@split_neg5p75_w=" ^ (let val {whole,frac} = Real.split (~5.75) in Real.fmt (StringCvt.FIX (SOME 4)) whole ^ ":" ^ Real.fmt (StringCvt.FIX (SOME 4)) frac end) ^ "\n");
val () = print ("@@split_inf=" ^ (let val {whole,frac} = Real.split Real.posInf in Real.toString whole ^ ":" ^ Real.toString frac end) ^ "\n");
val () = print ("@@manexp_neg12=" ^ (let val {man,exp} = Real.toManExp (~12.0) in Real.fmt (StringCvt.FIX (SOME 4)) man ^ ":" ^ Int.toString exp end) ^ "\n");
val () = print ("@@manexp_half=" ^ (let val {man,exp} = Real.toManExp 0.5 in Real.fmt (StringCvt.FIX (SOME 4)) man ^ ":" ^ Int.toString exp end) ^ "\n");
val () = print ("@@manexp_rt_pi=" ^ Bool.toString (Real.== (Real.fromManExp (Real.toManExp 3.14159), 3.14159)) ^ "\n");
val () = print ("@@manexp_inf=" ^ (let val {man,exp} = Real.toManExp Real.posInf in Real.toString man ^ ":" ^ Int.toString exp end) ^ "\n");

(* ---- realFloor/realCeil/realRound/realTrunc on negatives, halves, inf ---- *)
val () = print ("@@realround_neg2p5=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Real.realRound (~2.5)) ^ "\n");
val () = print ("@@realround_neg3p5=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Real.realRound (~3.5)) ^ "\n");
val () = print ("@@realfloor_neg2p5=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Real.realFloor (~2.5)) ^ "\n");
val () = print ("@@realceil_neg2p5=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Real.realCeil (~2.5)) ^ "\n");
val () = print ("@@realtrunc_neg2p5=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Real.realTrunc (~2.5)) ^ "\n");
val () = print ("@@realfloor_inf=" ^ Real.toString (Real.realFloor Real.posInf) ^ "\n");
val () = print ("@@realceil_neginf=" ^ Real.toString (Real.realCeil Real.negInf) ^ "\n");

(* ---- Real.rem edge inputs ---- *)
val () = print ("@@rem_inf_divisor=" ^ Real.fmt (StringCvt.FIX (SOME 4)) (Real.rem (5.3, Real.posInf)) ^ "\n");
val () = print ("@@rem_neg_dividend=" ^ Real.fmt (StringCvt.FIX (SOME 4)) (Real.rem (~5.3, 2.0)) ^ "\n");
val () = print ("@@rem_zero_divisor_nan=" ^ Bool.toString (Real.isNan (Real.rem (5.0, 0.0))) ^ "\n");

(* ---- Math.* on edge inputs ---- *)
val () = print ("@@math_sqrt_negzero=" ^ Real.toString (Math.sqrt (~0.0)) ^ "\n");
val () = print ("@@math_ln_zero=" ^ Real.toString (Math.ln 0.0) ^ "\n");
val () = print ("@@math_ln_neg_isnan=" ^ Bool.toString (Real.isNan (Math.ln (~1.0))) ^ "\n");
val () = print ("@@math_log10_zero=" ^ Real.toString (Math.log10 0.0) ^ "\n");
val () = print ("@@math_pow_00=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Math.pow (0.0, 0.0)) ^ "\n");
val () = print ("@@math_pow_inf_zero=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Math.pow (Real.posInf, 0.0)) ^ "\n");
val () = print ("@@math_pow_zero_neg=" ^ Real.toString (Math.pow (0.0, ~1.0)) ^ "\n");
val () = print ("@@math_exp_inf=" ^ Real.toString (Math.exp Real.posInf) ^ "\n");
val () = print ("@@math_exp_neginf=" ^ Real.fmt (StringCvt.FIX (SOME 1)) (Math.exp Real.negInf) ^ "\n");
val () = print ("@@math_atan2_00=" ^ Real.fmt (StringCvt.FIX (SOME 4)) (Math.atan2 (0.0, 0.0)) ^ "\n");
val () = print ("@@math_atan2_inf=" ^ Real.fmt (StringCvt.FIX (SOME 8)) (Math.atan2 (Real.posInf, Real.posInf)) ^ "\n");
val () = print ("@@math_sqrt_inf=" ^ Real.toString (Math.sqrt Real.posInf) ^ "\n");

(* ============================ Real32 mirrors ============================ *)
val () = print ("@@r32_fmt_gen_posinf=" ^ Real32.fmt (StringCvt.GEN (SOME 6)) Real32.posInf ^ "\n");
val () = print ("@@r32_fmt_fix_nan=" ^ Real32.fmt (StringCvt.FIX (SOME 2)) (0.0/0.0) ^ "\n");
val () = print ("@@r32_tostring_neginf=" ^ Real32.toString Real32.negInf ^ "\n");
val () = print ("@@r32_tostring_nan=" ^ Real32.toString (0.0/0.0) ^ "\n");
val () = print ("@@r32_fromstring_plain=" ^ Real32.fmt (StringCvt.FIX (SOME 4)) (Option.getOpt (Real32.fromString "2.5", ~9.0)) ^ "\n");
val () = print ("@@r32_fromstring_bad=" ^ Bool.toString (Option.isSome (Real32.fromString "xyz")) ^ "\n");
val () = print ("@@r32_signbit_nan=" ^ Bool.toString (Real32.signBit (0.0/0.0)) ^ "\n");
val () = print ("@@r32_copysign_inf_neg=" ^ Real32.toString (Real32.copySign (Real32.posInf, ~1.0)) ^ "\n");
val () = print ("@@r32_samesign_negzero=" ^ Bool.toString (Real32.sameSign (~0.0, 1.0)) ^ "\n");
val () = print ("@@r32_nextafter_eq=" ^ Real32.toString (Real32.nextAfter (5.0, 5.0)) ^ "\n");
val () = print ("@@r32_split_neg5p75=" ^ (let val {whole,frac} = Real32.split (~5.75) in Real32.fmt (StringCvt.FIX (SOME 4)) whole ^ ":" ^ Real32.fmt (StringCvt.FIX (SOME 4)) frac end) ^ "\n");
val () = print ("@@r32_manexp_half=" ^ (let val {man,exp} = Real32.toManExp 0.5 in Real32.fmt (StringCvt.FIX (SOME 4)) man ^ ":" ^ Int.toString exp end) ^ "\n");
val () = print ("@@r32_realround_neg2p5=" ^ Real32.fmt (StringCvt.FIX (SOME 1)) (Real32.realRound (~2.5)) ^ "\n");
val () = print ("@@r32_rem_neg=" ^ Real32.fmt (StringCvt.FIX (SOME 4)) (Real32.rem (~5.3, 2.0)) ^ "\n");
val () = print ("@@r32_ln_zero=" ^ Real32.toString (Real32.Math.ln 0.0) ^ "\n");
val () = print ("@@r32_pow_00=" ^ Real32.fmt (StringCvt.FIX (SOME 1)) (Real32.Math.pow (0.0, 0.0)) ^ "\n");
val () = print ("@@r32_sqrt_negzero=" ^ Real32.toString (Real32.Math.sqrt (~0.0)) ^ "\n");
val () = print ("@@r32_unordered_nan=" ^ Bool.toString (Real32.unordered (0.0/0.0, 1.0)) ^ "\n");
val () = print ("@@r32_qm_nan=" ^ Bool.toString (Real32.?= (0.0/0.0, 5.0)) ^ "\n");
val () = print ("@@r32_compare_nan=" ^ ((case Real32.compare (0.0/0.0, 1.0) of LESS => "L" | EQUAL => "E" | GREATER => "G") handle IEEEReal.Unordered => "UNORDERED" | _ => "OTHER") ^ "\n");
