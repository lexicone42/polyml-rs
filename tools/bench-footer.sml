(* ---- shared bench driver (identical across all bench_*.sml) ----
 * No env vars  -> faithfulness mode: prints @@<bench_name>=<checksum> at the
 *                 SMALL default size (deterministic; the differential sweep
 *                 compares this line byte-for-byte against upstream).
 * BENCH_TIME=1 -> timing mode: runs BENCH_REPS reps at size BENCH_N under an
 *                 in-SML CPU Timer, prints @@time_ms / @@reps / @@n / @@checksum.
 *)
local
  fun getenvInt name dflt =
      case OS.Process.getEnv name of
          SOME s => (case Int.fromString s of SOME i => i | NONE => dflt)
        | NONE => dflt
  val n0     = getenvInt "BENCH_N" default_n
  val reps   = getenvInt "BENCH_REPS" 1
  val timing = Option.isSome (OS.Process.getEnv "BENCH_TIME")
  fun repeat k = if k <= 1 then checksum (bench n0)
                 else (checksum (bench n0); repeat (k - 1))
in
  val () =
    if timing then
      let
        val t  = Timer.startCPUTimer ()
        val cs = repeat reps
        val {usr, sys} = Timer.checkCPUTimer t
        val ms = Time.toMilliseconds usr + Time.toMilliseconds sys
      in
        print ("@@bench=" ^ bench_name ^ "\n");
        print ("@@time_ms=" ^ LargeInt.toString ms ^ "\n");
        print ("@@reps=" ^ Int.toString reps ^ "\n");
        print ("@@n=" ^ Int.toString n0 ^ "\n");
        print ("@@checksum=" ^ cs ^ "\n")
      end
    else
      print ("@@" ^ bench_name ^ "=" ^ checksum (bench n0) ^ "\n")
end;
