(* diff-corpus category: os_process + date (Wave 1a — real system/Date/errorMsg, 2026-07-01) *)
(* Everything here is deterministic across engines on the same machine:
   fixed times, fixed commands, same TZ/locale for both sides. *)

(* OS.Process.system: real execution + honest status mapping. *)
val () = print ("@@system_true=[" ^ Bool.toString (OS.Process.isSuccess (OS.Process.system "true")) ^ "]\n");
val () = print ("@@system_false=[" ^ Bool.toString (OS.Process.isSuccess (OS.Process.system "false")) ^ "]\n");
val () = print ("@@system_exit3=[" ^ Bool.toString (OS.Process.isSuccess (OS.Process.system "exit 3")) ^ "]\n");
val () = print ("@@system_echo=[" ^ Bool.toString (OS.Process.isSuccess (OS.Process.system "echo @@from_child")) ^ "]\n");

(* Date: strftime + UTC conversion of fixed instants. *)
val () = print ("@@date_fmt_epoch1d=[" ^ Date.fmt "%Y-%m-%d %H:%M:%S" (Date.fromTimeUniv (Time.fromReal 86400.0)) ^ "]\n");
val () = print ("@@date_fmt_2020=[" ^ Date.fmt "%a %j %H" (Date.fromTimeUniv (Time.fromReal 1577836800.0)) ^ "]\n");
val () = print ("@@date_toString_univ=[" ^ Date.toString (Date.fromTimeUniv (Time.fromReal 0.0)) ^ "]\n");
(* Local conversions: TZ-dependent but IDENTICAL for both engines on one box. *)
val () = print ("@@date_local_epoch=[" ^ Date.toString (Date.fromTimeLocal (Time.fromReal 0.0)) ^ "]\n");
val () = print ("@@date_localoffset=[" ^ Time.toString (Date.localOffset ()) ^ "]\n");

(* The IO error chain: message + errno decoding (real strerror). *)
val () =
    (TextIO.openIn "/nonexistent_polyml_diff_probe"; print "@@open_missing=[NO_RAISE]\n")
        handle IO.Io {cause = OS.SysErr (m, SOME e), ...} =>
                   print ("@@open_missing=[" ^ m ^ "/" ^ OS.errorMsg e ^ "]\n")
             | IO.Io _ => print "@@open_missing=[IOIO_NO_SYSERR]\n";
val () = print ("@@errormsg_shape=[" ^ Bool.toString (size (OS.errorMsg 2) > 0) ^ "]\n");
