(* Brainfuck interpreter, in SML, running a BF "Hello World" program.
 *
 * The execution stack is 5-deep:
 *   x86_64 CPU
 *   └─ polyml-rs Rust runtime (the bytecode interpreter we built)
 *      └─ PolyML's SML interpreter (compiled to bytecode)
 *         └─ this SML Brainfuck interpreter
 *            └─ the BF "Hello World" program
 *
 * Tape: 30000 byte cells. Pointer: 0..29999.
 * Loops [...]: pre-compute matching bracket positions for jumps.
 *
 * Run via:
 *   ./target/release/poly run --max-steps 100000000 /tmp/basis_loaded < demos/bf.sml *)

fun compileBrackets code =
    let val n = String.size code
        val matches = Array.array (n, ~1)
        fun loop i stack =
            if i >= n then ()
            else
                let val c = String.sub (code, i)
                in if c = #"[" then loop (i + 1) (i :: stack)
                   else if c = #"]" then
                     case stack of
                         [] => raise Fail "unmatched ]"
                       | open_pos :: rest =>
                         (Array.update (matches, open_pos, i);
                          Array.update (matches, i, open_pos);
                          loop (i + 1) rest)
                   else loop (i + 1) stack
                end
        val () = loop 0 []
    in matches end;

fun run code =
    let val n = String.size code
        val matches = compileBrackets code
        val tape = Array.array (30000, 0)
        val out = ref []
        fun step (pc, ptr) =
            if pc >= n then ()
            else
                let val c = String.sub (code, pc)
                in case c of
                       #"+" => (Array.update (tape, ptr,
                                  (Array.sub (tape, ptr) + 1) mod 256);
                                step (pc + 1, ptr))
                     | #"-" => (Array.update (tape, ptr,
                                  (Array.sub (tape, ptr) - 1 + 256) mod 256);
                                step (pc + 1, ptr))
                     | #">" => step (pc + 1, ptr + 1)
                     | #"<" => step (pc + 1, ptr - 1)
                     | #"." => (out := Array.sub (tape, ptr) :: !out;
                                step (pc + 1, ptr))
                     | #"[" => (if Array.sub (tape, ptr) = 0
                                then step (Array.sub (matches, pc) + 1, ptr)
                                else step (pc + 1, ptr))
                     | #"]" => (if Array.sub (tape, ptr) <> 0
                                then step (Array.sub (matches, pc) + 1, ptr)
                                else step (pc + 1, ptr))
                     | _    => step (pc + 1, ptr)
                end
        val () = step (0, 0)
    in String.implode (List.rev (List.map (chr o Word.toInt o Word.fromInt) (!out))) end;

(* Hello World in Brainfuck. *)
val helloworld = "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.";
val result = run helloworld;
print "Brainfuck interpreter (in SML) running 'Hello World' BF program:\n";
print ("  Output: \"" ^ result ^ "\"\n");
print ("  Length: " ^ Int.toString (String.size result) ^ " chars\n");
