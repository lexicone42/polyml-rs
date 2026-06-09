(* 1. Recursive-descent arithmetic expression parser + evaluator.
   Grammar: expr = term (('+'|'-') term)* ; term = factor (('*'|'/') factor)* ;
   factor = number | '(' expr ')'. Evaluates a fixed string deterministically. *)
local
  val src = "2+3*4-(10-6)/2+7*(1+1)"
  val cs  = String.explode src
  (* token stream as a ref to a char list *)
  val rest = ref cs
  fun peek () = case !rest of c::_ => SOME c | [] => NONE
  fun adv () = case !rest of _::t => rest := t | [] => ()
  fun isDig c = Char.isDigit c
  fun number acc =
        case peek () of
            SOME c => if isDig c
                      then (adv (); number (acc*10 + (Char.ord c - Char.ord #"0")))
                      else acc
          | NONE => acc
  fun expr () =
        let val t0 = term ()
            fun loop a =
                case peek () of
                    SOME #"+" => (adv (); loop (a + term ()))
                  | SOME #"-" => (adv (); loop (a - term ()))
                  | _ => a
        in loop t0 end
  and term () =
        let val f0 = factor ()
            fun loop a =
                case peek () of
                    SOME #"*" => (adv (); loop (a * factor ()))
                  | SOME #"/" => (adv (); loop (a div factor ()))
                  | _ => a
        in loop f0 end
  and factor () =
        case peek () of
            SOME #"(" => (adv (); let val v = expr () in (adv (); v) end)
          | SOME c => if isDig c then number 0 else 0
          | NONE => 0
  val result = expr ()
in
  val () = print ("@@p1_expr_eval=" ^ Int.toString result ^ "\n")
end

(* 2. Tiny stack-machine interpreter. Opcodes manipulate an int stack;
   exercises datatype dispatch + a big case + closures over a ref stack. *)
local
  datatype opc = PUSH of int | ADD | SUB | MUL | DUP | SWAP | NEG
  val prog = [PUSH 5, PUSH 3, ADD, DUP, MUL, PUSH 7, SUB, NEG, PUSH 100, SWAP, SUB]
  fun run (ops, stk) =
        case ops of
            [] => stk
          | (PUSH n)::r => run (r, n::stk)
          | ADD::r => (case stk of a::b::t => run (r, (a+b)::t) | _ => stk)
          | SUB::r => (case stk of a::b::t => run (r, (b-a)::t) | _ => stk)
          | MUL::r => (case stk of a::b::t => run (r, (a*b)::t) | _ => stk)
          | DUP::r => (case stk of a::t => run (r, a::a::t) | _ => stk)
          | SWAP::r => (case stk of a::b::t => run (r, b::a::t) | _ => stk)
          | NEG::r => (case stk of a::t => run (r, (~a)::t) | _ => stk)
  val top = case run (prog, []) of x::_ => x | [] => ~999999
in
  val () = print ("@@p2_stackmachine=" ^ Int.toString top ^ "\n")
end

(* 3. RPN evaluator over a token list, with division and error handling. *)
local
  exception RpnErr
  val toks = ["3","4","+","5","*","2","/","9","-","11","+"]
  fun isNum s = List.all Char.isDigit (String.explode s)
  fun ev (t, stk) =
        if isNum t then (valOf (Int.fromString t))::stk
        else case (t, stk) of
                 ("+", a::b::r) => (b+a)::r
               | ("-", a::b::r) => (b-a)::r
               | ("*", a::b::r) => (b*a)::r
               | ("/", a::b::r) => (b div a)::r
               | _ => raise RpnErr
  val final = List.foldl ev [] toks
  val ans = case final of [x] => x | _ => raise RpnErr
in
  val () = print ("@@p3_rpn=" ^ Int.toString ans ^ "\n")
end

(* 4. JSON-ish tokenizer counting token kinds over a fixed string.
   Exercises a char-driven state walk + multiple accumulators. *)
local
  val s = "{\"a\":[1,22,333],\"b\":{\"c\":true,\"d\":false},\"e\":null}"
  val cs = String.explode s
  fun classify (cs, braces, brackets, colons, commas, digits) =
        case cs of
            [] => (braces, brackets, colons, commas, digits)
          | c::r =>
              let val b1 = if c = #"{" orelse c = #"}" then braces+1 else braces
                  val b2 = if c = #"[" orelse c = #"]" then brackets+1 else brackets
                  val co = if c = #":" then colons+1 else colons
                  val cm = if c = #"," then commas+1 else commas
                  val dg = if Char.isDigit c then digits+1 else digits
              in classify (r, b1, b2, co, cm, dg) end
  val (br, bk, co, cm, dg) = classify (cs, 0, 0, 0, 0, 0)
  val total = br + bk + co + cm + dg
in
  val () = print ("@@p4_jsontok=" ^ Int.toString br ^ "," ^ Int.toString bk ^ ","
                  ^ Int.toString co ^ "," ^ Int.toString cm ^ "," ^ Int.toString dg
                  ^ ";" ^ Int.toString total ^ "\n")
end

(* 5. Fibonacci with a memo table (array), then sum a window. *)
local
  val n = 60
  val memo = Array.array (n+1, 0)
  val () = Array.update (memo, 0, 0)
  val () = Array.update (memo, 1, 1)
  fun fill i = if i > n then ()
               else (Array.update (memo, i,
                       Array.sub (memo, i-1) + Array.sub (memo, i-2));
                     fill (i+1))
  val () = fill 2
  (* sum fib(50..60) *)
  fun sumWin (i, acc) = if i > 60 then acc
                        else sumWin (i+1, acc + Array.sub (memo, i))
  val s = sumWin (50, 0)
in
  val () = print ("@@p5_fibwin=" ^ Int.toString (Array.sub (memo, 60))
                  ^ ";" ^ Int.toString s ^ "\n")
end

(* 6. gcd/lcm via Euclid over a list; chain-fold with overflow-safe-ish values. *)
local
  fun gcd (a, 0) = a
    | gcd (a, b) = gcd (b, a mod b)
  fun lcm (a, b) = (a div gcd (a, b)) * b
  val nums = [12, 18, 24, 30, 42, 56, 84]
  val g = List.foldl (fn (x, acc) => gcd (acc, x)) (hd nums) (tl nums)
  val l = List.foldl (fn (x, acc) => lcm (acc, x)) (hd nums) (tl nums)
in
  val () = print ("@@p6_gcdlcm=" ^ Int.toString g ^ ";" ^ Int.toString l ^ "\n")
end

(* 7. Prime factorization with multiplicity, formatted as p^e*p^e. *)
local
  fun factor (n, d, acc) =
        if n <= 1 then List.rev acc
        else if n mod d = 0
        then let fun cnt (m, k) = if m mod d = 0 then cnt (m div d, k+1) else (m, k)
                 val (m', k) = cnt (n, 0)
             in factor (m', d+1, (d, k)::acc) end
        else factor (n, d+1, acc)
  val fs = factor (360360, 2, [])
  fun show [] = ""
    | show [(p,e)] = Int.toString p ^ "^" ^ Int.toString e
    | show ((p,e)::r) = Int.toString p ^ "^" ^ Int.toString e ^ "*" ^ show r
in
  val () = print ("@@p7_factor=" ^ show fs ^ "\n")
end

(* 8. Collatz: longest chain length among starts 1..10000. *)
local
  fun steps (n, c) = if n = 1 then c
                     else if n mod 2 = 0 then steps (n div 2, c+1)
                     else steps (3*n+1, c+1)
  fun search (i, bestN, bestLen) =
        if i > 10000 then (bestN, bestLen)
        else let val l = steps (i, 0)
             in if l > bestLen then search (i+1, i, l)
                else search (i+1, bestN, bestLen) end
  val (bn, bl) = search (1, 1, 0)
in
  val () = print ("@@p8_collatz=" ^ Int.toString bn ^ ";" ^ Int.toString bl ^ "\n")
end

(* 9. Run-length encode then decode a string; verify round-trip + report lengths. *)
local
  val orig = "aaaabbbccccccdeeeeeffffffffffg"
  fun rle [] = []
    | rle (c::cs) =
        let fun go (x, k, []) = [(x, k)]
              | go (x, k, y::ys) = if y = x then go (x, k+1, ys)
                                   else (x, k) :: go (y, 1, ys)
        in go (c, 1, cs) end
  val encoded = rle (String.explode orig)
  fun decode pairs =
        String.implode (List.concat (map (fn (c, k) => List.tabulate (k, fn _ => c)) pairs))
  val decoded = decode encoded
  val ok = (decoded = orig)
in
  val () = print ("@@p9_rle=" ^ Int.toString (length encoded) ^ ";"
                  ^ Int.toString (String.size decoded) ^ ";"
                  ^ (if ok then "OK" else "BAD") ^ "\n")
end

(* 10. The andb-shape itself, generalized: a hand-written int bitwise-AND that
   uses the "if isShort both then word path else bignum path" idiom. This is the
   exact optimizer shape the original bug lived in. Cross small/large operands. *)
local
  fun myAndb (i: int, j: int) : int =
        if RunCall.isShort i andalso RunCall.isShort j
        then (* word path: emulate with mod arithmetic on nonneg small ints *)
             let fun loop (a, b, bit, acc) =
                       if bit > 62 then acc
                       else let val ba = a mod 2 and bb = b mod 2
                                val nb = if ba = 1 andalso bb = 1 then acc + bit else acc
                            in loop (a div 2, b div 2, bit*2, nb) end
             in loop (i, j, 1, 0) end
        else IntInf.toInt (IntInf.andb (IntInf.fromInt i, IntInf.fromInt j))
  (* mix small and large operands; big > maxInt so isShort is false *)
  val big = valOf Int.maxInt
  val r1 = myAndb (0xF0F0, 0x0FF0)        (* small,small *)
  val r2 = myAndb (big, 0xFFFF)           (* large,small — the bug case *)
  val r3 = myAndb (0xABCD, big)           (* small,large *)
in
  val () = print ("@@p10_andbshape=" ^ Int.toString r1 ^ ";"
                  ^ Int.toString r2 ^ ";" ^ Int.toString r3 ^ "\n")
end

(* 11. Mutual recursion: a tiny tokenizer+parser for a balanced-paren / nesting
   depth checker, returning max depth and whether balanced. *)
local
  val s = "(()((())())()(()))"
  fun walk ([], depth, maxd, ok) = (maxd, ok andalso depth = 0)
    | walk (c::cs, depth, maxd, ok) =
        case c of
            #"(" => let val d = depth + 1
                    in walk (cs, d, Int.max (maxd, d), ok) end
          | #")" => let val d = depth - 1
                    in walk (cs, d, maxd, ok andalso d >= 0) end
          | _ => walk (cs, depth, maxd, ok)
  val (md, bal) = walk (String.explode s, 0, 0, true)
in
  val () = print ("@@p11_parens=" ^ Int.toString md ^ ";"
                  ^ (if bal then "balanced" else "unbalanced") ^ "\n")
end

(* 12. Higher-order pipeline: build a list, map/filter/fold with closures that
   capture mutable state, plus a curried adder factory. *)
local
  val xs = List.tabulate (50, fn i => i + 1)
  fun mkAdder k = fn x => x + k
  val add7 = mkAdder 7
  val counter = ref 0
  val mapped = map (fn x => (counter := !counter + 1; add7 (x * x))) xs
  val evens = List.filter (fn x => x mod 2 = 0) mapped
  val total = List.foldl (op +) 0 evens
in
  val () = print ("@@p12_pipeline=" ^ Int.toString (!counter) ^ ";"
                  ^ Int.toString (length evens) ^ ";" ^ Int.toString total ^ "\n")
end

(* 13. Deterministic real arithmetic: Newton's method for sqrt + a small series.
   Reals formatted via Real.fmt FIX 8 so output is byte-stable. *)
local
  fun newton (x, guess, n) =
        if n = 0 then guess
        else newton (x, 0.5 * (guess + x / guess), n - 1)
  val r1 = newton (2.0, 1.0, 20)
  val r2 = newton (16.0, 4.0, 20)
  (* Leibniz partial sum for pi/4 *)
  fun leib (k, sign, acc) =
        if k >= 200 then acc
        else leib (k+1, ~sign, acc + sign / (real (2*k+1)))
  val pi4 = leib (0, 1.0, 0.0)
  fun fmt r = Real.fmt (StringCvt.FIX (SOME 8)) r
in
  val () = print ("@@p13_reals=" ^ fmt r1 ^ ";" ^ fmt r2 ^ ";" ^ fmt (pi4*4.0) ^ "\n")
end

(* 14. Sieve of Eratosthenes via a bool array; count primes + sum + nth prime. *)
local
  val n = 5000
  val sieve = Array.array (n+1, true)
  val () = Array.update (sieve, 0, false)
  val () = Array.update (sieve, 1, false)
  fun mark (p, m) = if m > n then ()
                    else (Array.update (sieve, m, false); mark (p, m+p))
  fun run p = if p*p > n then ()
              else (if Array.sub (sieve, p) then mark (p, p*p) else ();
                    run (p+1))
  val () = run 2
  fun tally (i, cnt, sum, last) =
        if i > n then (cnt, sum, last)
        else if Array.sub (sieve, i) then tally (i+1, cnt+1, sum+i, i)
        else tally (i+1, cnt, sum, last)
  val (cnt, sum, last) = tally (2, 0, 0, 0)
in
  val () = print ("@@p14_sieve=" ^ Int.toString cnt ^ ";"
                  ^ Int.toString sum ^ ";" ^ Int.toString last ^ "\n")
end

(* 15. Binary tree: insert a fixed sequence into a BST, then in-order traversal
   sum + tree height + node count. Datatype recursion + structural matching. *)
local
  datatype tree = Leaf | Node of tree * int * tree
  fun ins (Leaf, x) = Node (Leaf, x, Leaf)
    | ins (Node (l, v, r), x) =
        if x < v then Node (ins (l, x), v, r)
        else if x > v then Node (l, v, ins (r, x))
        else Node (l, v, r)
  val seq = [50, 30, 70, 20, 40, 60, 80, 10, 25, 35, 45, 55, 65, 75, 85]
  val t = List.foldl (fn (x, acc) => ins (acc, x)) Leaf seq
  fun height Leaf = 0
    | height (Node (l, _, r)) = 1 + Int.max (height l, height r)
  fun count Leaf = 0
    | count (Node (l, _, r)) = 1 + count l + count r
  fun inorderSum Leaf = 0
    | inorderSum (Node (l, v, r)) = inorderSum l + v + inorderSum r
in
  val () = print ("@@p15_bst=" ^ Int.toString (count t) ^ ";"
                  ^ Int.toString (height t) ^ ";" ^ Int.toString (inorderSum t) ^ "\n")
end

(* 16. Word/bitwise stress: pack/unpack via Word ops, shifts, andb/orb/xorb.
   Exercises the word-path codegen directly (the bug's cousin path). *)
local
  fun packRGBA (r, g, b, a) =
        Word.orb (Word.<< (Word.fromInt r, 0w24),
        Word.orb (Word.<< (Word.fromInt g, 0w16),
        Word.orb (Word.<< (Word.fromInt b, 0w8),
                  Word.fromInt a)))
  val px = packRGBA (0x12, 0x34, 0x56, 0x78)
  fun chan (w, sh) = Word.toInt (Word.andb (Word.>> (w, sh), 0wxFF))
  val rr = chan (px, 0w24)
  val gg = chan (px, 0w16)
  val bb = chan (px, 0w8)
  val aa = chan (px, 0w0)
  val x = Word.xorb (px, 0wxFFFFFFFF)
  val back = Word.xorb (x, 0wxFFFFFFFF)
  val roundtrip = (back = px)
in
  val () = print ("@@p16_bits=" ^ Int.toString rr ^ "," ^ Int.toString gg ^ ","
                  ^ Int.toString bb ^ "," ^ Int.toString aa ^ ";"
                  ^ Word.toString px ^ ";" ^ (if roundtrip then "OK" else "BAD") ^ "\n")
end
