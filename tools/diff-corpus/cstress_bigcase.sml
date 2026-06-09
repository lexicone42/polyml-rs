(* 1. case over 16 integer constants returning distinct primes; sum over all + default *)
local
  fun sel n =
    case n of
        0 => 2 | 1 => 3 | 2 => 5 | 3 => 7 | 4 => 11 | 5 => 13
      | 6 => 17 | 7 => 19 | 8 => 23 | 9 => 29 | 10 => 31 | 11 => 37
      | 12 => 41 | 13 => 43 | 14 => 47 | 15 => 53 | _ => ~1
  fun loop (i, acc) = if i > 17 then acc else loop (i+1, acc + sel i)
in
  val () = print ("@@case16sum=" ^ Int.toString (loop (0, 0)) ^ "\n")
end

(* 2. case over 40 integer constants — beyond a single small jump table; spot-check several + default *)
local
  fun f n =
    case n of
        0=>100|1=>101|2=>102|3=>103|4=>104|5=>105|6=>106|7=>107|8=>108|9=>109
      |10=>110|11=>111|12=>112|13=>113|14=>114|15=>115|16=>116|17=>117|18=>118|19=>119
      |20=>120|21=>121|22=>122|23=>123|24=>124|25=>125|26=>126|27=>127|28=>128|29=>129
      |30=>130|31=>131|32=>132|33=>133|34=>134|35=>135|36=>136|37=>137|38=>138|39=>139
      | _ => ~7
  val pts = [0,1,15,16,17,31,32,33,38,39,40,41,~1]
  val s = foldl (fn (x,a) => a + f x) 0 pts
in
  val () = print ("@@case40sum=" ^ Int.toString s ^ "\n")
end

(* 3. nested case: outer over 8, inner over 8, returns a function of both *)
local
  fun g (a, b) =
    case a of
        0 => (case b of 0=>0|1=>1|2=>2|3=>3|4=>4|5=>5|6=>6|_=>7)
      | 1 => (case b of 0=>10|1=>11|2=>12|3=>13|4=>14|5=>15|6=>16|_=>17)
      | 2 => (case b of 0=>20|1=>21|2=>22|3=>23|4=>24|5=>25|6=>26|_=>27)
      | 3 => (case b of 0=>30|1=>31|2=>32|3=>33|4=>34|5=>35|6=>36|_=>37)
      | 4 => (case b of 0=>40|1=>41|2=>42|3=>43|4=>44|5=>45|6=>46|_=>47)
      | 5 => (case b of 0=>50|1=>51|2=>52|3=>53|4=>54|5=>55|6=>56|_=>57)
      | 6 => (case b of 0=>60|1=>61|2=>62|3=>63|4=>64|5=>65|6=>66|_=>67)
      | _ => (case b of 0=>70|1=>71|2=>72|3=>73|4=>74|5=>75|6=>76|_=>77)
  fun acc (i, s) =
    if i > 63 then s
    else acc (i+1, s + g (i div 8, i mod 8))
in
  val () = print ("@@nestedcase=" ^ Int.toString (acc (0, 0)) ^ "\n")
end

(* 4. case on a datatype with 14 constructors *)
local
  datatype color =
      C0 | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | C10 | C11 | C12 | C13
  fun rank c =
    case c of
        C0=>0|C1=>1|C2=>2|C3=>3|C4=>4|C5=>5|C6=>6
      | C7=>7|C8=>8|C9=>9|C10=>10|C11=>11|C12=>12|C13=>13
  val all = [C13,C0,C7,C3,C12,C1,C9,C6,C11,C2,C10,C4,C8,C5]
  val s = foldl (fn (c,a) => (a * 31 + rank c) mod 1000000007) 0 all
in
  val () = print ("@@dtcase14=" ^ Int.toString s ^ "\n")
end

(* 5. hand-written state machine / lexer over Char with a big case *)
local
  datatype tok = TNUM | TID | TWS | TOP | TOTHER
  fun classify ch =
    case ch of
        #"0"=>TNUM|(#"1")=>TNUM|(#"2")=>TNUM|(#"3")=>TNUM|(#"4")=>TNUM
      | #"5"=>TNUM|(#"6")=>TNUM|(#"7")=>TNUM|(#"8")=>TNUM|(#"9")=>TNUM
      | #" "=>TWS|(#"\t")=>TWS|(#"\n")=>TWS
      | #"+"=>TOP|(#"-")=>TOP|(#"*")=>TOP|(#"/")=>TOP
      | c => if (c >= #"a" andalso c <= #"z") orelse (c >= #"A" andalso c <= #"Z")
             then TID else TOTHER
  fun tcode TNUM=1|tcode TID=2|tcode TWS=3|tcode TOP=4|tcode TOTHER=5
  val src = "x1 + 23*foo - 9 / Bar7 ?!"
  fun scan (i, acc) =
    if i >= String.size src then acc
    else scan (i+1, (acc * 6 + tcode (classify (String.sub (src, i)))) mod 1000000007)
in
  val () = print ("@@lexer=" ^ Int.toString (scan (0, 0)) ^ "\n")
end

(* 6. dispatch table: case selecting one of several closures, applied to an arg *)
local
  fun dispatch op_ =
    case op_ of
        0 => (fn x => x + 1)
      | 1 => (fn x => x - 1)
      | 2 => (fn x => x * 2)
      | 3 => (fn x => x * x)
      | 4 => (fn x => x + 100)
      | 5 => (fn x => x - 100)
      | 6 => (fn x => if x mod 2 = 0 then x div 2 else 3*x+1)
      | 7 => (fn x => ~x)
      | _ => (fn x => x)
  fun run (i, x) =
    if i > 7 then x else run (i+1, dispatch i x)
in
  val () = print ("@@dispatch=" ^ Int.toString (run (0, 5)) ^ "\n")
end

(* 7. case on negative + positive constants mixed (jump table offset stress) *)
local
  fun f n =
    case n of
        ~5 => 500 | ~4 => 400 | ~3 => 300 | ~2 => 200 | ~1 => 100
      | 0 => 0
      | 1 => ~100 | 2 => ~200 | 3 => ~300 | 4 => ~400 | 5 => ~500
      | _ => 999999
  val pts = [~6,~5,~4,~3,~2,~1,0,1,2,3,4,5,6]
  val s = foldl (fn (x,a) => a + f x) 0 pts
in
  val () = print ("@@negcase=" ^ Int.toString s ^ "\n")
end

(* 8. sparse case over large widely-spaced constants (forces compare-chain, not table) *)
local
  fun f n =
    case n of
        1 => 11 | 100 => 22 | 5000 => 33 | 99999 => 44
      | 1000000 => 55 | 123456789 => 66 | ~777 => 77
      | _ => 0
  val pts = [1,2,100,99,5000,99999,1000000,123456789,~777,~778,0]
  val s = foldl (fn (x,a) => a * 7 + f x) 0 pts
in
  val () = print ("@@sparse=" ^ Int.toString s ^ "\n")
end

(* 9. recursive descent expression evaluator with big char case (real optimizer stress) *)
local
  (* evaluate fully-parenthesized + digit expression, single-pass with explicit stack *)
  exception Bad
  fun digit c = Char.ord c - Char.ord #"0"
  (* simple left-to-right eval of d (op d)* with op in +-* , no precedence *)
  fun eval s =
    let
      fun step (i, acc, pend) =
        if i >= String.size s then acc
        else
          let val c = String.sub (s, i) in
            case c of
                #"+" => step (i+1, acc, SOME (op +))
              | #"-" => step (i+1, acc, SOME (op -))
              | #"*" => step (i+1, acc, SOME (op * ))
              | #" " => step (i+1, acc, pend)
              | _ =>
                  if c >= #"0" andalso c <= #"9" then
                    let val d = digit c in
                      case pend of
                          NONE => step (i+1, d, NONE)
                        | SOME f => step (i+1, f (acc, d), NONE)
                    end
                  else raise Bad
          end
    in step (0, 0, NONE) end
  val r1 = eval "1 + 2 * 3 - 4"   (* ((1+2)*3)-4 = 5 *)
  val r2 = eval "9 - 1 - 1 - 1"   (* 6 *)
  val r3 = eval "2 * 2 * 2 * 2"   (* 16 *)
in
  val () = print ("@@eval=" ^ Int.toString (r1 * 10000 + r2 * 100 + r3) ^ "\n")
end

(* 10. big case returning datatype, then dispatch on it (two-stage CASE) *)
local
  datatype action = Push of int | Pop | Dup | Add | Swap | Nop
  fun decode n =
    case n of
        0 => Push 1 | 1 => Push 2 | 2 => Push 3 | 3 => Push 5 | 4 => Push 8
      | 5 => Pop | 6 => Dup | 7 => Add | 8 => Swap | 9 => Nop
      | _ => Nop
  fun exec (a, stk) =
    case a of
        Push v => v :: stk
      | Pop => (case stk of _::t => t | [] => [])
      | Dup => (case stk of h::t => h::h::t | [] => [])
      | Add => (case stk of a::b::t => (a+b)::t | s => s)
      | Swap => (case stk of a::b::t => b::a::t | s => s)
      | Nop => stk
  val prog = [0,1,7,2,7,6,3,7,8,4,7]  (* sequence of opcodes *)
  val finalStk = foldl (fn (n, s) => exec (decode n, s)) [] prog
  val s = foldl (fn (x,a) => a*100 + x) 0 finalStk
in
  val () = print ("@@vm=" ^ Int.toString s ^ "\n")
end

(* 11. case where all branches are exactly contiguous 0..19 (dense 20-way table) *)
local
  fun fib20 n =
    case n of
        0=>0|1=>1|2=>1|3=>2|4=>3|5=>5|6=>8|7=>13|8=>21|9=>34
      |10=>55|11=>89|12=>144|13=>233|14=>377|15=>610|16=>987|17=>1597|18=>2584|19=>4181
      | _ => ~1
  fun loop (i, s) = if i >= 22 then s else loop (i+1, s + fib20 i)
in
  val () = print ("@@dense20=" ^ Int.toString (loop (0, 0)) ^ "\n")
end

(* 12. nested datatype case with payloads — Word8-style state machine on a string *)
local
  datatype st = Start | InNum | InWord | Done of int
  fun next (s, c) =
    case (s, c) of
        (Start, d) => if d >= #"0" andalso d <= #"9" then InNum
                      else if d = #"!" then Done 9 else InWord
      | (InNum, d) => if d >= #"0" andalso d <= #"9" then InNum
                      else if d = #"!" then Done 1 else InWord
      | (InWord, d) => if d = #"!" then Done 2 else InWord
      | (Done k, _) => Done k
  fun stcode Start=0|stcode InNum=1|stcode InWord=2|stcode (Done k)= 100+k
  fun drive str =
    let
      fun go (i, s) =
        if i >= String.size str then s
        else go (i+1, next (s, String.sub (str, i)))
    in stcode (go (0, Start)) end
  val a = drive "123abc"
  val b = drive "42!"
  val c = drive "hello!"
  val d = drive "!"
in
  val () = print ("@@smachine=" ^ Int.toString (a*1000000 + b*10000 + c*100 + d) ^ "\n")
end

(* 13. andb-shape: if isShort i andalso isShort j then word-path else rts-path.
       Replicate the exact mis-compiled shape with RunCall.isShort over a big case
       of (short,short),(short,big),(big,short),(big,big) inputs. IntInf typing. *)
local
  val big1 : IntInf.int = 4611686018427387904     (* 2^62, not short on 63-bit *)
  val big2 : IntInf.int = ~4611686018427387905
  fun myAndb (i:IntInf.int, j:IntInf.int) : IntInf.int =
    if RunCall.isShort i andalso RunCall.isShort j
    then IntInf.andb (i, j)   (* both short: word-path; the mis-compiled branch *)
    else IntInf.andb (i, j)   (* rts-path *)
  val pairs = [ (12, 10), (255, 16), (big1, 7), (7, big1),
                (big1, big2), (~1, 255), (big2, 1), (0, big1) ]
  fun show (a, b) = IntInf.toString (myAndb (a, b))
  val s = String.concatWith "," (map show pairs)
in
  val () = print ("@@andbshape=" ^ s ^ "\n")
end

(* 14. case over result of a computation feeding into another case (chained tables) *)
local
  fun stage1 n =
    case n mod 7 of
        0 => 3 | 1 => 1 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 9 | _ => 2
  fun stage2 m =
    case m of
        1 => 100 | 2 => 200 | 3 => 300 | 4 => 400 | 5 => 500
      | 6 => 600 | 7 => 700 | 8 => 800 | 9 => 900 | _ => 0
  fun loop (i, s) =
    if i >= 50 then s
    else loop (i+1, s + stage2 (stage1 i))
in
  val () = print ("@@chain=" ^ Int.toString (loop (0, 0)) ^ "\n")
end

(* 15. exception-laden big case: some branches raise, caught and mapped *)
local
  exception E1 and E2 and E3
  fun risky n =
    case n of
        0 => 10
      | 1 => raise E1
      | 2 => 20
      | 3 => raise E2
      | 4 => 40
      | 5 => raise E3
      | 6 => 60
      | 7 => raise E1
      | 8 => 80
      | _ => 0
  fun safe n =
    (risky n) handle E1 => ~1 | E2 => ~2 | E3 => ~3
  fun loop (i, s) = if i > 9 then s else loop (i+1, (s*1000 + (1000 + safe i)) mod 1000000007)
in
  val () = print ("@@exncase=" ^ Int.toString (loop (0, 0)) ^ "\n")
end

(* 16. wide Char dispatch building a hex/escape encoder via case on every category *)
local
  fun enc c =
    case c of
        #"\\" => "\\\\"
      | #"\"" => "\\q"
      | #"\n" => "\\n"
      | #"\t" => "\\t"
      | #"<"  => "&lt;"
      | #">"  => "&gt;"
      | #"&"  => "&amp;"
      | _ => str c
  val src = "a<b>&\"c\\\nd\te"
  val out = String.concat (map enc (String.explode src))
in
  val () = print ("@@encoder=" ^ Int.toString (String.size out) ^ ":" ^ out ^ "\n")
end
