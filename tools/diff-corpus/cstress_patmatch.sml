(* 1: expr datatype evaluator — nested constructor case, recursion *)
local
  datatype expr = Num of int
                | Add of expr * expr
                | Sub of expr * expr
                | Mul of expr * expr
                | Neg of expr
                | IfZ of expr * expr * expr
  fun eval e =
    case e of
        Num n => n
      | Add (a, b) => eval a + eval b
      | Sub (a, b) => eval a - eval b
      | Mul (a, b) => eval a * eval b
      | Neg a => ~(eval a)
      | IfZ (c, t, f) => if eval c = 0 then eval t else eval f
  val prog = Add (Mul (Num 3, Num 4),
                  IfZ (Sub (Num 5, Num 5),
                       Neg (Num 7),
                       Num 100))
in
  val () = print ("@@eval1=" ^ Int.toString (eval prog) ^ "\n")
end

(* 2: deep nested constructor patterns on option/list of pairs *)
local
  fun classify x =
    case x of
        NONE => 0
      | SOME [] => 1
      | SOME [(a, b)] => a + b
      | SOME ((a, b) :: (c, d) :: _) => a * b + c * d
  val r1 = classify NONE
  val r2 = classify (SOME [])
  val r3 = classify (SOME [(3, 4)])
  val r4 = classify (SOME [(2, 5), (3, 6), (9, 9)])
in
  val () = print ("@@classify=" ^ Int.toString (r1+r2+r3+r4) ^ "\n")
end

(* 3: as-patterns + layered list pattern, dedup-ish *)
local
  fun compress xs =
    case xs of
        [] => []
      | [x] => [x]
      | (x :: (rest as (y :: _))) =>
          if x = y then compress rest else x :: compress rest
  val out = compress [1,1,2,3,3,3,4,1,1]
in
  val () = print ("@@compress=" ^ String.concatWith "," (map Int.toString out) ^ "\n")
end

(* 4: record patterns with field punning + layered tuple *)
local
  type pt = { x : int, y : int, tag : string }
  fun describe (p : pt) =
    case p of
        { x = 0, y = 0, ... } => "origin"
      | { x = 0, y, ... } => "yaxis:" ^ Int.toString y
      | { x, y = 0, ... } => "xaxis:" ^ Int.toString x
      | { x, y, tag } => tag ^ ":" ^ Int.toString (x + y)
  val a = describe { x = 0, y = 0, tag = "A" }
  val b = describe { x = 0, y = 7, tag = "B" }
  val c = describe { x = 5, y = 0, tag = "C" }
  val d = describe { x = 3, y = 4, tag = "D" }
in
  val () = print ("@@record=" ^ a ^ "|" ^ b ^ "|" ^ c ^ "|" ^ d ^ "\n")
end

(* 5: integer literal patterns + default branch, big case *)
local
  fun roman n =
    case n of
        1 => "I" | 2 => "II" | 3 => "III" | 4 => "IV" | 5 => "V"
      | 6 => "VI" | 7 => "VII" | 8 => "VIII" | 9 => "IX" | 10 => "X"
      | _ => "?"
  val s = String.concatWith " " (List.map roman [0,1,4,5,9,10,11])
in
  val () = print ("@@roman=" ^ s ^ "\n")
end

(* 6: string literal patterns via case *)
local
  fun opcode s =
    case s of
        "add" => 1 | "sub" => 2 | "mul" => 3 | "div" => 4
      | "nop" => 0 | _ => ~1
  val codes = map opcode ["add","mul","xor","nop","div","sub"]
in
  val () = print ("@@opcode=" ^ String.concatWith "," (map Int.toString codes) ^ "\n")
end

(* 7: deep tree of binary nodes, structural fold via case *)
local
  datatype 'a tree = Leaf | Node of 'a tree * 'a * 'a tree
  fun ins (t, v) =
    case t of
        Leaf => Node (Leaf, v, Leaf)
      | Node (l, x, r) =>
          if v < x then Node (ins (l, v), x, r)
          else if v > x then Node (l, x, ins (r, v))
          else t
  fun inorder t =
    case t of
        Leaf => []
      | Node (l, x, r) => inorder l @ [x] @ inorder r
  val t = foldl (fn (v, acc) => ins (acc, v)) Leaf [5,3,8,1,4,7,9,2,6,3,5]
in
  val () = print ("@@bst=" ^ String.concatWith "," (map Int.toString (inorder t)) ^ "\n")
end

(* 8: exception patterns + handler dispatch *)
local
  exception Neg of int
  exception Zero
  fun safe n = if n < 0 then raise Neg n
               else if n = 0 then raise Zero
               else 1000 div n
  fun trial n = (safe n handle Neg k => ~k | Zero => 999 | Overflow => 7)
  val results = map trial [10, 0, ~3, 4, 25]
in
  val () = print ("@@exn=" ^ String.concatWith "," (map Int.toString results) ^ "\n")
end

(* 9: nested case with constructor + guard, mutual constructors *)
local
  datatype shape = Circle of int
                 | Rect of int * int
                 | Tri of int * int * int
  fun area s =
    case s of
        Circle r => 3 * r * r
      | Rect (w, h) => w * h
      | Tri (a, b, c) =>
          (case (a, b, c) of
               (x, y, z) => if x + y > z then x * y div 2 else 0)
  val total = foldl op+ 0 (map area [Circle 2, Rect(3,4), Tri(6,8,5), Tri(2,2,9)])
in
  val () = print ("@@area=" ^ Int.toString total ^ "\n")
end

(* 10: layered tuple-of-datatype, pattern on multiple scrutinees *)
local
  datatype color = R | G | B
  fun mix (c1, c2) =
    case (c1, c2) of
        (R, R) => "red"
      | (R, G) => "yellow"
      | (G, R) => "yellow"
      | (G, B) => "cyan"
      | (B, G) => "cyan"
      | (R, B) => "magenta"
      | (B, R) => "magenta"
      | (x, y) => "same"
  val combos = [mix (R,G), mix (G,B), mix (B,R), mix (R,R), mix (G,G)]
in
  val () = print ("@@mix=" ^ String.concatWith "|" combos ^ "\n")
end

(* 11: andb-shape: isShort-guarded word path vs rts path (the known bug class) *)
local
  val big = IntInf.<< (1, 0w70) + 0xF   (* a long/boxed int *)
  val small = 0xFF : IntInf.int
  (* mixed small/big — a wrong word-path optimization would truncate to a small value *)
  val r = IntInf.andb (small, big)
  val s = IntInf.andb (big, small)
  val t = IntInf.andb (big, big)
in
  val () = print ("@@andb=" ^ IntInf.toString r ^ "," ^ IntInf.toString s ^ "," ^ IntInf.toString t ^ "\n")
end

(* 12: char patterns in case, fold over string *)
local
  fun cls c =
    case c of
        #"0" => 0 | #"1" => 1 | #"2" => 2 | #"3" => 3 | #"4" => 4
      | #" " => ~1 | _ => 9
  val s = "31 42 x9"
  val sum = CharVector.foldl (fn (c, acc) => acc + cls c) 0 s
in
  val () = print ("@@char=" ^ Int.toString sum ^ "\n")
end

(* 13: deep nested option/list/datatype evaluator with environment *)
local
  datatype tm = Var of string
              | Lit of int
              | Let of string * tm * tm
              | Op of string * tm * tm
  fun lookup (env, x) =
    case env of
        [] => 0
      | (k, v) :: rest => if k = x then v else lookup (rest, x)
  fun ev (env, t) =
    case t of
        Var x => lookup (env, x)
      | Lit n => n
      | Let (x, e1, e2) => ev ((x, ev (env, e1)) :: env, e2)
      | Op (f, a, b) =>
          let val av = ev (env, a) val bv = ev (env, b) in
            case f of "+" => av + bv | "-" => av - bv
                    | "*" => av * bv | _ => 0
          end
  val prog = Let ("x", Lit 10,
               Let ("y", Op ("+", Var "x", Lit 5),
                 Op ("*", Var "x", Var "y")))
in
  val () = print ("@@interp=" ^ Int.toString (ev ([], prog)) ^ "\n")
end

(* 14: wildcard-heavy nested patterns, exhaustive on 3-tuple of bools *)
local
  fun maj (a, b, c) =
    case (a, b, c) of
        (true, true, _) => true
      | (true, _, true) => true
      | (_, true, true) => true
      | _ => false
  fun b2i x = if x then 1 else 0
  val all = [(true,true,true),(true,true,false),(true,false,false),
             (false,false,false),(false,true,true),(true,false,true)]
  val s = foldl (fn (t, acc) => acc * 2 + b2i (maj t)) 0 all
in
  val () = print ("@@maj=" ^ Int.toString s ^ "\n")
end

(* 15: real-number patterns via comparison branches + Real.fmt determinism *)
local
  datatype rexpr = RN of real | RAdd of rexpr * rexpr | RMul of rexpr * rexpr | RDiv of rexpr * rexpr
  fun reval e =
    case e of
        RN r => r
      | RAdd (a, b) => reval a + reval b
      | RMul (a, b) => reval a * reval b
      | RDiv (a, b) => reval a / reval b
  val r = reval (RDiv (RAdd (RN 1.0, RMul (RN 2.0, RN 3.0)), RN 4.0))
in
  val () = print ("@@real=" ^ Real.fmt (StringCvt.FIX (SOME 8)) r ^ "\n")
end

(* 16: large literal-int dispatch + arithmetic that could truncate if mis-optimized *)
local
  fun step n =
    case n mod 4 of
        0 => n div 2
      | 1 => 3 * n + 1
      | 2 => n div 2
      | _ => 3 * n + 1
  fun run (n, fuel, acc) =
    if n = 1 orelse fuel = 0 then acc
    else run (step n, fuel - 1, acc + 1)
  val len = run (27, 1000, 0)
in
  val () = print ("@@collatz=" ^ Int.toString len ^ "\n")
end

(* 17: nested as-patterns binding sub-structures, swap detection *)
local
  datatype 'a seq = Nil | Cons of 'a * 'a seq
  fun toList s = case s of Nil => [] | Cons (x, r) => x :: toList r
  fun fromList xs = foldr Cons Nil xs
  fun sortStep s =
    case s of
        (Cons (a, (rest as Cons (b, more)))) =>
          if a > b then Cons (b, sortStep (Cons (a, more)))
          else Cons (a, sortStep rest)
      | other => other
  fun bubble (s, 0) = s
    | bubble (s, k) = bubble (sortStep s, k - 1)
  val sorted = toList (bubble (fromList [5,2,8,1,9,3,7], 7))
in
  val () = print ("@@bubble=" ^ String.concatWith "," (map Int.toString sorted) ^ "\n")
end

(* 18: pattern match on int*int with literal-and-var mix in tuple positions *)
local
  fun gcd (a, 0) = a
    | gcd (0, b) = b
    | gcd (a, b) = gcd (b, a mod b)
  val pairs = [(48,36),(17,5),(100,75),(7,7),(0,9)]
  val gs = map gcd pairs
in
  val () = print ("@@gcd=" ^ String.concatWith "," (map Int.toString gs) ^ "\n")
end

(* 19: deeply nested datatype: JSON-ish, structural traversal *)
local
  datatype json = JNull
                | JBool of bool
                | JInt of int
                | JArr of json list
                | JObj of (string * json) list
  fun sumInts j =
    case j of
        JNull => 0
      | JBool _ => 0
      | JInt n => n
      | JArr xs => foldl (fn (x, a) => a + sumInts x) 0 xs
      | JObj fields => foldl (fn ((_, v), a) => a + sumInts v) 0 fields
  val doc = JObj [("a", JInt 1),
                  ("b", JArr [JInt 2, JInt 3, JNull, JBool true]),
                  ("c", JObj [("d", JInt 4), ("e", JArr [JInt 5, JInt 6])])]
in
  val () = print ("@@json=" ^ Int.toString (sumInts doc) ^ "\n")
end

(* 20: ref + pattern match in loop, mutable accumulation *)
local
  datatype instr = Push of int | Pop | AddTop | DupTop
  fun run prog =
    let val stk = ref ([] : int list)
        fun exec i =
          case (i, !stk) of
              (Push n, s) => stk := n :: s
            | (Pop, _ :: r) => stk := r
            | (Pop, []) => ()
            | (AddTop, a :: b :: r) => stk := (a + b) :: r
            | (AddTop, _) => ()
            | (DupTop, a :: r) => stk := a :: a :: r
            | (DupTop, []) => ()
    in app exec prog;
       case !stk of [] => 0 | x :: _ => x
    end
  val v = run [Push 3, Push 4, AddTop, DupTop, Push 10, AddTop, AddTop]
in
  val () = print ("@@vm=" ^ Int.toString v ^ "\n")
end
