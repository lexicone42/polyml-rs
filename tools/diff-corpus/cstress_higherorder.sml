(* 1: foldl/foldr/map/filter chain over a big list *)
local
  val xs = List.tabulate (2000, fn i => i - 1000)
  val evens = List.filter (fn x => x mod 2 = 0) xs
  val mapped = List.map (fn x => x * x - 3 * x + 1) evens
  val s1 = List.foldl (fn (a, acc) => acc + a) 0 mapped
  val s2 = List.foldr (fn (a, acc) => acc - a) 0 mapped
in
  val () = print ("@@p1=" ^ Int.toString s1 ^ "," ^ Int.toString s2 ^ "\n")
end

(* 2: function composition chains with o *)
local
  fun inc x = x + 1
  fun dbl x = x * 2
  fun neg x = ~x
  val f = inc o dbl o neg o inc o dbl
  val g = (fn x => x - 7) o f o (fn x => x + 100)
  val total = List.foldl (fn (i, a) => a + g i) 0 (List.tabulate (50, fn i => i))
in
  val () = print ("@@p2=" ^ Int.toString total ^ "\n")
end

(* 3: pipeline of functions held in a list, applied left-to-right *)
local
  val pipeline : (int -> int) list =
    [ fn x => x + 3,
      fn x => x * x,
      fn x => x - 11,
      fn x => x div 2,
      fn x => if x < 0 then ~x else x ]
  fun run fs x = List.foldl (fn (f, v) => f v) x fs
  val results = List.map (run pipeline) [~5, 0, 4, 13, 100]
  val joined = String.concatWith ";" (List.map Int.toString results)
in
  val () = print ("@@p3=" ^ joined ^ "\n")
end

(* 4: map a closure capturing mutable state, then fold *)
local
  val counter = ref 0
  fun stamp x = (counter := !counter + 1; x * (!counter))
  val big = List.tabulate (300, fn i => i + 1)
  val stamped = List.map stamp big
  val acc = List.foldl (fn (a, s) => s + a) 0 stamped
in
  val () = print ("@@p4=" ^ Int.toString acc ^ ":" ^ Int.toString (!counter) ^ "\n")
end

(* 5: sort via a comparator closure (insertion sort), reverse comparator too *)
local
  fun insert cmp x [] = [x]
    | insert cmp x (y :: ys) =
        if cmp (x, y) = GREATER then y :: insert cmp x ys else x :: y :: ys
  fun isort cmp = List.foldr (fn (x, acc) => insert cmp x acc) []
  val data = [37, ~4, 18, 0, 99, ~50, 18, 7, 7, 23]
  val asc = isort Int.compare data
  val desc = isort (fn (a, b) => Int.compare (b, a)) data
in
  val () = print ("@@p5=" ^ String.concatWith "," (List.map Int.toString asc)
                  ^ "|" ^ String.concatWith "," (List.map Int.toString desc) ^ "\n")
end

(* 6: generic fold over a datatype (binary tree) *)
local
  datatype 'a tree = Leaf | Node of 'a tree * 'a * 'a tree
  fun build [] = Leaf
    | build (x :: xs) =
        let
          val (lo, hi) = List.partition (fn y => y < x) xs
        in
          Node (build lo, x, build hi)
        end
  fun foldTree f acc Leaf = acc
    | foldTree f acc (Node (l, v, r)) =
        let val acc1 = foldTree f acc l
        in foldTree f (f (v, acc1)) r end
  val t = build [50, 30, 70, 20, 40, 60, 80, 10, 35]
  val sum = foldTree (fn (v, a) => a + v) 0 t
  val cnt = foldTree (fn (_, a) => a + 1) 0 t
  val inorder = foldTree (fn (v, a) => v :: a) [] t  (* reversed-of-inorder *)
in
  val () = print ("@@p6=" ^ Int.toString sum ^ ":" ^ Int.toString cnt
                  ^ ":" ^ String.concatWith "," (List.map Int.toString (rev inorder)) ^ "\n")
end

(* 7: curried higher-order combinators, partial application *)
local
  fun apply3 f x = f (f (f x))
  fun adder n = fn x => x + n
  fun scaler n = fn x => x * n
  val mk = fn (a, b) => (adder a) o (scaler b)
  val fns = List.map mk [(1, 2), (3, 4), (~2, 5), (10, ~1)]
  val applied = List.map (fn f => apply3 f 1) fns
  val tot = List.foldl op+ 0 applied
in
  val () = print ("@@p7=" ^ String.concatWith "," (List.map Int.toString applied)
                  ^ "=" ^ Int.toString tot ^ "\n")
end

(* 8: foldl building a closure accumulator (Horner's method via fold) *)
local
  val coeffs = [3, ~1, 4, ~1, 5, ~9, 2, 6]  (* highest degree first *)
  fun horner x = List.foldl (fn (c, acc) => acc * x + c) 0 coeffs
  val vals = List.map horner [0, 1, 2, ~1, ~2, 3]
in
  val () = print ("@@p8=" ^ String.concatWith "," (List.map Int.toString vals) ^ "\n")
end

(* 9: real-number pipeline, fmt-formatted, fold of map *)
local
  fun fx r = Real.fmt (StringCvt.FIX (SOME 8)) r
  val xs = List.tabulate (10, fn i => Real.fromInt (i + 1))
  val transformed = List.map (fn r => Math.sqrt r + r / 2.0) xs
  val total = List.foldl (op +) 0.0 transformed
  val composed = (fn r => r * 2.0) o (fn r => r + 1.0) o Math.sqrt
  val one = composed 16.0
in
  val () = print ("@@p9=" ^ fx total ^ ":" ^ fx one ^ "\n")
end

(* 10: exception-driven short-circuit inside a fold (find first) *)
local
  exception Found of int
  fun firstSatisfying p xs =
    (List.foldl (fn (x, ()) => if p x then raise Found x else ()) () xs; ~1)
    handle Found v => v
  val data = List.tabulate (500, fn i => (i * 37 + 11) mod 1000)
  val r1 = firstSatisfying (fn x => x > 950) data
  val r2 = firstSatisfying (fn x => x = 12345) data  (* never -> ~1 *)
in
  val () = print ("@@p10=" ^ Int.toString r1 ^ ":" ^ Int.toString r2 ^ "\n")
end

(* 11: map+filter+fold producing a string, with String.map closure *)
local
  val words = ["apple", "Banana", "cherry", "Date", "egg", "Fig"]
  val upFirst = List.filter (fn s => Char.isUpper (String.sub (s, 0))) words
  val lengths = List.map String.size words
  val totalLen = List.foldl op+ 0 lengths
  val rot = String.map (fn c => if Char.isAlpha c
                                then Char.chr (Char.ord #"a" + (Char.ord (Char.toLower c) - Char.ord #"a" + 13) mod 26)
                                else c) "HelloWorld"
in
  val () = print ("@@p11=" ^ String.concatWith "," upFirst ^ ":"
                  ^ Int.toString totalLen ^ ":" ^ rot ^ "\n")
end

(* 12: generic fold over a recursive expression datatype (eval) *)
local
  datatype expr = Num of int
                | Add of expr * expr
                | Mul of expr * expr
                | Neg of expr
  fun eval (Num n) = n
    | eval (Add (a, b)) = eval a + eval b
    | eval (Mul (a, b)) = eval a * eval b
    | eval (Neg a) = ~(eval a)
  fun foldExpr fnum fadd fmul fneg e =
    let
      fun go (Num n) = fnum n
        | go (Add (a, b)) = fadd (go a, go b)
        | go (Mul (a, b)) = fmul (go a, go b)
        | go (Neg a) = fneg (go a)
    in go e end
  val e = Add (Mul (Num 3, Num 4), Neg (Add (Num 5, Num 6)))
  val v = eval e
  val nodeCount = foldExpr (fn _ => 1) (fn (a, b) => a + b + 1)
                           (fn (a, b) => a + b + 1) (fn a => a + 1) e
in
  val () = print ("@@p12=" ^ Int.toString v ^ ":" ^ Int.toString nodeCount ^ "\n")
end

(* 13: andb-shape stressor — isShort-guarded branch over mixed-size ints *)
local
  (* mimic "if isShort i andalso isShort j then word-path else other-path" *)
  fun classify (i, j) =
    if RunCall.isShort i andalso RunCall.isShort j then 1 else 0
  val big = 1000000000000000000  (* large, may be boxed *)
  val small = 5
  val cases = [(small, small), (small, big), (big, small), (big, big), (0, 0)]
  val tags = List.map classify cases
  (* also exercise actual IntInf bit ops that motivated the original bug *)
  val ab = [ IntInf.andb (5, big),
             IntInf.andb (big, 5),
             IntInf.andb (big, big),
             IntInf.andb (7, 3),
             IntInf.orb (small, big) ]
in
  val () = print ("@@p13=" ^ String.concatWith "," (List.map Int.toString tags)
                  ^ ":" ^ String.concatWith "," (List.map IntInf.toString ab) ^ "\n")
end

(* 14: deep composition of many small fns built by fold *)
local
  val ops : (int -> int) list =
    List.tabulate (40, fn i =>
      case i mod 4 of
        0 => (fn x => x + i)
      | 1 => (fn x => x - (i div 2))
      | 2 => (fn x => x * 2 - i)
      | _ => (fn x => (x + i) div 2))
  val composed = List.foldl (fn (f, g) => f o g) (fn x => x) ops
  val results = List.map composed [0, 1, ~3, 17]
in
  val () = print ("@@p14=" ^ String.concatWith "," (List.map Int.toString results) ^ "\n")
end

(* 15: mapPartial + foldl over option-producing closures *)
local
  fun safeDiv d n = if d = 0 then NONE else SOME (n div d)
  val nums = List.tabulate (30, fn i => i - 15)
  val quotients = List.mapPartial (fn x => safeDiv x 1000) nums
  val sum = List.foldl op+ 0 quotients
  val cnt = List.length quotients
in
  val () = print ("@@p15=" ^ Int.toString sum ^ ":" ^ Int.toString cnt ^ "\n")
end

(* 16: tail-recursive fold building reversed list, then big case dispatch *)
local
  fun dispatch n =
    case n mod 7 of
        0 => "zero" | 1 => "one" | 2 => "two" | 3 => "three"
      | 4 => "four" | 5 => "five" | _ => "six"
  val labels = List.map dispatch (List.tabulate (21, fn i => i))
  val histogram = List.foldl
        (fn (s, acc) => acc + String.size s) 0 labels
  val distinct = List.foldl
        (fn (s, acc) => if List.exists (fn x => x = s) acc then acc else s :: acc)
        [] labels
in
  val () = print ("@@p16=" ^ Int.toString histogram ^ ":"
                  ^ Int.toString (List.length distinct) ^ "\n")
end
