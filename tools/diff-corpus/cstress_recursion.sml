(* 1. deep tail-recursive accumulator: sum 1..100000 *)
local
  fun sumTo (n, acc) = if n = 0 then acc else sumTo (n - 1, acc + n)
in
  val s1 = sumTo (100000, 0)
end;
print ("@@tailsum=" ^ Int.toString s1 ^ "\n");

(* 2. non-tail recursion: naive fib 30 *)
local
  fun fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)
in
  val s2 = fib 30
end;
print ("@@fib30=" ^ Int.toString s2 ^ "\n");

(* 3. Ackermann (2,n) and (3,3) — deep recursion *)
local
  fun ack (0, n) = n + 1
    | ack (m, 0) = ack (m - 1, 1)
    | ack (m, n) = ack (m - 1, ack (m, n - 1))
in
  val s3 = ack (2, 7) + ack (3, 3)
end;
print ("@@ackermann=" ^ Int.toString s3 ^ "\n");

(* 4. mutual recursion: isEven/isOdd over 0..50, count evens *)
local
  fun isEven 0 = true
    | isEven n = isOdd (n - 1)
  and isOdd 0 = false
    | isOdd n = isEven (n - 1)
  fun loop (n, acc) = if n > 50 then acc
                      else loop (n + 1, if isEven n then acc + 1 else acc)
in
  val s4 = loop (0, 0)
end;
print ("@@evencount=" ^ Int.toString s4 ^ "\n");

(* 5. 3-way mutual recursion: mod-3 classifier *)
local
  fun isZeroMod3 0 = true | isZeroMod3 n = isTwoMod3 (n - 1)
  and isOneMod3 0 = false | isOneMod3 n = isZeroMod3 (n - 1)
  and isTwoMod3 0 = false | isTwoMod3 n = isOneMod3 (n - 1)
  fun count (n, acc) = if n > 99 then acc
                       else count (n + 1, if isZeroMod3 n then acc + 1 else acc)
in
  val s5 = count (0, 0)
end;
print ("@@mod3count=" ^ Int.toString s5 ^ "\n");

(* 6. tree recursion over a built binary tree: sum of leaves *)
local
  datatype tree = Leaf of int | Node of tree * tree
  fun build (lo, hi) =
        if lo = hi then Leaf lo
        else let val mid = (lo + hi) div 2
             in Node (build (lo, mid), build (mid + 1, hi)) end
  fun sumTree (Leaf v) = v
    | sumTree (Node (l, r)) = sumTree l + sumTree r
in
  val s6 = sumTree (build (1, 1000))
end;
print ("@@treesum=" ^ Int.toString s6 ^ "\n");

(* 7. tree recursion: max depth of an unbalanced tree *)
local
  datatype 'a tree = Lf | Br of 'a tree * 'a * 'a tree
  fun ins (Lf, x) = Br (Lf, x, Lf)
    | ins (Br (l, v, r), x) =
        if x < v then Br (ins (l, x), v, r)
        else if x > v then Br (l, v, ins (r, x))
        else Br (l, v, r)
  fun depth Lf = 0
    | depth (Br (l, _, r)) = 1 + Int.max (depth l, depth r)
  (* deterministic pseudo-shuffle insertion order via linear congruential *)
  fun gen (n, seed, t) =
        if n = 0 then t
        else let val seed' = (seed * 1103515245 + 12345) mod 1000
             in gen (n - 1, seed', ins (t, seed')) end
in
  val s7 = depth (gen (300, 7, Lf))
end;
print ("@@treedepth=" ^ Int.toString s7 ^ "\n");

(* 8. recursion returning a tuple: (sum, product mod 1000007, count) *)
local
  fun walk 0 = (0, 1, 0)
    | walk n =
        let val (s, p, c) = walk (n - 1)
        in (s + n, (p * n) mod 1000007, c + 1) end
  val (sm, pr, ct) = walk 20
in
  val s8 = sm * 1000 + pr + ct
end;
print ("@@tupret=" ^ Int.toString s8 ^ "\n");

(* 9. recursion with an accumulator that is a CLOSURE (CPS factorial) *)
local
  fun factCPS (0, k) = k 1
    | factCPS (n, k) = factCPS (n - 1, fn r => k (n * r))
  val s9 = factCPS (12, fn x => x)
in
  val s9 = s9
end;
print ("@@cpsfact=" ^ Int.toString s9 ^ "\n");

(* 10. CPS over a list — sum with continuations, mixing closures and recursion *)
local
  fun sumK ([], k) = k 0
    | sumK (x :: xs, k) = sumK (xs, fn r => k (x + r))
  fun range (0, acc) = acc
    | range (n, acc) = range (n - 1, n :: acc)
  val s10 = sumK (range (500, []), fn x => x)
in
  val s10 = s10
end;
print ("@@cpslistsum=" ^ Int.toString s10 ^ "\n");

(* 11. recursion building a closure accumulator then applying it *)
local
  (* compose n increments-by-i into one function, then apply to 0 *)
  fun buildAdder (0, f) = f
    | buildAdder (n, f) = buildAdder (n - 1, fn x => f (x + n))
  val adder = buildAdder (100, fn x => x)
  val s11 = adder 0
in
  val s11 = s11
end;
print ("@@closacc=" ^ Int.toString s11 ^ "\n");

(* 12. recursion with refs as a mutable accumulator (deep loop) *)
local
  val acc = ref 0
  fun loop n = if n = 0 then () else (acc := !acc + (n mod 7); loop (n - 1))
in
  val () = loop 50000
  val s12 = !acc
end;
print ("@@refacc=" ^ Int.toString s12 ^ "\n");

(* 13. big case dispatch inside recursion: collatz step counter *)
local
  fun steps (n, c) =
        if n = 1 then c
        else case n mod 2 of
                 0 => steps (n div 2, c + 1)
               | _ => steps (3 * n + 1, c + 1)
  (* total steps for all starts 1..200 *)
  fun total (i, acc) = if i > 200 then acc else total (i + 1, acc + steps (i, 0))
in
  val s13 = total (1, 0)
end;
print ("@@collatz=" ^ Int.toString s13 ^ "\n");

(* 14. recursion over a datatype with a big case (expression evaluator) *)
local
  datatype expr = Num of int
                | Add of expr * expr
                | Sub of expr * expr
                | Mul of expr * expr
                | Neg of expr
  fun eval (Num n) = n
    | eval (Add (a, b)) = eval a + eval b
    | eval (Sub (a, b)) = eval a - eval b
    | eval (Mul (a, b)) = eval a * eval b
    | eval (Neg a) = ~ (eval a)
  (* build a deep expression tree recursively *)
  fun deep 0 = Num 1
    | deep n = Add (Mul (Num 2, deep (n - 1)), Neg (Num n))
  val s14 = eval (deep 25)
in
  val s14 = s14
end;
print ("@@evalexpr=" ^ Int.toString s14 ^ "\n");

(* 15. recursion + exceptions: find first index with predicate via raise *)
local
  exception Found of int
  fun scan ([], _) = ~1
    | scan (x :: xs, i) =
        if x * x > 5000 then raise Found i else scan (xs, i + 1)
  fun range (0, acc) = acc
    | range (n, acc) = range (n - 1, n :: acc)
  val s15 = (scan (range (200, []), 0)) handle Found i => i
in
  val s15 = s15
end;
print ("@@excscan=" ^ Int.toString s15 ^ "\n");

(* 16. mutually recursive even/odd via the andb-shape stress: deep + real *)
local
  (* Newton's method for sqrt, recursive; print deterministic real *)
  fun newton (x, guess, iters) =
        if iters = 0 then guess
        else newton (x, (guess + x / guess) / 2.0, iters - 1)
  val r = newton (2.0, 1.0, 20)
in
  val s16 = Real.fmt (StringCvt.FIX (SOME 8)) r
end;
print ("@@newtonsqrt=" ^ s16 ^ "\n");

(* 17. recursion returning function-of-functions: Church numerals to int *)
local
  fun church 0 = (fn _ => fn x => x)
    | church n = let val c = church (n - 1)
                 in fn f => fn x => f (c f x) end
  fun toInt c = c (fn x => x + 1) 0
  val s17 = toInt (church 1000)
in
  val s17 = s17
end;
print ("@@church=" ^ Int.toString s17 ^ "\n");

(* 18. deep left-fold + right-fold recursion divergence check *)
local
  val M = 1000000007
  fun range (0, acc) = acc
    | range (n, acc) = range (n - 1, n :: acc)
  val xs = range (2000, [])
  (* keep every step in range so a wrong-branch/truncation shows, no overflow *)
  val lsum = foldl (fn (x, a) => (a * 2 + x) mod M) 0 xs
  val rsum = foldr (fn (x, a) => (a * 2 + x) mod M) 0 xs
in
  val s18 = lsum * 31 + rsum
end;
print ("@@foldmix=" ^ Int.toString s18 ^ "\n");
