(* deriv — symbolic differentiation without simplification (the Gabriel "deriv"
 * flavour). Builds a size-n expression, differentiates it (the derivative is
 * O(n^2) in nodes because Mul duplicates subtrees), and counts result nodes.
 * A small-object allocation / GC-churn benchmark; pure integer/datatype. *)

datatype expr =
    Num of int
  | Var of string
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Divi of expr * expr;

fun deriv (Num _)        = Num 0
  | deriv (Var "x")      = Num 1
  | deriv (Var _)        = Num 0
  | deriv (Add (a, b))   = Add (deriv a, deriv b)
  | deriv (Sub (a, b))   = Sub (deriv a, deriv b)
  | deriv (Mul (a, b))   = Add (Mul (deriv a, b), Mul (a, deriv b))
  | deriv (Divi (a, b))  =
      Divi (Sub (Mul (deriv a, b), Mul (a, deriv b)), Mul (b, b));

fun count (Num _)       = 1
  | count (Var _)       = 1
  | count (Add (a, b))  = 1 + count a + count b
  | count (Sub (a, b))  = 1 + count a + count b
  | count (Mul (a, b))  = 1 + count a + count b
  | count (Divi (a, b)) = 1 + count a + count b;

fun build 0 = Num 1
  | build n = Add (Mul (Var "x", build (n - 1)), Num n);

fun bench n =
    let val e  = build n
        val d  = deriv e
    in count d end;

fun checksum (r:int) = Int.toString r;

val bench_name = "bench_deriv";
val default_n  = 60;
