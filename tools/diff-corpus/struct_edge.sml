(* diff-corpus category: struct_edge — structure/equality/exn-introspection +
   compiler-stress (functor/sig/record/mutual-rec/poly-rec) edge cases not
   covered by listsarr/listpair/vectors/arrayslice/option_bool/exceptions/
   cstress_*. 2026-06-16. Every case reduces to a deterministic @@label=value. *)

(* ---- polymorphic / structural equality ---- *)
(* ref equality is BY-IDENTITY, not structural: two fresh refs differ even
   with equal contents; a ref equals itself. *)
val () = print ("@@eq_two_fresh_refs=" ^ Bool.toString (ref 1 = ref 1) ^ "\n");
val () = print ("@@eq_ref_self=" ^ (let val r = ref 1 in Bool.toString (r = r) end) ^ "\n");
val () = print ("@@eq_ref_aliased=" ^ (let val r = ref 5 val s = r in Bool.toString (r = s) end) ^ "\n");
val () = print ("@@eq_ref_after_update=" ^ (let val r = ref 1 val s = r val _ = r := 99 in Bool.toString (r = s) end) ^ "\n");
(* structural equality on tuples / nested tuples *)
val () = print ("@@eq_tuple_eq=" ^ Bool.toString ((1,2,3) = (1,2,3)) ^ "\n");
val () = print ("@@eq_tuple_neq=" ^ Bool.toString ((1,2,3) = (1,2,4)) ^ "\n");
val () = print ("@@eq_nested_tuple=" ^ Bool.toString (((1,2),(3,4)) = ((1,2),(3,4))) ^ "\n");
(* structural equality on lists *)
val () = print ("@@eq_list_eq=" ^ Bool.toString ([1,2,3] = [1,2,3]) ^ "\n");
val () = print ("@@eq_list_len=" ^ Bool.toString ([1,2,3] = [1,2]) ^ "\n");
val () = print ("@@eq_list_empty=" ^ Bool.toString (([]:int list) = []) ^ "\n");
val () = print ("@@eq_list_of_tuples=" ^ Bool.toString ([(1,"a"),(2,"b")] = [(1,"a"),(2,"b")]) ^ "\n");
(* structural equality on datatype values *)
local datatype color = Red | Green | Blue of int in
  val () = print ("@@eq_dt_nullary=" ^ Bool.toString (Red = Red) ^ "\n");
  val () = print ("@@eq_dt_diff_ctor=" ^ Bool.toString (Red = Green) ^ "\n");
  val () = print ("@@eq_dt_carried_eq=" ^ Bool.toString (Blue 7 = Blue 7) ^ "\n");
  val () = print ("@@eq_dt_carried_neq=" ^ Bool.toString (Blue 7 = Blue 8) ^ "\n")
end;
(* equality on option / mixed *)
val () = print ("@@eq_option_some=" ^ Bool.toString (SOME 3 = SOME 3) ^ "\n");
val () = print ("@@eq_option_none=" ^ Bool.toString ((NONE:int option) = NONE) ^ "\n");
val () = print ("@@eq_option_mixed=" ^ Bool.toString (SOME 3 = NONE) ^ "\n");
(* equality on strings / chars *)
val () = print ("@@eq_string=" ^ Bool.toString ("abc" = "abc") ^ "\n");
val () = print ("@@eq_char=" ^ Bool.toString (#"x" = #"x") ^ "\n");
(* list containing refs: identity propagates structurally *)
val () = print ("@@eq_list_of_refs=" ^ (let val r = ref 0 in Bool.toString ([r] = [r]) end) ^ "\n");
val () = print ("@@eq_list_fresh_refs=" ^ Bool.toString ([ref 0] = [ref 0]) ^ "\n");

(* ---- General: exnName / exnMessage on builtins + user exns ---- *)
val () = print ("@@exnName_Div=" ^ (General.exnName Div) ^ "\n");
val () = print ("@@exnName_Overflow=" ^ (General.exnName Overflow) ^ "\n");
val () = print ("@@exnName_Subscript=" ^ (General.exnName Subscript) ^ "\n");
val () = print ("@@exnName_Empty=" ^ (General.exnName Empty) ^ "\n");
val () = print ("@@exnName_Bind=" ^ (General.exnName Bind) ^ "\n");
local exception MyErr of int in
  val () = print ("@@exnName_user=" ^ (General.exnName (MyErr 5)) ^ "\n")
end;
(* exnMessage embeds the name (and, for value-carrying, the payload form).
   We probe only the NAME prefix to stay deterministic across formatting. *)
val () = print ("@@exnMessage_Div_has=" ^ Bool.toString (String.isSubstring "Div" (General.exnMessage Div)) ^ "\n");
val () = print ("@@exnMessage_Sub_has=" ^ Bool.toString (String.isSubstring "Subscript" (General.exnMessage Subscript)) ^ "\n");
(* caught exn: name survives the handle path *)
val () = print ("@@exnName_caught=" ^ ((List.nth ([1], 9); "NO") handle e => General.exnName e) ^ "\n");
val () = print ("@@exnName_caught_user=" ^ (let exception Custom in (raise Custom; "NO") handle e => General.exnName e end) ^ "\n");

(* ---- General.before / o / ignore ---- *)
val () = print ("@@before_value=" ^ (let val r = ref 0 in Int.toString ((r := 7; 42) before (r := 99)) ^ ":" ^ Int.toString (!r) end) ^ "\n");
val () = print ("@@before_order=" ^ (let val log = ref [] fun note n = log := n :: !log in ignore ((note 1; 5) before (note 2)); String.concatWith "," (map Int.toString (rev (!log))) end) ^ "\n");
val () = print ("@@o_compose=" ^ Int.toString (((fn x => x - 1) o (fn x => x * 10)) 5) ^ "\n");
val () = print ("@@o_assoc=" ^ Int.toString ((((fn x=>x+1) o (fn x=>x*2)) o (fn x=>x+3)) 4) ^ "\n");
val () = print ("@@ignore_unit=" ^ (case ignore (1+1) of () => "OK") ^ "\n");

(* ---- order / compare combinators on tuples ---- *)
fun pairCompare (cmpA, cmpB) ((a1,b1),(a2,b2)) =
  case cmpA (a1,a2) of EQUAL => cmpB (b1,b2) | ord => ord;
fun ordStr LESS = "LT" | ordStr EQUAL = "EQ" | ordStr GREATER = "GT";
val () = print ("@@pcmp_first_decides=" ^ ordStr (pairCompare (Int.compare, String.compare) ((1,"z"),(2,"a"))) ^ "\n");
val () = print ("@@pcmp_second_decides=" ^ ordStr (pairCompare (Int.compare, String.compare) ((5,"a"),(5,"b"))) ^ "\n");
val () = print ("@@pcmp_equal=" ^ ordStr (pairCompare (Int.compare, String.compare) ((5,"a"),(5,"a"))) ^ "\n");
val () = print ("@@string_compare=" ^ ordStr (String.compare ("apple","apricot")) ^ "\n");
val () = print ("@@char_compare=" ^ ordStr (Char.compare (#"a", #"b")) ^ "\n");

(* ---- List functions in my area not already exercised: nth/getItem/partition
   in fresh combinations, mapPartial, concat with empties, collate on strings,
   revAppend roundtrip ---- *)
val () = print ("@@list_mapPartial=" ^ String.concatWith "," (map Int.toString (List.mapPartial (fn x => if x mod 2 = 0 then SOME (x*x) else NONE) [1,2,3,4,5,6])) ^ "\n");
val () = print ("@@list_partition_both=" ^ (let val (a,b) = List.partition (fn x => x > 3) [5,1,4,2,3,6] in String.concatWith "," (map Int.toString a) ^ "/" ^ String.concatWith "," (map Int.toString b) end) ^ "\n");
val () = print ("@@list_collate_str=" ^ ordStr (List.collate Char.compare (explode "abc", explode "abd")) ^ "\n");
val () = print ("@@list_revAppend_rt=" ^ String.concatWith "," (map Int.toString (List.revAppend (List.revAppend ([1,2,3],[]), []))) ^ "\n");
val () = print ("@@list_getItem_chain=" ^ (case List.getItem [9,8,7] of SOME (h, t) => Int.toString h ^ ":" ^ (case List.getItem t of SOME (h2,_) => Int.toString h2 | NONE => "x") | NONE => "NONE") ^ "\n");

(* ---- compiler-stress: functor application ---- *)
signature ADDER = sig type t val zero : t val add : t * t -> t val show : t -> string end;
functor Sum (A : ADDER) = struct
  fun sumList xs = List.foldl A.add A.zero xs
  fun showList xs = A.show (sumList xs)
end;
structure IntAdder : ADDER = struct
  type t = int
  val zero = 0
  fun add (a,b) = a + b
  val show = Int.toString
end;
structure IntSum = Sum (IntAdder);
val () = print ("@@functor_intsum=" ^ IntSum.showList [10,20,30,40] ^ "\n");
structure StrAdder : ADDER = struct
  type t = string
  val zero = ""
  fun add (a,b) = a ^ b
  fun show s = s
end;
structure StrSum = Sum (StrAdder);
val () = print ("@@functor_strsum=" ^ StrSum.showList ["a","b","c"] ^ "\n");

(* ---- compiler-stress: signature ascription (opaque vs transparent) ---- *)
signature COUNTER = sig type t val init : t val tick : t -> t val read : t -> int end;
structure Counter :> COUNTER = struct
  type t = int
  val init = 0
  fun tick n = n + 1
  fun read n = n
end;
val () = print ("@@sig_opaque_counter=" ^ Int.toString (Counter.read (Counter.tick (Counter.tick (Counter.tick Counter.init)))) ^ "\n");
(* transparent ascription lets the type leak; we just check it computes *)
structure TCounter : COUNTER = struct
  type t = int
  val init = 100
  fun tick n = n + 10
  fun read n = n
end;
val () = print ("@@sig_transparent=" ^ Int.toString (TCounter.read (TCounter.tick TCounter.init)) ^ "\n");

(* ---- compiler-stress: records with field punning ---- *)
type point = { x : int, y : int, label : string };
fun mkpt x y label = { x = x, y = y, label = label };  (* field punning shorthand *)
val () = print ("@@record_punning=" ^ (let val {x, y, label} = mkpt 3 4 "p" in label ^ ":" ^ Int.toString (x + y) end) ^ "\n");
val () = print ("@@record_field_select=" ^ Int.toString (#y (mkpt 11 22 "q")) ^ "\n");
val () = print ("@@record_eq=" ^ Bool.toString (mkpt 1 2 "a" = mkpt 1 2 "a") ^ "\n");
val () = print ("@@record_neq=" ^ Bool.toString (mkpt 1 2 "a" = mkpt 1 2 "b") ^ "\n");
(* anonymous-tuple-as-record selection (#1 etc already in option_bool; do #N on 4-tuple) *)
val () = print ("@@record_tuple4=" ^ Int.toString (#3 (10,20,30,40)) ^ "\n");

(* ---- compiler-stress: mutually-recursive datatypes + functions ---- *)
datatype tree = Leaf of int | Branch of forest
and forest = Empty | Cons of tree * forest;
fun sumTree (Leaf n) = n
  | sumTree (Branch f) = sumForest f
and sumForest Empty = 0
  | sumForest (Cons (t, rest)) = sumTree t + sumForest rest;
val sampleForest = Cons (Leaf 1, Cons (Branch (Cons (Leaf 2, Cons (Leaf 3, Empty))), Cons (Leaf 4, Empty)));
val () = print ("@@mutual_sumforest=" ^ Int.toString (sumForest sampleForest) ^ "\n");
fun countLeaves (Leaf _) = 1
  | countLeaves (Branch f) = countForest f
and countForest Empty = 0
  | countForest (Cons (t, rest)) = countLeaves t + countForest rest;
val () = print ("@@mutual_countleaves=" ^ Int.toString (countForest sampleForest) ^ "\n");

(* ---- compiler-stress: even/odd mutual recursion ---- *)
fun isEven 0 = true | isEven n = isOdd (n - 1)
and isOdd 0 = false | isOdd n = isEven (n - 1);
val () = print ("@@mutual_evenodd=" ^ Bool.toString (isEven 100) ^ ":" ^ Bool.toString (isOdd 7) ^ "\n");

(* ---- compiler-stress: exceptions carrying payloads, extracted in handler ---- *)
local
  exception Pair of int * string
  fun emit (n, s) = raise (Pair (n, s))
  fun extract (n, s) = (emit (n, s); "") handle Pair (k, t) => Int.toString k ^ t
in
  val () = print ("@@exn_payload_extract=" ^ extract (42, "ok") ^ "\n")
end;
local
  exception Rec of { code : int, msg : string }
  fun go () = raise (Rec { code = 7, msg = "boom" })
in
  val () = print ("@@exn_record_payload=" ^ ((go ()) handle Rec {code, msg} => Int.toString code ^ ":" ^ msg) ^ "\n")
end;

(* ---- compiler-stress: deeply nested pattern match ---- *)
fun classify3 (SOME (a, b :: c :: _)) = a + b + c
  | classify3 (SOME (a, [b])) = a + b
  | classify3 (SOME (a, [])) = a
  | classify3 NONE = ~1;
val () = print ("@@nested_pat_3=" ^ Int.toString (classify3 (SOME (100, [1,2,3,4]))) ^ "\n");
val () = print ("@@nested_pat_1=" ^ Int.toString (classify3 (SOME (100, [5]))) ^ "\n");
val () = print ("@@nested_pat_0=" ^ Int.toString (classify3 (SOME (100, []))) ^ "\n");
val () = print ("@@nested_pat_none=" ^ Int.toString (classify3 NONE) ^ "\n");

(* ---- compiler-stress: nested-datatype depth (the recursive call here is at the
   SAME type — a plain polymorphic datatype traversal, valid HM-ML; genuine
   polymorphic recursion over ('a*'a) nested needs an explicit forall SML lacks,
   so we keep this monomorphic-recursion form which both sides accept). ---- *)
datatype 'a tre = Tip of 'a | Fork of 'a tre * 'a tre;
fun depth (Tip _) = 0
  | depth (Fork (l, r)) = 1 + Int.max (depth l, depth r);
val () = print ("@@tre_depth=" ^ Int.toString (depth (Fork (Fork (Tip 1, Tip 2), Tip 3))) ^ "\n");
fun treeSum (Tip n) = n
  | treeSum (Fork (l, r)) = treeSum l + treeSum r;
val () = print ("@@tre_sum=" ^ Int.toString (treeSum (Fork (Fork (Tip 1, Tip 2), Fork (Tip 3, Tip 4)))) ^ "\n");

(* ---- compiler-stress: let-polymorphism (a polymorphic id used at two types) ---- *)
val () = print ("@@let_poly=" ^ (let fun id x = x in Int.toString (id 5) ^ ":" ^ id "s" ^ ":" ^ Bool.toString (id true) end) ^ "\n");

(* ---- compiler-stress: curried + higher-order through a structure ---- *)
structure HOF = struct
  fun twice f x = f (f x)
  fun compose3 f g h x = f (g (h x))
end;
val () = print ("@@hof_twice=" ^ Int.toString (HOF.twice (fn x => x * 3) 2) ^ "\n");
val () = print ("@@hof_compose3=" ^ Int.toString (HOF.compose3 (fn x=>x+1) (fn x=>x*2) (fn x=>x-3) 10) ^ "\n");
