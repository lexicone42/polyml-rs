(* diff-corpus category: letpoly — let-polymorphism, scoping, local hoisting, val rec mutual *)

(* 1. polymorphic identity in a let, instantiated at int, string, bool — combine into one digest *)
val () =
  let
    val id = fn x => x
    val a = id 42
    val b = id "hi"
    val c = id true
  in
    print ("@@poly_id_three_types=" ^ Int.toString a ^ "|" ^ b ^ "|" ^ Bool.toString c ^ "\n")
  end;

(* 2. polymorphic pair-builder used at (int,string) and (bool,int); the value restriction is fine since fn *)
val () =
  let
    fun mk x y = (x, y)
    val p1 = mk 7 "seven"
    val p2 = mk false 99
  in
    print ("@@poly_mk_pairs=" ^ Int.toString (#1 p1) ^ ":" ^ #2 p1 ^ ";" ^
           Bool.toString (#1 p2) ^ ":" ^ Int.toString (#2 p2) ^ "\n")
  end;

(* 3. shadowed bindings: inner let rebinds x at a DIFFERENT type; the optimizer must not confuse them *)
val () =
  let
    val x = 10
    val r1 = x + 5
    val s =
      let val x = "outer-was-int" in x ^ "!" end
    val r2 = x * 2  (* x must still be the int 10 here *)
  in
    print ("@@shadow_diff_types=" ^ Int.toString r1 ^ "/" ^ s ^ "/" ^ Int.toString r2 ^ "\n")
  end;

(* 4. val rec mutual recursion: even/odd, nested in a local..in..end, lifted *)
val () =
  let
    fun ev 0 = true | ev n = od (n - 1)
    and od 0 = false | od n = ev (n - 1)
  in
    print ("@@mutual_even_odd=" ^ Bool.toString (ev 100) ^ "," ^ Bool.toString (od 77) ^
           "," ^ Bool.toString (ev 1) ^ "," ^ Bool.toString (od 0) ^ "\n")
  end;

(* 5. local fun lifted out of a loop; closure captures the multiplier; sum over a recursion *)
val () =
  let
    fun scaler k =
      let fun go (0, acc) = acc
            | go (n, acc) = go (n - 1, acc + n * k)
      in go end
    val s3 = scaler 3 (10, 0)
    val s5 = scaler 5 (10, 0)
  in
    print ("@@closure_scaler=" ^ Int.toString s3 ^ "," ^ Int.toString s5 ^ "\n")
  end;

(* 6. a small polymorphic STACK library used at int and string in the same scope *)
val () =
  let
    datatype 'a stack = Stk of 'a list
    val empty = Stk []
    fun push (Stk xs) x = Stk (x :: xs)
    fun pop (Stk []) = NONE
      | pop (Stk (x :: xs)) = SOME (x, Stk xs)
    fun depth (Stk xs) = length xs
    val si = push (push (push empty 1) 2) 3
    val ss = push (push empty "a") "b"
    val (topI, _) = valOf (pop si)
    val (topS, _) = valOf (pop ss)
  in
    print ("@@poly_stack_two_types=" ^ Int.toString topI ^ ":" ^ Int.toString (depth si) ^
           ";" ^ topS ^ ":" ^ Int.toString (depth ss) ^ "\n")
  end;

(* 7. nested local..in..end with redefinitions at each level; final uses outermost helper *)
val () =
  let
    fun f x = x + 1
    val a = f 0
    val r =
      let
        fun f x = x * 10  (* shadow *)
        val b = f 2
        val inner =
          let fun f x = x - 3 in f 100 end  (* shadow again *)
      in
        b + inner
      end
    val final = f a + r  (* outer f again: f(1)=2 *)
  in
    print ("@@nested_local_shadow=" ^ Int.toString final ^ "\n")
  end;

(* 8. polymorphic map written by hand, instantiated at int->int and int->string *)
val () =
  let
    fun mymap f [] = []
      | mymap f (x :: xs) = f x :: mymap f xs
    val ints = mymap (fn x => x * x) [1,2,3,4]
    val strs = mymap (fn x => Int.toString x ^ "x") [5,6,7]
  in
    print ("@@poly_map_two_inst=" ^ String.concatWith "," (mymap Int.toString ints) ^
           "|" ^ String.concatWith "," strs ^ "\n")
  end;

(* 9. polymorphic compose used to build int-pipeline and string-pipeline *)
val () =
  let
    fun compose f g = fn x => f (g x)
    val inc = fn x => x + 1
    val dbl = fn x => x * 2
    val ipipe = compose inc (compose dbl inc)   (* x => (2*(x+1))+1 *)
    val toTag = fn s => "[" ^ s ^ "]"
    val spipe = compose toTag (compose toTag Int.toString)
  in
    print ("@@poly_compose=" ^ Int.toString (ipipe 5) ^ "|" ^ spipe 9 ^ "\n")
  end;

(* 10. val rec building a closure over a ref counter; let-bound state, scoping of the ref *)
val () =
  let
    val counter = ref 0
    fun bump () = (counter := !counter + 1; !counter)
    val a = bump ()
    val b = bump ()
    val nested =
      let val counter = ref 100 in (counter := !counter + 7; !counter) end
    val c = bump ()  (* outer counter must continue from 2 -> 3 *)
  in
    print ("@@ref_scope_counter=" ^ Int.toString a ^ "," ^ Int.toString b ^ "," ^
           Int.toString nested ^ "," ^ Int.toString c ^ "\n")
  end;

(* 11. polymorphic option-default helper at three types; ensures generalization not monomorphized *)
val () =
  let
    fun getOr d NONE = d | getOr d (SOME v) = v
    val i = getOr 0 (SOME 55)
    val s = getOr "none" NONE
    val b = getOr false (SOME true)
  in
    print ("@@poly_getOr=" ^ Int.toString i ^ "/" ^ s ^ "/" ^ Bool.toString b ^ "\n")
  end;

(* 12. mutual recursion with an accumulator AND a shadowed helper name inside; ackermann-ish but bounded *)
val () =
  let
    fun a 0 n = n + 1
      | a m 0 = a (m - 1) 1
      | a m n = a (m - 1) (a m (n - 1))
  in
    print ("@@ackermann_2_3=" ^ Int.toString (a 2 3) ^ ",@@hidden=" ^ Int.toString (a 3 3) ^ "\n")
  end;

(* 13. let-poly with the value restriction: a fn ('a list) is generalizable; a partially-applied is not.
       Use eta-expanded forms so both are polymorphic; instantiate at two types. *)
val () =
  let
    val singleton = fn x => [x]
    fun firstOf xs = hd xs
    val li = singleton 123
    val ls = singleton "abc"
  in
    print ("@@poly_singleton=" ^ Int.toString (firstOf li) ^ "/" ^ firstOf ls ^ "\n")
  end;

(* 14. a fold written generic over both element and accumulator type; used to sum ints and concat strings *)
val () =
  let
    fun myfold f acc [] = acc
      | myfold f acc (x :: xs) = myfold f (f (x, acc)) xs
    val sum = myfold (fn (x, a) => x + a) 0 [1,2,3,4,5]
    val cat = myfold (fn (x, a) => a ^ x) "" ["a","b","c","d"]
    val cnt = myfold (fn (_, a) => a + 1) 0 [true,false,true]
  in
    print ("@@poly_fold=" ^ Int.toString sum ^ "/" ^ cat ^ "/" ^ Int.toString cnt ^ "\n")
  end;

(* 15. heavily nested closures capturing distinct let-bound vars; ensures each closure keeps its own env *)
val () =
  let
    fun makeAdder n = fn x => x + n
    val add3 = makeAdder 3
    val add10 = makeAdder 10
    val adders = [makeAdder 1, makeAdder 2, makeAdder 3, makeAdder 4]
    val applied = List.map (fn g => g 100) adders
  in
    print ("@@closure_adders=" ^ Int.toString (add3 (add10 0)) ^ ";" ^
           String.concatWith "," (List.map Int.toString applied) ^ "\n")
  end;

(* 16. where-type-ish via let: an abstract "ordered set" built locally on int, then on string *)
val () =
  let
    fun insert cmp x [] = [x]
      | insert cmp x (y :: ys) =
          (case cmp (x, y) of
               LESS => x :: y :: ys
             | EQUAL => y :: ys
             | GREATER => y :: insert cmp x ys)
    fun isort cmp xs = List.foldl (fn (x, acc) => insert cmp x acc) [] xs
    val si = isort Int.compare [5,3,8,3,1,9,5,2]
    val ss = isort String.compare ["pear","apple","fig","apple","date"]
  in
    print ("@@poly_ordset=" ^ String.concatWith "," (List.map Int.toString si) ^ "|" ^
           String.concatWith "," ss ^ "\n")
  end;

(* 17. deep shadowing inside a big case expression; verify the matched branch binds correctly *)
val () =
  let
    datatype shape = Circle of int | Rect of int * int | Tri of int * int * int
    fun area s =
      case s of
          Circle r => 3 * r * r       (* pi~=3 to stay integer/deterministic *)
        | Rect (w, h) => w * h
        | Tri (a, b, c) => let val s = (a + b + c) in s * s div 4 end  (* shadows outer s *)
    val shapes = [Circle 5, Rect (4, 6), Tri (3,4,5)]
    val areas = List.map area shapes
  in
    print ("@@case_shadow_area=" ^ String.concatWith "," (List.map Int.toString areas) ^ "\n")
  end;

(* 18. polymorphic queue (two stacks) exercised at int and char; depth + dequeue order *)
val () =
  let
    datatype 'a queue = Q of 'a list * 'a list
    val emptyq = Q ([], [])
    fun enq (Q (f, b)) x = Q (f, x :: b)
    fun deq (Q ([], [])) = NONE
      | deq (Q ([], b)) = deq (Q (rev b, []))
      | deq (Q (x :: f, b)) = SOME (x, Q (f, b))
    fun drain q =
      case deq q of NONE => [] | SOME (x, q') => x :: drain q'
    val qi = enq (enq (enq emptyq 1) 2) 3
    val qc = enq (enq emptyq #"a") #"b"
    val di = drain qi
    val dc = drain qc
  in
    print ("@@poly_queue=" ^ String.concatWith "," (List.map Int.toString di) ^ "|" ^
           String.implode dc ^ "\n")
  end;
