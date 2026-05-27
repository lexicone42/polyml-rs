(* Sieve of Eratosthenes: find primes up to N.
 *
 * Run via:
 *   ./target/release/poly run /tmp/basis_loaded < demos/sieve.sml
 *
 * (Requires basis-loaded checkpoint at /tmp/basis_loaded — see
 *  vendor/polyml comments in CLAUDE.md for how to build it.) *)

fun sieve n =
    let val arr = Array.array (n + 1, true)
        val () = Array.update (arr, 0, false)
        val () = Array.update (arr, 1, false)
        fun mark step start =
            if start > n then ()
            else (Array.update (arr, start, false); mark step (start + step))
        fun loop i =
            if i * i > n then ()
            else
                (if Array.sub (arr, i) then mark i (i + i) else ();
                 loop (i + 1))
        val () = loop 2
        fun collect i acc =
            if i > n then List.rev acc
            else if Array.sub (arr, i) then collect (i + 1) (i :: acc)
            else collect (i + 1) acc
    in collect 2 [] end;

val primes = sieve 100;
print "Primes < 100:\n  ";
List.app (fn p => print (Int.toString p ^ " ")) primes;
print "\n";
print ("Count: " ^ Int.toString (length primes) ^ "\n");
val twin_pairs = List.foldl
    (fn (p, acc) =>
        if List.exists (fn q => q = p + 2) primes
        then (p, p + 2) :: acc
        else acc)
    [] primes;
print "Twin prime pairs < 100:\n  ";
List.app (fn (p, q) =>
    print ("(" ^ Int.toString p ^ "," ^ Int.toString q ^ ") "))
    (List.rev twin_pairs);
print "\n";
