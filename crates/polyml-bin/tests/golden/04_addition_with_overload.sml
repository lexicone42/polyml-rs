(* Install the infix declaration and `+` overload manually
   (Stage1.sml would normally do this via basis/InitialBasis.ML). *)
infix 6 + -;
RunCall.addOverload FixedInt.+ "+";
val x = 1 + 2;
