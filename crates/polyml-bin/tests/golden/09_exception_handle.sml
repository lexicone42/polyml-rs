exception Oops;
val it = (raise Oops) handle Oops => 42;
