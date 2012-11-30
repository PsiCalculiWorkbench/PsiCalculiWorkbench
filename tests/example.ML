(* uses pwb/missing *)

(* Tests are loaded using pwb module system. Tests can use this to preload
 * requirements as above. *)

(* Let's define the tests *)

val t1 = PwbTestRunner.testTrue "2 + 2 = 4" (fn () => 2 + 2 = 4);

val t2 = PwbTestRunner.testTrue 
    "Test which fails because of an exception raised"
    (fn () => raise (Fail "Exception"));

(* Now register them with the test runner *)
PwbTestRunner.registerTests [t1, t2];

