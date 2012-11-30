(* uses pwb/missing,
        pwb/missing-io,
        pwb/pwb-logger
 *)


structure PwbTestRunner : 
sig
  type test

  (* Add tests to the list of tests to run *)
  val registerTests : test list -> unit
  (* Make a test which return true if passed *)
  val testTrue : string -> (unit -> bool) -> test
  (* Likewise, but returns false *)
  val testFalse : string -> (unit -> bool) -> test

  val testSome : string -> (unit -> 'a option) -> test
  val testNone : string -> (unit -> 'a option) -> test
  val testLeft : string -> (unit -> ('a,'b) Either.either) -> test
  val testRight : string -> (unit -> ('a,'b) Either.either) -> test

  (* Run all the tests in the given directory.
   *
   * Tests are SML files with .ML suffix which uses the above functions to
   * define unit tests. Only registered tests are run.
   *
   * The test directory is flat. This function does not recurse into the
   * subdirectories.
   *)
  val runAllInDir : string -> unit
  (* An alias for the above *)
  val run : string -> unit

  (* Only run those test files which have the given prefix in the given
   * directory.
   *)
  val runPrefixInDir : string -> string -> unit

  (* The logger name used to log the output of the results of the above
   * functions. (see pwb/pwb-logger) *)
  val loggerName : string

end =
  (* NB: This structure uses stateful variables (refs). It is not
   * intended to be run in parallel. *)
struct
  open Missing
  open MissingIO

  type test = string * (unit -> bool)
  type tests = test list

  val tests : tests ref = ref []

  fun registerTests test = tests := test @ (!tests)
  fun resetTests () = tests := []
  fun getTests () = !tests

  val failed = ref 0
  val passed = ref 0

  fun resetCounters () = (failed := 0; passed := 0)
  fun incFailed () = failed := (!failed) + 1
  fun incPassed () = passed := (!passed) + 1
  fun getFailed () = !failed
  fun getPassed () = !passed

  val i = Int.toString

  val loggerName = "PwbTestRunner"
  fun log msg = PwbLog.write loggerName msg

  fun runTest (name, test) =
    (if test ()
        then (log ("PASS test '" ^ name ^ "'"); incPassed ())
        else (log ("FAIL test '" ^ name ^ "'"); incFailed ()))
    handle x =>
        (log ("FAIL test '" ^ name ^ "' exception '"
            ^ (exnName x) ^ "' captured with the message '"
            ^ (exnMessage x) ^ "'");
         incFailed ())

  fun mlFiles f dir =
    readDirFiles dir |>
    filter (String.isSuffix ".ML") |>
    filter f |>
    map (fn f => OS.Path.concat (dir,f))


  fun runTestForFile file =
  let
    val () = resetCounters ()
    val () = resetTests ()
    val () = log ("Loading tests in the file '" ^ file ^ "'")
    val () = Uses.uses ("@" ^ file)
    val () = forall runTest (getTests ())

    val f  = getFailed ()
    val p  = getPassed ()
    val () = log (i (f + p) ^ " test(s) run of which " ^ (i f) ^ " failed and " ^
                 (i p) ^ " passed")
  in
    ()
  end

  val totalFailed = ref 0
  val totalPassed = ref 0
  val totalFilesFailed = ref 0
  fun incFilesFailed () = totalFilesFailed := (!totalFilesFailed) + 1
  fun resetTotals () =
    (totalFailed := 0; totalPassed := 0; totalFilesFailed := 0)
  fun runTestForFileWithCounters file =
    ( ((runTestForFile file) 
        handle x => 
            (incFilesFailed ()
            ; log ("Exception '"^ (exnName x) ^"' was cought with the message '"
                  ^ (exnMessage x) ^"' while loading '"^ file ^"'")))
    ; totalFailed := (!totalFailed) + (getFailed ())
    ; totalPassed := (!totalPassed) + (getPassed ())
    )

  fun runFiles' files = files |> forall runTestForFileWithCounters
  fun runFiles files =
    ( resetTotals ()
    ; runFiles' files
    ; log ("*** Summary: " ^ (i (!totalFailed)) ^ " test(s) failed, "
                      ^ (i (!totalPassed)) ^ " test(s) passed, "
                      ^ (i (!totalFilesFailed)) ^ " test file(s) failed to load.  ***")
    )

  fun runFilterInDir f dir = mlFiles f dir |> runFiles
  fun runAllInDir dir = runFilterInDir (const true) dir
  fun runPrefixInDir prfx dir = runFilterInDir (prfx <// String.isPrefix) dir

  val run = runAllInDir

  fun testTrue name test = (name,test)
  fun testFalse name test = (name, fn () => not (test ()))

  fun testSome name test = (name, (fn () => test () |> maybe false (const true)))
  fun testNone name test = (name, (fn () => test () |> maybe true (const false)))

  fun testLeft name test =
    (name, (fn () => test () |> either (const true) (const false)))
  fun testRight name test =
    (name, (fn () => test () |> either (const false) (const true)))

  (*val () = PwbLog.pushLoggerStdOut loggerName*)
end;


