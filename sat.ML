(* uses pwb/missing,
        pwb/constraint-solvers/dimacs,
        pwb/constraint-solvers/pwb-smt,
        pwb/constraint-solvers/pwb-smt-theories
*)

structure PwbSATSolverMain =
struct
  open Missing
  structure DP = DIMACSFileParser

  fun pos s =
  let val (line, column, _) = DP.Stream.pos s in
    "line: "^ Int.toString line ^ " column: " ^ Int.toString column
  end

  fun getMsg (DP.Fail x) = x
    | getMsg (DP.Error x) = x

  fun getParseRes r = 
    case r of
         RIGHT ((x,_)::_) => x
       | RIGHT _ => Err.error "cant happen"
       | LEFT ((msg, stream)::_) => 
           Err.error ("Parse error: "  ^ (getMsg msg) ^" at "^ (pos stream))
       | LEFT _ => Err.error "can't happen"

  fun itos i =
    if i < 0 
        then "-" ^ (Int.toString (Int.abs i))
        else Int.toString i

  fun printSat numVars clauses vars =
    (print ("s cnf 1 " ^ (Int.toString numVars) ^ " " ^ (Int.toString clauses) ^ "\n");
    print "v";
    forall (fn v => print (" " ^ itos v)) vars;
    print "\n")

  fun printUnsat numVars clauses =
    print ("s cnf 0 " ^ (Int.toString numVars) ^ " " ^ (Int.toString clauses) ^ "\n");

  fun printTime sat numVars clauses secs =
    print ("t cnf "^ sat ^ " " ^ (itos numVars) ^ " " ^ (itos clauses) ^ " " ^
    (Real.toString secs) ^ " 0\n")

  fun main () = 
  let
    val (nvars,clauses,cnf) = TextIO.stdIn |> DP.parseStream |> getParseRes
    val timer = Timer.startCPUTimer ()
    val res = PwbSATSolver.sat cnf
    val {usr=usr,sys=sys} = Timer.checkCPUTimer timer
    val secs = Time.toReal usr + Time.toReal sys
  in
    case res of
         NONE => 
         (printUnsat nvars clauses;
           printTime "0" nvars clauses secs)
       | SOME (vars, _) => 
           (printSat nvars clauses vars;
           printTime "1" nvars clauses secs)
  end

  fun exitFail () =
    OS.Process.exit (OS.Process.failure)

  fun start () =
    main () handle err => (print (exnMessage err); print "\n"; exitFail ())
end;

PwbSml.restoreOutput ();
fun start () = PwbSATSolverMain.start ()

