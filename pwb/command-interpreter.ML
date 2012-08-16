(* uses pwb/missing,
        pwb/missing-io,
        pwb/tupling,
        pwb/data/maps
*)


signature COMMAND_INTERPRETER =
sig
  type inputstream

  val isReady : inputstream -> bool
  val isEnd   : inputstream -> bool
  val read    : inputstream -> char * inputstream
  val peek    : inputstream -> char

  type interpreter
  type state

  (* Given current interpreter state and an input,
     output an action to be carried out if the command was
     read correctly *)
  type command =
    interpreter -> inputstream -> (unit -> interpreter)

  val make              : unit -> interpreter
  val addCommand        : interpreter -> string -> command -> interpreter
  val getState          : interpreter -> state
  val setState          : interpreter -> state -> interpreter
  val setPrompt         : interpreter -> string -> interpreter
  val readCommands      : interpreter -> inputstream -> interpreter
  val readEvalPrintLoop : interpreter -> inputstream ->
                                interpreter * inputstream
  val flagExit          : interpreter -> interpreter
  val output            : interpreter -> string -> interpreter
end;


functor ParsedCommandInterpreter(A:
  sig
    type inputstream

    val isReady : inputstream -> bool
    val isEnd   : inputstream -> bool
    val read    : inputstream -> char * inputstream
    val peek    : inputstream -> char

    type state
    val makeState : unit -> state
  end) : COMMAND_INTERPRETER =
struct
  open Tupling open Missing open A

  structure T = CharListTrie

  datatype interpreter = Int of
     ( (interpreter -> inputstream ->
                    (unit -> interpreter)) T.map
                        (* 1, the command list *)
     * state            (* 2, the state *)
     * string           (* 3, the prompt *)
     * bool             (* 4, the flag for exiting the interpreter *)
     )


  fun getState (Int i)       = get2of4 i
  fun setState (Int i) state = Int (set2of4 i state)
  fun setPrompt (Int i) str  = Int (set3of4 i str)
  fun make ()                = Int (T.empty,makeState(),"",false)


  type command =
    interpreter -> inputstream -> (unit -> interpreter)

  fun addCommand (Int i) name cmd =
    Int $ upd1of4 i (fn cmds =>
        T.add cmds (String.explode name) cmd)

  fun flagExit (Int i) = Int $ set4of4 i true

  fun output _ _ = Err.undefined ()

  fun printPrompt (Int i) = output (Int i) (get3of4 i)

  fun discard s =
    if isReady s andalso not (isEnd s)
        then (discard o snd o read) s
        else s

  fun readEvalPrintLoop _ _ = Err.undefined ()
  fun readCommands _ _ = Err.undefined ()

  (*

  fun cmndTerm r = stok ";" >> return r
  fun vacious interp = ws >> eof (true, interp)
  fun commandParser (interp as (Interpreter (cmnds,_,_))) =
    ((List.foldr choice zero
                (map (fn (Command cmnd) =>
                        ws >> cmnd interp) cmnds)) >>= cmndTerm)
    </choice/>
        (vacious interp)
    </choice/>
        error "Unrecognised input"

  fun parserMsg (Fail m) = m
    | parserMsg (Error m) = m

  fun outputParseErr msg = (
    out "Error: ";
    out (parserMsg msg);
    out "\n"
  )


  fun readEvalPrintLoop (interp as (Interpreter (cmnds, state, prompt)))
                        stream =
  let
    fun loop interp stream =
    let
      val commands = commandParser interp
      val () = printPrompt interp
      val res = parse commands stream
    in
      if Stream.isEnd stream then (interp, stream) else
      case res of
           RIGHT [((true,interp'),s)]  => (interp', s)
         | RIGHT [((false,interp'),s)] => loop interp' s
         | LEFT ((msg,s)::_) =>
             let
               val () = outputParseErr msg
             in
               loop interp (discard s)
             end
         | _ => Err.error "Unhandled case in readEvalPrintLoop"
    end
  in
    loop interp stream
  end

  fun readCommands interp stream =
  let
    fun commands interp =
        (eof interp)
      </choice/>
        ((commandParser interp) >>=
        (fn (true, interp')  => return interp'
          | (false, interp') => commands interp'))
  in
    case parse (commands interp) stream of
         LEFT ((msg,s)::_) => raise (General.Fail (parserMsg msg))
       | RIGHT ((interp,s)::_) => interp
       | _ => Err.error "Undefined case in readCommands"
  end
  *)

end;


  (*[> Some example/test code <]*)

  (*
structure TestTest =
struct
  structure TestParser = Parser(ParserStreamIO)

  structure TestParsedCommandInterpreter = ParsedCommandInterpreter(
  struct
    open Missing
    structure CommandParser = TestParser
    type state = unit
    fun make () = ()
  end);
  open TestParser
  open TestParsedCommandInterpreter
  fun captureStdIn () = ParserStreamIO.make TextIO.stdIn

  fun makeInterp () =
  let
    val interp = make ()
    val interp = setPrompt interp "Psi> "
    fun exitC () = str "exit" >> return (true,())
    fun sayHelloC () = str "hello" >>
      delayed (fn () => (print "You typed hello!\n"; return (false, ())))
    val interp = addCommands interp [exitC, sayHelloC]
  in
    interp
  end

  fun start () =
     readEvalPrintLoop (makeInterp ()) (captureStdIn ())

  fun readTest () =
    MissingIO.withOpenFile "test.txt"
      (fn is =>
        (readCommands (makeInterp ()) (ParserStreamIO.make is); ()) )
end;


fun start () =
let
  val _ = TestTest.start ()
in
  ()
end;

[>start ();<]
TestTest.readTest ();


*)
