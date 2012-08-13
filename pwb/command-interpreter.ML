(* uses pwb/missing,
        pwb/parser,
        pwb/pp,
        pwb/psi-parsing,
        pwb/missing-io
*)

signature COMMAND_INTERPRETER =
sig
  type interpreter
  type state
  type command
  type inputstream

  val make              : unit -> interpreter
  val addCommands       : interpreter -> command list -> interpreter
  val getState          : interpreter -> state
  val setState          : interpreter -> state -> interpreter
  val setPrompt         : interpreter -> string -> interpreter
  val readCommands      : interpreter -> inputstream -> interpreter
  val readEvalPrintLoop : interpreter -> inputstream ->
                                interpreter * inputstream
end;


functor ParsedCommandInterpreter(A:
  sig
    structure CommandParser : PARSER
    type state
    val make : unit -> state
  end) : COMMAND_INTERPRETER =
struct
  open A
  open Missing
  structure Lexer = PsiLexerParserComb(CommandParser)
  structure Stream = CommandParser.Stream
  open CommandParser
  open Lexer

  type state = state
  type inputstream = Stream.stream

  datatype command' =
    Command of (interpreter -> (bool * interpreter) CommandParser.parser)
  and interpreter = Interpreter of (command' list * state * string)

  type command = interpreter -> (bool * interpreter) CommandParser.parser


  fun make () = Interpreter ([], A.make (), "")
  fun getState (Interpreter (_,state,_)) = state
  fun setState (Interpreter (cmnds, _, p)) state =
    Interpreter (cmnds, state, p)
  fun setPrompt (Interpreter (cmnds, state, prompt)) prompt' =
    Interpreter (cmnds, state, prompt')
  fun addCommand (Interpreter (cmnds, state, prompt)) cmd =
    Interpreter ((Command cmd)::cmnds, state, prompt)
  fun addCommands interp cmnds =
    List.foldr (uncurry (flip addCommand)) interp cmnds

  fun out s = print s
  fun printPrompt (Interpreter (_,_,prompt)) = out prompt

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

  fun discard s =
    if Stream.isReady s andalso not (Stream.isEnd s)
        then (discard o snd o always id o Stream.head) s
        else s

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

end;


(*
  (* Some example/test code *)

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
    val interp = addCommand (addCommand interp exitC) sayHelloC
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

(*start ();*)
TestTest.readTest ();


*)

