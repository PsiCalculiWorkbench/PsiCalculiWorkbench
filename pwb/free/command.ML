(* uses pwb/free/instance,
        pwb/free/constraint,
        pwb/parser,
        pwb/pp-psi,
        pwb/psi-parsing,
        pwb/command
 *)

structure FreeTermPrintParseReq'FinSort'ChEq =
struct
  structure Parser = Parser(StringStream)
  structure Lex    = PsiParserBase(Parser)

  fun printN n   = Err.undefined ()
  fun printT m   = Err.undefined ()
  fun printC phi = Err.undefined ()
  fun printA psi = Err.undefined ()

  fun name () = Err.undefined ()
  fun term () = Err.undefined ()
  fun cond () = Err.undefined ()
  fun assr () = Err.undefined ()

  fun parseResult p s =
    case Parser.parse (p ()) (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult term s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s

end;


structure FreeTermParseReq'FinSort'ChEq : PSI_PARSER_REQ =
struct
  structure Psi = FreeTermPsi'FinSort'ChEq
  open FreeTermPrintParseReq'FinSort'ChEq
  val var = SOME FreeTermSymbPsi'FinSort'ChEq.var
end;


structure FreeTermPrinterReq'FinSort'ChEq : PSI_INSTANCE_PRETTY_PRINTER =
struct
  structure Inst = FreeTermPsi'FinSort'ChEq.Inst
  open FreeTermPrintParseReq'FinSort'ChEq
  val var = SOME FreeTermSymbPsi'FinSort'ChEq.var
end;


structure StubCommand = CommandParser(struct
  structure SI           = FreeTermSymbPsi'FinSort'ChEq
  structure SCS          = FreeTermSymbTrCS'FinSort'ChEq
  structure SBCS         = FreeTermSymbBisimCS'FinSort'ChEq
  structure PsiParserReq = FreeTermParseReq'FinSort'ChEq
  structure PPInst       = FreeTermPrinterReq'FinSort'ChEq
  val useBisim           = false (* true if bisimulation constraint solver is
                                    implemented *)
end);



(*structure Stub = StubCommand;*)
(*structure PsiInstance = Stub;*)

