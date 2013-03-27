(* uses pwb/missing,
        pwb/missing-io,
        pwb/parser
 *)


functor DIMACSParser(P : PARSER) =
struct
  open Missing
  open P

  val sp = sat (fn c => Char.isSpace c andalso c <> #"\n")
  val ws = many sp
  val sep = many1 sp
  val eol = str "\n"

  fun num () = many1 (sat Char.isDigit) >>= 
    return o always id o Int.fromString o String.implode

  fun format () = ws >> str "p" >> sep >> str "cnf" >> sep >> 
    num () >>=
    (fn variables => sep >> num () >>=
    (fn clauses => ws >> return (variables, clauses)))

  fun comment () = 
    str "c" >> until (eol </choice/> eof "")


  val clSp = sat Char.isSpace
  val clWS = many clSp
  val litSep = many1 clSp
  val clSep = clWS >> str "0"

  fun nnum () = 
    try (clWS >> notP (str "0") NONE) >>
        (((str "-" >> return (~1)) </choice/> (return 1)) >>=
        (fn x => num () >>=
        (fn n => return (x * n))))

  fun clause () = clWS >> 
    (nnum () </sepby1/> litSep) >>=
    (fn x => clWS >> return x)

  fun clauses () = clause () </sepby/> clSep

  fun dimacs () =
                    (comment () </sepby/> eol) >> eol >>
                    format () >>=
    (fn (vs,cls) => eol >> clauses () >>=
    (fn cnf => return (vs, cls, cnf)))
end;

structure DIMACSFileParser =
struct
  structure P = Parser(ParserStreamIO)
  structure DP = DIMACSParser(P)
  open DP

  fun parseStream ins = P.parse (DP.dimacs ()) (ParserStreamIO.make ins)

  fun parseFile filename =
    MissingIO.withOpenFile filename parseStream
end;


(*PwbSml.restoreOutput ();*)
(*PolyML.print ( *)
(*DIMACSFileParser.parseFile "/Users/ramunasgutkovas/Desktop/ex.cnf"*)
(* );*)

(*structure SP = Parser(StringStream);*)
(*structure DP = DIMACSParser(SP);*)

(*PwbSml.restoreOutput ();*)
(*PolyML.print (SP.parse (DP.clause () ) (StringStream.make "1 2 3 0 2"));*)
(*PolyML.print (SP.parse (DP.clauses () ) (StringStream.make "1 2 3 0 4\n5 0 6"));*)
(*PolyML.print (SP.parse (DP.nnum () ) (StringStream.make "0"));*)
(*PolyML.print (SP.parse (DP.nnum () ) (StringStream.make "1"));*)
(*PolyML.print (SP.parse (DP.nnum () ) (StringStream.make "~1"));*)
(*PolyML.print (SP.parse (DP.sep ) (StringStream.make "  "));*)
(*PolyML.print (SP.parse (DP.num ()) (StringStream.make "4"));*)
(*PolyML.print (SP.parse (DP.format ()) (StringStream.make "p cnf 4 3"));*)


