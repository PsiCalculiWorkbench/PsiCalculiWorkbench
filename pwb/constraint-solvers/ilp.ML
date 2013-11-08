(* uses pwb/missing,
        pwb/missing-io,
        pwb/pp,
        pwb/parser
*)


(*
 * Integer Linear Programming
 *)
signature ILP =
sig
  type var = string

  datatype rel = Eq | Lt | Gt | LtE | GtE

  type equation =
    ((int * string) list) * rel * ((int * string) list)

  type equation_system=
    equation list

  type solution = (var * int) list

  val solve : equation_system -> (string, solution) Either.either
end;





structure LPSolveSolver : ILP =
struct
  open Missing
  open MissingIO
  open WPrettyPrinter
  structure PPA = PrettyPrinterAux(WPrettyPrinter)
  open PPA
  structure P = Parser(ParserStreamIO)
  (*structure P = Parser(StringStream)*)
  open P

  type var = string

  datatype rel = Eq | Lt | Gt | LtE | GtE

  (* Empty string as var means only use the coefficient *)
  type equation =
    ((int * string) list) * rel * ((int * string) list)

  type equation_system=
    equation list

  type solution = (var * int) list


  fun varsLin lin = map snd lin |> filter (fn "" => false | _ => true)

  fun vars sys = nub $ flatmap (fn (l,_,r) => varsLin l @ varsLin r) sys

  val intT = text o Int.toString

  fun ppLin lin =
    map (fn (k, "") => intT k
          | (k, x) => intT k </sp/> text "*" </sp/> text x) lin |>
    sep (text " " </join/> text "+" </join/> text " ")

  fun txtRel rel =
    case rel of
         Eq => "="
       | Lt => "<"
       | Gt => ">"
       | LtE => "<="
       | GtE => ">="

  fun ppEq (lhs, rel, rhs) =
    ppLin lhs </sp/> text (txtRel rel) </sp/> ppLin rhs

  fun ppSys' sys =
    map ppEq sys |>
    map (fn (e) => e </join/> text ";") |>
    sep line

  fun ppIntVars vars = text "int" </sp/> sep comma (map text vars)

  fun ppSys sys =
    text "min:;" </nl/> ppSys' sys </nl/> ppIntVars (vars sys)
                </join/> text ";" </join/> line

  fun stringify sys = ppSys sys |> pretty 80

  val ws = many (sat Char.isSpace) >> return ()

  val intP = many1 (sat Char.isDigit) >>=
    return o always id o Int.fromString o String.concat o map Char.toString

  val varP = many1 (sat Char.isAlpha) >>=
    return o String.concat o map Char.toString

  val solP =    varP >>=
    (fn var =>  ws >>
                intP >>=
    (fn vl  =>  ws >>
                return (var,vl)))

  val vobf = "Value of objective function:"
  val avotv = "Actual values of the variables:"

  val solParser =
    ws >> str vobf >> ws >>
        intP >> ws >> str avotv >> ws >>
        many solP (* >>= (fn s => ws >> eof s) *)

  val s = [
            ([ (1, "x"), (2, "y") ], Eq, [ (2, "x"), (1, "z") ]),
            ([ (1, "u"), (2, "z") ], Eq, [ (1, "z") ]),
            ([ (1, "y") ], Eq, [(2, "")] )
          ]


  fun runLpSolve sys =
  let
    val result = ref (LEFT "")
    val succ =
    inOutFSytem
      (fn inp => fn outp => "lp_solve < " ^ inp ^ " > " ^ outp)
      (fn out => TextIO.output (out, stringify sys))
      (fn i =>
          let
            val p = parse solParser (ParserStreamIO.make i)
            val v = case p of
                         RIGHT (res,_) => RIGHT res
                       | LEFT (Error msg,_) => LEFT msg
                       | LEFT _ => LEFT ""
            val _ = result := v
          in
            ()
          end)
    in
      if succ
        then !result
        else LEFT "lp_solve failed to run"
    end

  fun solve sys = runLpSolve sys


  (*val s = inOutFSytem*)
    (*(fn inp => fn outp => "lp_solve < " ^ inp ^ " > " ^ outp)*)
    (*(fn out => TextIO.output (out, stringify s))*)
    (*(fn i =>*)
        (*let*)
          (*val p = parse solParser (ParserStreamIO.make i)*)
          (*val _ = PolyML.print_depth 100*)
          (*val _ = PolyML.print p*)
        (*in*)
          (*()*)
        (*end*)
    (*)*)


  (*val tst = "Value of objective function: 22\n\nActual values of the variables:\nx                               4\ny                               2\nz                               0\nu                               0\n"*)
  (*val p = parse solParser (StringStream.make tst)*)
  (*val _ = PolyML.print_depth 100*)
  (*val _ = PolyML.print p*)



  (*val _ = PolyML.print_depth 100;*)
  (*val _ = PolyML.print (solve s)*)
end;

