(* uses pwb/missing,
        pwb/parser
 *)

structure ParserExample =
struct
  structure P = Parser(StringStream)

  val stream = StringStream.make

  local open P open Missing in

  val space = many (sat Char.isSpace)

  fun token p =
                    p
    >>= (fn r =>    space
    >>              return r
    )

  fun symb cs = token (str cs)

  fun apply p = space >> p



  val mul = (op * )
  val fra = (op div)
  val add = (op +)
  val sub = (op -)

  fun expr () = term () </leftAssocOp1/> addop ()

  and term () = factor () </leftAssocOp1/> mulop ()

  and factor () = digit () </choice/>
    (            symb "("
    >>           delayed expr
    >>= (fn n => symb ")"
    >>           return n)
    )

  and digit () =
    token (sat Char.isDigit) >>= (fn d =>
    return ((ord d) - (ord #"0")))
  and addop () =
    (symb "+" >> return add) </choice/>
    (symb "-" >> return sub)
  and mulop () =
    (symb "*" >> return mul) </choice/>
    (symb "/" >> return fra)

  val res1 = parse (apply ( expr () )) (stream "1 - 2 * 3 + 4")
  val res2 = parse (apply ( expr () )) (stream "((1 - 2) * 3) + 4")


  datatype 'a sum = Sum of ('a sum * 'a sum) | N of 'a

  val sums = stream "1+2+3+4"

  fun sumDigit () =
    token (sat Char.isDigit) >>= (fn d =>
    return (N $ (ord d) - (ord #"0")))

  fun sumOp () = symb "+" >> return Sum

  fun sumExprL () = sumDigit () </leftAssocOp1/> sumOp () >>= eof
  val res3 = parse (sumExprL ()) sums

  fun sumExprR () = sumDigit () </rightAssocOp1/> sumOp () >>= eof
  val res4 = parse (sumExprR ()) sums

end;
end;
