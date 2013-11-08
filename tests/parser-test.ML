(* uses pwb/missing,
        pwb/parser,
        pwb/pwb-test
 *)

structure ParserExample =
struct
  open Missing
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


  (* setting up the testing framework *)
  fun testParseResult name p expected =
    PwbTestRunner.testTrue name 
        (fn () => p |> Either.either (const false) 
                       (fn (x,_) => x = expected))


  val res1 = parse (apply ( expr () )) (stream "1 - 2 * 3 + 4")
  val t1 = testParseResult "res1" res1 (~1)

  val res2 = parse (apply ( expr () )) (stream "((1 - 2) * 3) + 4")
  val t2 = testParseResult "res2" res2 (1)



  datatype 'a sum = Sum of ('a sum * 'a sum) | N of 'a

  val sums = stream "1+2+3+4"

  fun sumDigit () =
    token (sat Char.isDigit) >>= (fn d =>
    return (N $ (ord d) - (ord #"0")))

  fun sumOp () = symb "+" >> return Sum

  fun sumExprL () = sumDigit () </leftAssocOp1/> sumOp () >>= eof
  val res3 = parse (sumExprL ()) sums
  (* left associative parsing *)
  val t3 = testParseResult "res3: left associative" res3 
    (Sum (Sum (Sum (N 1, N 2), N 3), N 4))

  fun sumExprR () = sumDigit () </rightAssocOp1/> sumOp () >>= eof
  val res4 = parse (sumExprR ()) sums
  val t4 = testParseResult "res4: right associative" res4
    (Sum (N 1, Sum (N 2, Sum (N 3, N 4))))


  val () = PwbTestRunner.registerTests [t1, t2, t3, t4]
end;
end;

