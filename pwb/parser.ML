(* uses pwb/missing
 *)

infixr 0 >>=
infixr 0 >>

signature PARSER_STREAM =
sig
  type stream
  val head : stream -> (char * stream) option
  val isReady : stream -> bool
  val isEnd : stream -> bool

  (* line nr, column nr, character nr *)
  val pos  : stream -> int * int * int
  val resetPos : stream -> stream

  type base_stream
  val make : base_stream -> stream
end;


signature PARSER =
sig
  structure Stream : PARSER_STREAM

  datatype 'a fail = Fail of 'a | Error of 'a
  type 'result parser

  val parse : 'result parser -> Stream.stream ->
              (string fail * Stream.stream, 'result * Stream.stream) Either.either

  val direct  : (Stream.stream ->
                (string fail * Stream.stream,
                 'result * Stream.stream) Either.either) ->
                 'result parser

  val return  : 'a -> 'a parser
  val >>=     : 'a parser * ('a -> 'b parser) -> 'b parser
  val >>      : 'a parser * 'b parser -> 'b parser

  val delayed : (unit -> 'a parser) -> 'a parser
  val error   : string -> 'result parser
  val zero    : 'result parser
  val choice  : 'a parser * 'a parser -> 'a parser
  val eof     : 'a -> 'a parser

  val sPos : (int * int * int) parser

  val item : char parser
  val sat  : (char -> bool) -> char parser
  val chr  : char -> char parser
  val str  : string -> string parser

  val many   : 'a parser -> ('a list) parser
  val many1  : 'a parser -> ('a list) parser
  val sepby  : 'a parser * 'b parser -> 'a list parser
  val sepby1 : 'a parser * 'b parser -> 'a list parser

  val leftAssocOp1  : 'a parser * ('a * 'a -> 'a) parser -> 'a parser
  val leftAssocOp   : 'a parser -> ('a * 'a -> 'a) parser -> 'a -> 'a parser
  val rightAssocOp1 : 'a parser * ('a * 'a -> 'a) parser -> 'a parser
  val rightAssocOp  : 'a parser -> ('a * 'a -> 'a) parser -> 'a -> 'a parser

  val until : 'a parser -> char list parser
  val notP : 'a parser -> 'b -> 'b parser
  val try : 'a parser -> 'a parser
  val nofail : 'a parser -> 'a parser

  val both : 'a parser -> 'b parser -> ('a * 'b) parser

  (* TODO : *)
  (*val streamTrans : 'a parser -> 'a parser*)
end;




functor Parser (S : PARSER_STREAM) : PARSER =
struct
  open S
  open Missing

  structure Stream = S

  datatype 'a fail = Fail of 'a | Error of 'a

  datatype 'a parser = Parser of
     stream -> (string fail * stream, 'a * stream) either


  fun parse (Parser p) = p

  fun direct f = Parser f

  fun delayed f = Parser (fn s => (parse $ f ()) s)

  fun error  e = Parser (fn s => LEFT  (Fail e, s))
  val zero     = Parser (fn s => LEFT  (Fail "zero", s))
  fun return a = Parser (fn s => RIGHT (a, s))

  val sPos = Parser (fn s => RIGHT (Stream.pos s, s))

  fun nofail p = Parser (fn s =>
    case parse p s of
         LEFT (Fail e, s) => LEFT (Error e, s)
       | LEFT (Error e, s) => LEFT (Error e, s)
       | RIGHT r => RIGHT r)

  fun p >>= f  = Parser (fn s =>
    parse p s <//bindE//> (fn (r,s') => parse (f r) s') )

  fun p >> f = p >>= (fn _ => f)

  (* Ordered choice. Tries the first parser, if it succeds returns its result,
  * otherwise tries the second parser and if it succeeds returns its result,
  * and if it fails reutrns the first parser's failure *)
  fun choice (p,q) = Parser (fn s =>
    parse p s |> either (fn fl => parse q s |> either (fn _ => LEFT fl)
                                                      returnE)
                        returnE)

  val item = Parser (fn s =>
    case head s of
         NONE => LEFT (Fail "end of input unexpected", s)
       | SOME (a,s') => RIGHT (a,s') )


  fun eof result = Parser (fn s =>
    case head s of
         NONE => RIGHT (result, s)
       | SOME _ => LEFT (Fail "end of input expected", s) )


  fun sat p =
    item >>= (fn c =>
    if p c
        then return c
        else zero)

  fun chr c =
    (sat (op = /> c)) </choice/> error ("character "
                                       ^(Char.toString c) ^" was expected")

  fun str' [] = return ()
    | str' (s::ss) =
    chr s   >>
    str' ss >>
    return ()

  fun str s =
    (str' (String.explode s) >>
    return s) </choice/> error ("string " ^ s ^ " expected")

  fun until' p s a =
    case parse p s of
         RIGHT _ => RIGHT (a,s)
       | LEFT _ => parse item s |>
                    either LEFT (fn (i,s) => until' p s (i::a))

  fun until p = Parser (fn s => until' p s [])

  fun notP p d = Parser (fn s =>
    case parse p s of
         RIGHT _ => LEFT (Fail "notP", s)
       | LEFT  _ => RIGHT (d,s)
    )

  fun try p = Parser (fn s =>
    case parse p s of
         RIGHT (a,_) => RIGHT (a,s)
       | LEFT err => LEFT err
       )

  fun many p  = many1 p </choice/> return []
  and many1 p =
    p      >>= (fn x  =>
    many p >>= (fn xs =>
    return (x::xs)
    ))


  fun sepby (p, sep) = (p </sepby1/> sep) </choice/> return []
  and sepby1 (p, sep) =
    p               >>= (fn x =>
    many (sep >> p) >>= (fn xs =>
    return (x::xs)))


  fun chainl p oper a = (p </chainl1/> oper) </choice/> return a
  and chainl1 (p, oper) =
  let
    fun rest a =
      (             oper >>=
      (fn f =>      p    >>=
      (fn b =>      rest (f (a, b)) ))) </choice/> return a
  in
    p >>= rest
  end

  val leftAssocOp  = chainl
  val leftAssocOp1 = chainl1


  fun chainr p oper a = (p </chainr1/> oper) </choice/> return a
  and chainr1 (p, oper) =
  let
    fun rest a =
      (             oper >>=
      (fn f =>      p    >>=
      (fn b =>      (rest b </choice/> return b) >>=
      (fn c =>      return (f (a, c))))))
  in
    p >>= rest
  end

  val rightAssocOp  = chainr
  val rightAssocOp1 = chainr1


  fun prod a b =
    List.concat (map (fn el => map (fn el' => (el,el')) b) a)

  fun both p1 p2 = Parser (fn s =>
    (* TODO: the implementation could be a bit more efficient *)
    let
      val r1 = parse p1 s
      val r2 = parse p2 s
    in
      case (r1, r2) of
           (RIGHT (r1',s1) , RIGHT (r2',s2)) =>
            if Stream.pos s1 = Stream.pos s2
                then RIGHT ((r1',r2'),s1)
                else LEFT (Fail "Product parsers did not agree", s)
         | (LEFT e, RIGHT _) => LEFT e
         | (RIGHT _, LEFT e) => LEFT e
         | (LEFT e, LEFT _) =>  LEFT e
    end)

end;



structure StringStream : PARSER_STREAM =
struct
  type pos = int * int * int
  type stream = string * pos

  fun head (s, (l,c,i)) =
    if String.size s = i then
      NONE
    else
      let
        val ch = String.sub (s,i)
        val (l,c) = if ch = #"\n" then (l+1,0) else (l,c+1)
      in
        SOME (ch, (s, (l,c,i+1)))
      end

  fun make s = (s, (1,1,0))
  fun pos (_, p) = p
  fun resetPos (s,_) = make s

  type base_stream = string

  fun isReady _ = true
  fun isEnd (s, (_,_,i)) = String.size s = i
end;


structure StringParser =
struct
  structure P = Parser(StringStream)
  open P

  fun parseString p s = parse p (StringStream.make s)
end;


structure ParserStreamIO: PARSER_STREAM =
struct
  open Missing

  type pos = int * int * int
  type stream = TextIO.StreamIO.instream * pos
  type base_stream = TextIO.instream


  val initPos = (1,1,0)

  fun make bs =
  let
    val (rd, buf) = TextIO.StreamIO.getReader $ TextIO.getInstream bs
  in
    ((TextIO.StreamIO.mkInstream (rd, "")), initPos)
  end

  fun head (s, (line,col,chr)) =
    maybe NONE
        (fn (c,s) =>
            SOME (c, (s,
                if c = #"\n"
                    then (line+1,1,chr+1)
                    else (line,col+1,chr+1))) )
        (TextIO.StreamIO.input1 s)


  fun pos (_,p) = p
  fun resetPos (s,_) = (s,initPos)

  fun isReady (s,_) =
    maybe false (const true) (TextIO.StreamIO.canInput (s,1))

  fun isEnd (s,_) = TextIO.StreamIO.endOfStream s
end;

