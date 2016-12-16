(* uses pwb/parser,
        pwb/missing,
        pwb/psi
 *)

signature PSI_PARSER =
sig
  structure Parser : PARSER
  structure Psi    : PSI
  structure Cl     : PSI_CLAUSE
  sharing Cl.Psi = Psi

  val agent              : unit -> Psi.psi Parser.parser
  val term               : Psi.Inst.term Parser.parser
  val name               : Psi.Inst.name Parser.parser
  val processConstant    : unit -> string Parser.parser
  val processClause      : unit -> Cl.clause Parser.parser
  val processClauses     : unit -> (Cl.clause list) Parser.parser
  val onlyProcessClauses : unit -> (Cl.clause list) Parser.parser

  val t  : string -> string Parser.parser
  val ws : char list Parser.parser
end;

signature PSI_PARSER_REQ =
sig
  structure Psi : PSI
  val parseName : string -> (string, Psi.Inst.name) Either.either
  val parseTerm : string -> (string, Psi.Inst.term) Either.either
  val parseCond : string -> (string, Psi.Inst.condition) Either.either
  val parseAssr : string -> (string, Psi.Inst.assertion) Either.either
  val var       : (Psi.Inst.name -> Psi.Inst.term) option
end;


functor PsiLexerParserComb(P: PARSER) :
sig
  val identifier    : string P.parser
  val ws            : char list P.parser
  val literal       : string P.parser
  val singleWS      : unit P.parser
  val stok          : string -> unit P.parser
end =
struct
  open Missing
  open P


  val sp = sat Char.isSpace

  (* TODO: this accepts empty sequence of characters *)
  val space = many $ sat Char.isSpace

  val nl = #"\n"
  val inlineComment =
    str "--" >> until (chr nl) >> chr nl >> return ()

  fun nestedComment () =
  let
    fun any () =    (delayed nestedComment >> delayed any)
      </choice/>    ((try (str "*)")) >> return ())
      </choice/>    (item >> delayed any)
  in
    str "(*" >> delayed any >> str "*)" >> return ()
  end

  fun comment () = inlineComment
    </choice/>  delayed nestedComment


  val emptyWS = [] : char list

  fun ws' () =
               (space >> comment () >> delayed ws' >> space >> return emptyWS)
    </choice/> (space >> return emptyWS)

  val ws = delayed ws'

  val singleWS =
    (sp >> return ()) </choice/> comment ()

  fun isAlphaNumeric c =
    Char.isAlphaNum(c) orelse c = #"_"

  val identifier' =
                ws >> many1 (sat isAlphaNumeric) >>=
    (fn r =>    many (sat (op = /> #"'")) >>=
    (fn x =>    return (r @ x)
    ))

  val identifier = identifier' >>= return o String.implode

  fun escape beg esc escSym ennd =
    let
      fun rest x =
                    (esc >>= (fn e => rest (escSym::x)))
        </choice/>  (ennd >> return x)
        </choice/>  (item >>= rest o ((op ::) /> x))
    in
      ws >> beg >> rest [] >>= return o reverse
    end

  val doubleQuoteLiteral = escape (chr #"\"") (str "\\\"") (#"\"") (chr #"\"")
  val singleQuoteLiteral = escape (chr #"'") (str "\\'") (#"'") (chr #"'")
  val unescapeLiteral    = escape (str "{*") zero #" " (str "*}")

  val literal' =    doubleQuoteLiteral
       </choice/>   singleQuoteLiteral
       </choice/>   unescapeLiteral

  val literal =     (literal' >>= return o String.implode)
       </choice/>   identifier

  fun stok s =
                    (ws >> str s >> return ())
       </choice/>   (P.fail (s ^ " expected"))
end;


functor PsiParser
    (A:
    sig
      structure Parser : PARSER
      structure Req    : PSI_PARSER_REQ
      structure Cl : PSI_CLAUSE
      sharing Req.Psi = Cl.Psi
    end) : PSI_PARSER
=
struct
  structure Psi    = A.Req.Psi
  structure Parser = A.Parser
  structure B      = PsiLexerParserComb(Parser)
  structure Cl     = A.Cl
  open B
local
  open Missing
  open A.Req
  open Parser
  open Psi
in

  fun parseLiteral p = literal >>= (Either.either (Parser.fail) return) o p
  val name = parseLiteral parseName
  val assr = parseLiteral parseAssr
  val cond = parseLiteral parseCond
  val term = parseLiteral parseTerm


  fun tok p = ws >> p >>= (fn x => ws >> return x)
  val t = tok o str


  fun processConstant () = identifier

  fun nill () = t "0" >> return Nil

  and tau () = t "*tau*" >> return Tau

  and inputSubj () = ws >> term

  and inputObjFull () =
                t "(" >> t "\\" >> nofail $
                name </sepby1/> (t ",") >>=
    (fn xvec => t ")" >>
                term </sepby1/> (t ",") >>=
    (fn n    => return (xvec, n)))


  and inputObjAbr () =
                t "(" >>
                name </sepby1/> (t ",") >>=
    (fn x =>    nofail $ t ")" >>
                (case A.Req.var of
                     NONE => Parser.fail
                        ("Abbreviated form of Input is not supported" ^
                         " by the instance!")
                   | SOME v => return (x, List.map v x))
    )

  and inputObj () = inputObjFull () </choice/> inputObjAbr ()

  and input () =
                           inputSubj () >>=
    (fn m =>               inputObj  () >>=
    (fn (xvec, nvec) =>    return (fn p => Input (m, xvec, nvec, p))
    ))

  and brinput () =
                           inputSubj () >>=
    (fn m =>   t "?" >>    inputObj  () >>=
    (fn (xvec, nvec) =>    return (fn p => BrInput (m, xvec, nvec, p))
    ))

  and output () =
                t "'" >> nofail $
                term >>=
    (fn m =>    (t "<" >> term </sepby1/> (t ",") >>=
    (fn nvec => t ">" >>
                return (fn p => Output (m, nvec, p))))
    </choice/>  (t "!<" >> term </sepby1/> (t ",") >>=
    (fn nvec => t ">" >>
                return (fn p => BrOutput (m, nvec, p)))))

  and prefix' () = tau () </choice/> output () </choice/> input () </choice/> brinput ()
  and prefix  () =
                prefix' () >>=
    (fn p =>    ((t "." >> nofail $
                (delayed $ restrictedAgent ["parallel"])) </choice/> return Nil)  >>=
                return o p)

  and caseClause () =
                cond >>=
    (fn cond => t ":" >> nofail $
                delayed (restrictedAgent []) >>=
    (fn p =>    return (cond, p)
    ))

  and caseAgent () =
                t "case" >> nofail $
                caseClause () </sepby1/> (t "[]") >>=
    (fn cs =>   return (Case cs)
    )

  and restriction () =
                t "(" >> t "new" >> nofail $
                    (name </sepby1/> (t ",")) >>=
    (fn ns =>   t ")" >>
                delayed (restrictedAgent ["parallel"]) >>=
    (fn a =>    return (List.foldr Restriction a (Lst.reverse ns))
    ))

  and replication () =
                t "!" >> nofail $ delayed (restrictedAgent ["replication", "parallel"]) >>=
                return o Replication

  and par () =
        (delayed $ restrictedAgent ["parallel"])
    </rightAssocOp1/>
        (t "|" >> return Parallel)

  and assertion () =
                t "(|" >> nofail $
                assr >>=
    (fn psi =>  t "|)" >>
                return (Assertion psi)
    )

  and parens () =
                t "(" >>
                delayed agent >>=
    (fn a =>    nofail $
                t ")" >>
                return a
    )

  and invocation () =
                processConstant () >>=
    (fn a =>    t "<" >> nofail $
                (term </sepby/> (t ",")) >>=
    (fn mvec => t ">" >>
                return (Invocation (a, mvec))
    ))

  (* From the lowest to the highest priority *)
  and agentProds () =
  ("parallel"    , par            ()) ::
  ("restriction" , restriction    ()) ::
  ("replication" , replication    ()) ::
  ("parens"      , parens         ()) ::
  ("prefix"      , prefix         ()) ::
  ("case"        , caseAgent      ()) ::
  ("invocation"  , invocation     ()) ::
  ("assertion"   , assertion      ()) ::
  ("nil"         , nill           ()) ::
  []


  and restrictedAgent l () =
    List.foldr choice (fail "Agent expected") $
        map snd $
            (filter (not o (flip member) l o fst) $ agentProds ())

  and agent () = restrictedAgent [] ()


  fun processClause () =
    processConstant () >>= (fn c =>
    nofail (
    stok "(" >>
    (name </sepby/> (stok ",")) >>= (fn names =>
    stok ")" >>
    stok "<=" >> nofail (
    agent () >>= (fn a =>
    ws >> (stok ";") >>
    return (Cl.Clause (c,names,a))
    )))))


  fun processClauses () =
    many (processClause ())

  fun onlyProcessClauses () =
    processClauses () >>= (fn cls =>
    ws >> eof "" >>
    return cls
    )

end
end;

