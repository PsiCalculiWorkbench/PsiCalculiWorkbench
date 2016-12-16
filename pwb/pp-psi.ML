(* uses pwb/missing,
        pwb/parser,
        pwb/psi-parser,
        pwb/pp,
        pwb/psi *)

signature PSI_PRETTY_PRINTER =
sig
  structure PP  : PRETTY_PRINTER
  structure Psi : PSI

  val n : Psi.Inst.name      -> PP.document
  val t : Psi.Inst.term      -> PP.document
  val a : Psi.Inst.assertion -> PP.document
  val c : Psi.Inst.condition -> PP.document

  val ppAgent : Psi.psi -> PP.document

  val ppConstant : string -> PP.document
end;


signature PSI_PP_REQ =
sig
  structure Inst : PSI_INSTANCE

  val printN  : Inst.name      -> string
  val printT  : Inst.term      -> string
  val printC  : Inst.condition -> string
  val printA  : Inst.assertion -> string

  val var     : (Inst.name -> Inst.term) option
end;



functor EscapedPsiInstancePrettyPrinter
    (A: sig
      structure PP     : PRETTY_PRINTER
      structure PPInst : PSI_PP_REQ
    end) :
sig
  structure PPInst : PSI_PP_REQ
  structure PP     : PRETTY_PRINTER
  val n  : PPInst.Inst.name      -> PP.document
  val t  : PPInst.Inst.term      -> PP.document
  val c  : PPInst.Inst.condition -> PP.document
  val a  : PPInst.Inst.assertion -> PP.document
end =
struct
  open Missing
  open A
  open PP
  open PPInst
  structure StringParser = Parser(StringStream)
  structure B = PsiLexerParserComb(StringParser)

  local open StringParser in
  fun escape s =
  let
    val str = StringStream.make s
  in
    (* check if "s" is an identifier *)
    case parse (B.identifier >>= eof) str of
         RIGHT _ => s           (* if yes return unmodified *)
       | LEFT _  => escape' s   (* if no escape *)
  end
  and escape' s =
    "\"" ^ (String.concat $
        map (fn c => if c = #"\"" then "\\\"" else String.str c ) $
            String.explode s) ^ "\""
  end

  fun liftEscape f = text o escape o f

  (* The lifted functions *)
  val t = liftEscape printT
  val n = liftEscape printN
  val c = liftEscape printC
  val a = liftEscape printA
end;



functor PrettyPrintPsi
(A: sig
  structure PP     : PRETTY_PRINTER
  structure PPInst : PSI_PP_REQ
  structure Psi    : PSI
  sharing Psi.Inst = PPInst.Inst
end) : PSI_PRETTY_PRINTER =
struct
  open A
  structure PP  = PP
  structure Psi = Psi
  structure PPA = PrettyPrinterAux(PP)
  structure EPInst = EscapedPsiInstancePrettyPrinter(
  struct
    structure PP = PP
    structure PPInst = PPInst
  end)
  open EPInst
local
  open Missing
  open Psi
  open PP
  open PPA
  open PPInst
in

  fun ppConstant a = text a

  fun collapseNew' (Restriction (a,p)) avec = collapseNew' p (a :: avec)
    | collapseNew' p avec = (avec, p)

  fun collapseNew p = collapseNew' p []

  fun nestIndent d = nest 2 d

  fun enclose a doc b =
    text a </join/> doc </join/> text b

  fun isTupleInput xs ns =
      maybe false (fn v => Lst.all Psi.Inst.Term.eqData (Lst.zip (List.map v xs) ns)) var

  fun dot (a,p) =
    a </join/>
        (case p of
              Nil => empty
            | _ => text "." </join/>
                    nestIndent (line </join/> (print' p)))
  and printInArgs xs ns = 
      if isTupleInput xs ns
      then enclose "(" (commaSep (map n xs)) ")"
      else enclose "(\\" (commaSep (map n xs)) ")"
                   </join/> (commaSep (map t ns))
      
  and print' Nil = text "0"
    | print' (Tau p) =
        group $
            text "*tau*" </sp/> text "." </sp/> print' p
    | print' (Output (m, ns, p)) =
        group $
        text "'" </join/> t m </join/>
            (enclose "<" (commaSep (map t ns)) ">") </dot/> p
    | print' (BrOutput (m, ns, p)) =
        group $
        text "'" </join/> (t m) </join/> text "!" </join/> 
            (enclose "<" (commaSep (map t ns)) ">") </dot/> p
    | print' (Input (m, xvec, nn, p)) =
        group $ t m  </join/> printInArgs xvec nn </dot/> p
    | print' (BrInput (m, xvec, nn, p)) =
        group $ t m  </join/> text "?" </join/> printInArgs xvec nn </dot/> p
    | print' (Case cs) =
        let
          fun printCaseClause (cond,p) =
            c cond </sp/> text ":" </sp/> (print' p)
        in
        group $
            text "case" </join/>
                nestIndent
                    (line </join/>
                    (sep (text " " </join/>text "[]" </join/> line)
                         (map printCaseClause cs) ))
                </join/> line
        end
    | print' (proc as (Restriction _)) =
        let
          val (avec,p) = collapseNew proc
        in
          enclose "(new " (commaSep (map n avec)) ")"
            </join/>
                group (text "(" </join/> nestIndent
                                    (line </join/> print' p)
                                        </join/> line </join/>
                        text ")")
        end
    | print' (Parallel (p, q)) =
        group $ text "(" </join/> print' p </join/> text ")"
                </sp/> text "|" </join/>
                    (nestIndent $
                        line </join/>
                        text "(" </join/> print' q </join/> text ")")
    | print' (Replication p) =
        text "!(" </join/> print' p </join/> text ")"
    | print' (Assertion assr) =
        text "(|" </join/> a assr </join/> text "|)"
    | print' (Invocation (a, mvec)) =
        ppConstant a
            </join/> text "<" </join/> commaSep (map t mvec)
            </join/> text ">"

  fun ppAgent p = print' p

end
end;




functor PPClause(A : sig
  structure PP    : PRETTY_PRINTER
  structure Cl    : PSI_CLAUSE
  structure PPPsi : PSI_PRETTY_PRINTER
  sharing PP = PPPsi.PP
  sharing Cl.Psi = PPPsi.Psi
end):
sig
  structure PP    : PRETTY_PRINTER
  structure Cl    : PSI_CLAUSE
  structure PPPsi : PSI_PRETTY_PRINTER
  sharing PP = PPPsi.PP
  sharing Cl.Psi = PPPsi.Psi

  val ppClause        : Cl.clause -> PP.document
  val ppClauseFormals : Cl.clause -> PP.document
end =
struct
  open Missing
  open A open PP 
  structure PPA = PrettyPrinterAux(PP) open PPA

  (*
    A(x,y,..)
  *)
  fun ppClauseFormals (Cl.Clause (a,xvec,p)) =
    (PPPsi.ppConstant a) 
                </join/> text "("
                </join/> filledCommaSep (map PPPsi.n xvec)
                </join/> text ")"


  (*
    A(x,y,..) <= P
  *)
  fun ppClause (Cl.Clause (a,xvec,p)) =
        ppClauseFormals (Cl.Clause (a,xvec,p))
        </sp/> text "<="
            </join/> group (nest 2 (line </join/> PPPsi.ppAgent p))


end;

