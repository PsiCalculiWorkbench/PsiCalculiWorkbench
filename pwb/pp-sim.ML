(* uses pwb/missing,
        pwb/pp,
        pwb/pp-psi,
        pwb/simulator
*)


functor PPStrongAction
    (A : 
    sig
      structure PP     : PRETTY_PRINTER
      structure Act    : PSI_STRONG_ACTION
      structure PPInst : PSI_PP_REQ
      sharing Act.Inst = PPInst.Inst
    end):
    sig
      structure PP     : PRETTY_PRINTER
      structure Act    : PSI_STRONG_ACTION
      structure PPInst : PSI_PP_REQ
      sharing Act.Inst = PPInst.Inst

      val ppAction : Act.action -> PP.document
    end =
struct

  open A open PP open Missing
  structure PPA = PrettyPrinterAux(PP)
  open PPA
  structure EPInst = EscapedPsiInstancePrettyPrinter(struct
    structure PP = PP
    structure PPInst = PPInst
  end)
  open EPInst

  fun ppAction alpha =
    case alpha of
         Act.Tau => text "tau"
       | Act.Output (y,avec,m) =>
           n y </join/>
                    (if not (null avec)
                        then
                                     text "(\\"
                            </join/> filledCommaSep (map n avec)
                            </join/> text ")"
                        else
                            text " ")
                  </join/> t m
       | Act.Input (z,x) =>
           n z </join/> text "(" </join/> n x </join/> text ")"
       | Act.BrOutput (y,avec,m) => text "!" </join/> (ppAction (Act.Output(y,avec,m)))
       | Act.BrInput  (z,x)      => text "?" </join/> (ppAction (Act.Input(z,x)))

end;
