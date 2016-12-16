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
  open Missing
  open A open PP 
  structure PPA = PrettyPrinterAux(PP)
  open PPA
  structure EPInst = EscapedPsiInstancePrettyPrinter(struct
    structure PP = PP
    structure PPInst = PPInst
  end)
  open EPInst

  fun ppRes avec = 
      if null avec
      then text " "
      else
          text "(new "
               </join/> filledCommaSep (map n avec)
               </join/> text ")"

  fun ppAction alpha =
    case alpha of
         Act.Tau => text "tau"
       | Act.Output (y,avec,ms) =>
           t y </join/> ppRes avec </join/> filledCommaSep (map t ms)
       | Act.Input (z,xs) =>
           t z </join/> text "(" </join/> filledCommaSep (map n xs) </join/> text ")"
       | Act.BrOutput (y,avec,ms) =>
           t y </join/> text "!" </join/> ppRes avec </join/> filledCommaSep (map t ms)
       | Act.BrInput (z,xs) =>
           t z </join/> text "?(" </join/> filledCommaSep (map n xs) </join/> text ")"

end;
