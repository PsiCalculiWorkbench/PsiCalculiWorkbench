(* uses pwb/missing,
        pwb/nominal,
        pwb/pp
*)

functor PPNominal(A : sig
                        structure PP: PRETTY_PRINTER
                        structure Nom: NOMINAL
                        val ppAtom : Nom.atom -> PP.document
                        (* val ppData    : Nom.data -> PP.document *)
                      end):
                     sig
                       structure PP  : PRETTY_PRINTER
                       structure Nom : NOMINAL
                       val ppAtom    : Nom.atom -> PP.document
                       (* val ppData    : Nom.data -> PP.document *)
                       val ppSupp    : Nom.data -> PP.document
                       val ppFresh   : Nom.data -> PP.document
                     end =
struct
  open Missing
  open A open PP 
  structure PPA = PrettyPrinterAux(PP)
  open PPA

  val ppAtom = ppAtom
  (* val ppData = ppData *)

  fun ppSupp d =
    text "{" </join/> nest 1 (filledCommaSep (map ppAtom (Nom.support d))) 
             </join/> text "}"

  fun ppFresh _ = PP.empty

end;

