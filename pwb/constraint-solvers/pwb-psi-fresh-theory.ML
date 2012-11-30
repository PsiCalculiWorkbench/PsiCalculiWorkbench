(* uses pwb/missing,
        pwb/data-structures,
        pwb/constraint-solvers/pwb-smt,
        pwb/psi
 *)

functor PwbSmtPsiFreshTheoryNF (P: PSI)  (* : PWB_SMT_THEORY_NO_FORGET *)  =
struct
  open Missing

  type freshness = P.Inst.name * P.psi 

  datatype literal = Fresh of freshness
                   | NotFresh of freshness

  fun neg (Fresh x) = NotFresh x
    | neg (NotFresh x) = Fresh x


  fun eqL' (a,p) (a',p') = a = a' andalso p </P.eqData/> p'

  fun eqL (Fresh x) (Fresh x') = x <//eqL'//> x'
    | eqL (NotFresh x) (NotFresh x') = x <//eqL'//> x'
    | eqL _ _ = false

  type model = freshness list * freshness list

  val empty = ([],[])

  fun extend (fl,nfl) (Fresh f) = (f::fl,nfl)
    | extend (fl,nfl) (NotFresh f) = (fl,f::nfl)

  fun isConsistent (fl,nfl) PwbSMTTypes.Fast = true
    | isConsistent (fl,nfl) PwbSMTTypes.Complete =
      null (map fst fl <//Lst.intersection//> map fst nfl)

  fun models (fl,nfl) l = false
end;


functor PwbSmtPsiFreshTheory (P: PSI) (* : PWB_SMT_THEORY *) =
struct
  structure TNF = PwbSmtPsiFreshTheoryNF(P)
  structure T = PwbSmtTheoryWithForget(TNF)
  open T
end;

