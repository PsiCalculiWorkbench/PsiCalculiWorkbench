(* uses pwb/psi,
        pwb/simulator
 *)


signature PSI_LOGIC =
sig
  structure Psi: PSI
  structure Act: PSI_STRONG_ACTION
  sharing Psi.Inst = Act.Inst

  datatype formula
    = True
    | Not of formula
    | And of formula * formula
    | Cond of Psi.Inst.condition
    | AllNext of Act.action * formula
    | AllGlobally of formula
    | AllFuture of formula

  include NOMINAL
    where type atom = Psi.Inst.name
    where type data = formula
    sharing AtomSort = Psi.Inst.Sort
end;


functor PsiLogic(A: sig
    structure Psi: PSI
    structure Act: PSI_STRONG_ACTION
    sharing Psi.Inst = Act.Inst
end) : PSI_LOGIC  =
struct
  open A
  datatype formula
    = True
    | Not of formula
    | And of formula * formula
    | Cond of Psi.Inst.condition
    | AllNext of Act.action * formula
    | AllGlobally of formula
    | AllFuture of formula

  structure Nom = Nominal(
  struct
    type atom = Psi.Inst.name
    type data = formula

    structure AtomSort = Psi.Inst.Sort
    structure DataSort = struct
      datatype sort = FormulaSort fun eq _ = true end

    val atomSort = Psi.Inst.Term.atomSort
    fun dataSort _ = DataSort.FormulaSort

    fun swap pi (Not f) = Not (swap pi f)
      | swap pi (True) = True
      | swap pi (And (p,q)) = And (swap pi p, swap pi q)
      | swap pi (Cond phi) = Cond (Psi.Inst.Cond.swap pi phi)
      | swap pi (AllNext (act, p)) = AllNext (Act.swap pi act, swap pi p)
      | swap pi (AllGlobally p) = AllGlobally (swap pi p)
      | swap pi (AllFuture p) = AllFuture (swap pi p)

    val new = Psi.new
    val newBasedOn = Psi.newBasedOn

    fun support (Not p) = support p
      | support (True) = []
      | support (And (p,q)) = support p @ support q
      | support (Cond phi) = Psi.Inst.Cond.support phi
      | support (AllGlobally p) = support p
      | support (AllFuture p) = support p
      | support (AllNext (act, p)) =
      let
        val a = Act.support act
        val bn = Act.bn act
      in
        a @ (Lst.minus (support p) bn)
      end

    fun eq alphaEq (Not p, Not q) = eq alphaEq (p, q)
      | eq alphaEq (True, True) = true
      | eq alphaEq (And (p1,q1), And (p2,q2)) = eq alphaEq (p1,p2) andalso eq alphaEq (q1,q2)
      | eq alphaEq (Cond phi1, Cond phi2) = Psi.Inst.Cond.eqData (phi1,phi2)
      | eq alphaEq (AllGlobally p, AllGlobally q) = eq alphaEq (p,q)
      | eq alphaEq (AllFuture p, AllFuture q) = eq alphaEq (p,q)
      | eq alphaEq (AllNext _, AllNext _) = Err.error "unimplemented case in PsiLogic.eq alphaEq"
      | eq _ _ = false

  end)

  open Nom


end;


