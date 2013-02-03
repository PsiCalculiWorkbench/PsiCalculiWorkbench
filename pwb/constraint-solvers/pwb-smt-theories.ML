(* uses pwb/missing,
        pwb/data-structures,
        pwb/constraint-solvers/pwb-smt
 *)


(*
 * A Pwb SMT theory without a background theory. This theory is used for
 * initialising Pwb SMT solver as a SAT solver where literals (propositions) are
 * integers.
 *)
structure PwbPropositionalTheory : PWB_SMT_THEORY =
struct
  type literal = int

  fun neg x = ~ x
  fun eqL x y = x = y

  type model = unit
  val empty = ()
  fun extend _ _ = ()
  fun forget _ _ = ()

  fun isConsistent _ _ = true
  fun explainIncons _ = []
  fun models _ _ = false
  fun explainTProp _ _ = []
end;

structure PwbSATSolver = PwbSMT(PwbPropositionalTheory);


(*
 * A theory of equalities between variables.
 *)
structure PwbEqTheory (* : PWB_SMT_THEORY *) =
struct
  type eql = string * string
  datatype literal = Eq of eql
                   | InEq of eql

  fun neg (Eq x) = InEq x
    | neg (InEq x) = Eq x

  fun eqL x y = x = y

    (* equivalence closure, inequalities *)
  type model = eql list * eql list

  val empty = ([],[])

  fun extend (eqls,ineqls) (Eq x) = (x::eqls,ineqls)
    | extend (eqls,ineqls) (InEq x) = (eqls,x::ineqls)

  fun forget (eqls,ineqls) lits =
  let
    val (eq,ineq) = List.partition (fn (Eq _) => true | _ => false) lits
    val eq = map (fn (Eq x) => x | _ => Err.undefined "PwbEqTheory.forget") eq
    val ineq = map (fn (InEq x) => x | _ => Err.undefined "PwbEqTheory.forget") ineq
  in
    (Lst.minus eqls eq, Lst.minus ineqls ineq)
  end

  fun eqClosure' ids =
  let
    (* a tuple membership testing in a list *)
    fun eqInClosure (a,b) ids =
      Lst.exists (fn id => id = (a,b)) ids

    (* symmetry *)
    val r = map (fn (a,b) => (b,a)) ids
    val r = List.filter (fn (a,b) =>
                           not (eqInClosure (a,b) ids)) r
    val r = ids @ r

    (* transitivity *)
    val t = map (fn (a,b) =>
                map (fn (_,c) => (a,c))
                    (List.filter (fn (b',c) => b = b') r)) r
    val t = List.concat t
    val t = List.filter
              (fn (a,b) => not (eqInClosure (a,b) r)) t
  in
    if null t
        then r
        else eqClosure' (r @ t)
  end

  fun isConsistent m PwbSMTTypes.Fast = true
    | isConsistent (eqls,ineqls) PwbSMTTypes.Complete =
    null (Lst.intersection (eqClosure' eqls) ineqls)

  fun explainIncons m = []

  fun models m l = false

  fun explainTProp m l = []

end;

structure PwbEqSMTSolver = PwbSMT(PwbEqTheory);

