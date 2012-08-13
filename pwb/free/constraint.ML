(* uses pwb/free/instance,
        pwb/simulator,
        pwb/bisim
 *)

structure FreeTermSymbTrCS'FinSort'ChEq : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = FreeTermPsiReq'FinSort'ChEq
  structure Constraint = FreeTermSymbPsi'FinSort'ChEq.Constraint
  fun solve _ = Err.undefined ()
end;


structure FreeTermSymbBisimCS'FinSort'ChEq : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = FreeTermPsi'FinSort'ChEq
  structure Constraint = SymBisimConstraint(Psi)
  fun solve _ = Err.undefined ()
end;


