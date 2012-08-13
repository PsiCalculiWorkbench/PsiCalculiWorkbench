signature NOM_TERM_ALGEBRA_UNIFICATION =
sig
  (* structure Sigma: NOM_SIGMA *)
  structure Term: NOM_TERM_ALGEBRA

  val unify: (Term.carrier * Term.carrier) list ->
    (string, (Term.carrier * Term.carrier) list) Either.either
end;


functor NomTermAlgebraUnifier(Term: NOM_TERM_ALGEBRA):
    NOM_TERM_ALGEBRA_UNIFICATION =
struct
  structure Term = Term
  open Missing
  open Term

  fun unify ((m,n)::eqs) =
    if isVar m andalso isVar n then LEFT $ "TODO"
    else LEFT $ "TODO"
    | unify _ = LEFT $ "TODO"

end;
