(* uses pwb/missing,
        pwb/data-structures
 *)


structure PwbSMTTypes =
struct
  datatype strength = Complete | Fast
end;


signature PWB_SMT_THEORY =
sig
  (* The type represents both positive and negative literals *)
  type literal

  (* Negation of a literal *)
  val neg : literal -> literal

  (* Are the literals equal? *)
  val eqL : literal -> literal -> bool


  type model

  val empty : model

  (* Extension of a model with a literal. *)
  val extend  : model -> literal -> model

  (* Remove the last n literal (used for backtracking). *)
  val forget : model -> literal list -> model

  (*
   * Check consistency at different levels of strength. The Fast strength level
   * is not required to do a complete consistency check. It is even allowed to
   * always return true, as long as the Complete strength level does the
   * complete consistency check.
   *)
  val isConsistent : model -> PwbSMTTypes.strength -> bool

  (* Is a literal entailed by the theory, i.e. M |= l *)
  val models : model -> literal -> bool
end;


signature PWB_SMT_THEORY_NO_FORGET =
sig
  type literal
  type model

  val neg : literal -> literal
  val eqL : literal -> literal -> bool
  val empty : model
  val extend  : model -> literal -> model
  val isConsistent : model -> PwbSMTTypes.strength -> bool
  val models : model -> literal -> bool
end;



(* XXX
  A possible extensions of the above is to implement conflict driven
   backjumping, and, or, lemma learning.

  (* Explain why a literal was propogated (entailed), i.e.,
   * find a list of literals in a model which entail (imply)
   * the literal in question. *)
  val explainTProp : model -> literal -> literal list
  val explainIncons: model -> literal list
*)



signature PWB_SMT =
sig
  structure Theory : PWB_SMT_THEORY

  (* This type represents Quantifier free FO Formula in
   * Conjunctive Normal Form (CNF).
   *
   * CNF is of the form
   * (l1 \/ ... \/ ln) /\ ... /\ (l'1 \/ .. \/ l'm)
   *
   * where li, l'j are literals (positive or negative atomic formulas).
   *
   * In SML,
   *
   * [[l1, ..., ln], ..., [l'1, ..., l'm]]
   *
   * an empty clause denotes false. An empty formula denotes true.
   *
   *)
  type cnf = Theory.literal list list

  (* the cnf value cannot be an empty list, and cannot contain empty clauses *)
  val sat : cnf -> (Theory.literal list * Theory.model) option
end;




functor PwbSMT (T: PWB_SMT_THEORY): PWB_SMT =
struct
  structure Theory = T
  open Missing
  open Theory


  type clause = literal list
  type cnf = clause list

  (* simplified clause, original clause *)
  type fcnf = (clause * clause) list

  fun cnfToFCnf cls = map (fn x => (x,x)) cls


  datatype simp_fcnf = FCl of (clause * clause) list
                     | FCnfFalse of clause

  (* assigned literal, is a decision literal, the orignating clause,
   * the simplified formula at the stage of literal assignment *)
  type assignment_member = literal * bool * clause * simp_fcnf
  (* Is kept in reverse or the last literal appears first in the list *)
  type assignment = assignment_member list


  fun cnfToSFCnf cnf = FCl (cnfToFCnf cnf)

  (* The state is either:
   *    propositional model, theory model, formula,
   * or failed *)
  datatype state = State of assignment * T.model * simp_fcnf
                 | FailState


  fun isTrue a l = a |> List.find (fn (l',_,_,_) => l' <//eqL//> l)
                     |> maybe false (const true)

  fun isFalse a l = a |> List.find (fn (l',_,_,_) => l' <//eqL//> neg l)
                      |> maybe false (const true)

  fun isUndefined a l = not (isTrue a l) andalso not (isFalse a l)


  datatype literal_state = LitTrue | LitFalse | LitUndefined

  fun literalState a l =
    if isTrue a l then LitTrue
    else if isFalse a l then LitFalse
    else LitUndefined


  (* Datatype for the use in the simplifyClause function *)
  datatype simp_clause = Lit of literal list (* empty list denotes false *)
                       | ClTrue

  fun prependLit l (Lit ls) = Lit (l::ls)
    | prependLit _ ClTrue = ClTrue

  fun simplifyClause m [] = Lit []
    | simplifyClause m (l::ls) =
    case literalState m l of
         LitTrue      => ClTrue
       | LitFalse     => simplifyClause m ls
       | LitUndefined => prependLit l $ simplifyClause m ls

  (* Datatype for the us in the simpCNF function *)
  datatype simp_cnf = Cl of clause list (* empty list denotes true *)
                    | CnfFalse

  fun prependClause c (Cl cs) = Cl (c::cs)
    | prependClause _ CnfFalse = CnfFalse

  fun simplifyCNF m [] = Cl []
    | simplifyCNF m (c::cs) =
    case simplifyClause m c of
         ClTrue => simplifyCNF m cs
       | Lit [] => CnfFalse
       | Lit c' => prependClause c' (simplifyCNF m cs)


  fun prependFClause c (FCl cs) = FCl (c::cs)
    | prependFClause _ (FCnfFalse c) = FCnfFalse c

  fun simplifyFCNF' a [] = FCl []
    | simplifyFCNF' a ((c,co)::cs) =
    case simplifyClause a c of
         ClTrue => simplifyFCNF' a cs
       | Lit [] => FCnfFalse co
       | Lit c' => prependFClause (c',co) (simplifyFCNF' a cs)

  fun simplifyFCNF a (FCnfFalse c) = FCnfFalse c
    | simplifyFCNF a (FCl cs) = simplifyFCNF' a cs


  fun extendState (State (a,m,f)) d l cl =
  let
    val a' = (l,d,cl,f)::a
    val m' = T.extend m l
    val f' = simplifyFCNF a' f
  in
    State (a', m', f')
  end
    | extendState x _ _ _ = x

  fun setState a m fcnf =
    State (a,m,simplifyFCNF a fcnf)


  type adpll_rule = state -> state option


  fun findUnit (FCnfFalse _) = NONE
    | findUnit (FCl []) = NONE
    | findUnit (FCl (([l],c')::cs)) = SOME (l, c')
    | findUnit (FCl (c::cs)) = findUnit (FCl cs)

  fun unitPropogate FailState = NONE
    | unitPropogate (st as (State (a,m,fcnf))) =
    findUnit fcnf |>
    maybe NONE
        (* the literal l is not defined in a,
         * as otherwise it would have been simplified *)
        (fn (l, c') => SOME $ extendState st false l c')


  fun findDecision (FCnfFalse _) = NONE
    | findDecision (FCl []) = NONE
    | findDecision (FCl (((l::c),c')::cs)) = SOME (l,c')
    | findDecision _ = Err.undefined "PwbSMT.findDecision"

  fun decide FailState = NONE
    | decide (st as (State (a,m,fcnf))) =
    findDecision fcnf |>
    maybe NONE
        (fn (l,c') => SOME $ extendState st true l c')


  fun fail (State (a,m,FCnfFalse _)) =
    if exists (fn (l,d,c,cnf) => d) a
        then NONE
        else SOME (FailState)
    | fail _ = NONE



  fun findT' _ f [] = NONE
    | findT' p f (x::xs) = if p x then SOME (f, x, xs) else findT' p (x::f) xs
  fun findT p ls = findT' p [] ls

  fun lits a = map (fn (l,_,_,_) => l) a

  fun backtrack (State (a,m,FCnfFalse _)) =
    findT (fn (_,d,_,_) => d) a |>
    maybe NONE
       (fn (ls, (l,_,c,fcnf), a') =>
           SOME $ setState ((neg l, false, c, fcnf)::a')
                            (T.forget m (l::(lits ls))) fcnf)
    | backtrack _ = NONE


  fun theoryFalse strength FailState = NONE
    | theoryFalse strength (State (a,m,FCnfFalse _)) = NONE
    | theoryFalse strength (State (a,m,f)) =
    if T.isConsistent m strength
        then NONE
        else SOME $ State (a, m, FCnfFalse []) (* TODO explainIncons *)


  fun findL (FCnfFalse _) = NONE
    | findL (FCl []) = NONE
    | findL (FCl (([],_)::cs)) = findL (FCl cs)
    | findL (FCl ((l::ls, cl)::cs)) = SOME (l,cl)


  fun theoryPropagate FailState = NONE
    | theoryPropagate (st as (State (a,m,f))) =
    findL f |> maybe NONE (fn (l,cl) =>
            if m <//T.models//> l
                then SOME $ extendState st false l cl
                else if m <//T.models//> T.neg l
                    then SOME $ extendState st false (T.neg l) cl
                    else NONE)


  fun star r s =
    r s |> maybe (SOME s) (star r)

  fun plus r s =
    r s |> maybe NONE (star r)

  fun might r s =
    r s |> maybe (SOME s) SOME

  fun choice r r' s =
    r s |> maybeL (fn () => r' s) SOME

  fun seq r r' s = r s <//bindO//> r'

  fun app n r s = (r s)

  val up = app "unit-propagate" unitPropogate
  val de = app "decide" decide
  val bt = app "backtrack" backtrack
  val fa = app "fail" fail


  val thfC = app "theory consistency complete" (theoryFalse PwbSMTTypes.Complete)
  val thfF = app "theory consistency fast" (theoryFalse PwbSMTTypes.Fast)

  val tp = app "theory-propagate" theoryPropagate
  val upe = up <//seq//> might thfF
  val tpe = tp <//seq//> might thfF

  val exp = star (plus upe <//choice//> plus tpe)


  fun semiIncrementalOnlineExhaustive s =
    s |> exp <//seq//>
      star (
        (plus ((de <//choice//> bt) <//seq//> exp))
        <//choice//>
        thfC) <//seq//>
      might fa |>
    always id


  fun satP p cnf =
    State ([], T.empty, cnfToSFCnf cnf) |>
    p |>
    (fn (State (a,m,sfcnf)) => SOME (map (fn (l,_,_,_) => l) a, m)
      | (FailState) => NONE)

  fun sat cnf = satP semiIncrementalOnlineExhaustive cnf

end;


functor PwbSmtTheoryWithForget(T: PWB_SMT_THEORY_NO_FORGET): PWB_SMT_THEORY =
struct
  type literal = T.literal
  val neg = T.neg
  val eqL = T.eqL

  type model = T.model list
  val empty = []

  fun extend [] l = [T.extend T.empty l]
    | extend (m' as (m::ms)) l = (T.extend m l)::m'

  fun isConsistent [] _ = true
    | isConsistent (m::ms) strength = T.isConsistent m strength

  fun models [] l = T.models T.empty l
    | models (m::ms) l = T.models m l

  fun forget [] (l::_) = Err.error "There were more literals than models in PwbSmtTheoryWithForget.forget"
    | forget m [] = m
    | forget (m::ms) (l::ls) = forget ms ls
end;



functor PwbSMTNoForget(T: PWB_SMT_THEORY_NO_FORGET) : 
sig
  include PWB_SMT
  val getModel : Theory.model -> T.model
end =
struct
  structure TWF = PwbSmtTheoryWithForget(T)
  structure SMT = PwbSMT(TWF)
  open SMT

  fun getModel [] = T.empty
    | getModel (m::ms) = m
end;

