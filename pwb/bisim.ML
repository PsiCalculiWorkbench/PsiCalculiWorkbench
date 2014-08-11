(* uses pwb/missing,
        pwb/psi,
        pwb/simulator,
        pwb/weak-simulator,
        pwb/pwb-logger
*)

signature SYMBOLIC_BISIM_CONSTRAINT =
sig
  structure Psi : PSI
  structure Frame : FRAME
  sharing Psi = Frame.Psi

  datatype constraint
    (* transition constraints *)
    = True
    | False
    | Atomic of Psi.Inst.name list * Psi.Inst.assertion * Psi.Inst.condition
    (* constraints *)
    | TermEq of Psi.Inst.term  * Psi.Inst.term
    | FreshP of Psi.Inst.name  * Psi.psi
    | StImp  of Frame.frame * Frame.frame

    | Conj   of constraint * constraint
    | Disj   of constraint * constraint
    | Imp    of constraint * constraint
    | Forall of Psi.Inst.name * constraint

    | Var    of Psi.Inst.name

  include NOMINAL
    where type atom = Psi.Inst.name
    where type data = constraint
    sharing AtomSort = Psi.Inst.Sort


  val conj   : constraint * constraint -> constraint
  val disj   : constraint * constraint -> constraint
  val imp    : constraint * constraint -> constraint
  val termEq : Psi.Inst.term  * Psi.Inst.term -> constraint
  val stImp  : Frame.frame * Frame.frame -> constraint

  val subst : constraint -> (Psi.Inst.name * Psi.Inst.term) list -> constraint

  val substConst : constraint -> (Psi.Inst.name * constraint) -> constraint

  val simplify : constraint -> constraint
  val cnf      : constraint -> constraint
  val cnfList  : constraint -> constraint list list
  val dnf      : constraint -> constraint
  val rewrite  : (constraint -> constraint option) list
               -> constraint -> constraint


  val simplificationRules : (constraint -> constraint option) list
  val deMorganAndNegRules : (constraint -> constraint option) list
  val elimImpRules        : (constraint -> constraint option) list
  val disjRules           : (constraint -> constraint option) list

  val disjunct : constraint list -> constraint
  val conjunct : constraint list -> constraint
end;



signature SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
sig
  structure Psi        : PSI
  structure Constraint : SYMBOLIC_BISIM_CONSTRAINT

  val solve :
    Constraint.constraint ->
    (string, (Psi.Inst.name * Psi.Inst.term) list * Psi.Inst.assertion) Either.either


  sharing Constraint.Psi = Psi
end;


functor SymBisimConstraint(Psi: PSI) : SYMBOLIC_BISIM_CONSTRAINT =
struct
  structure Psi = Psi
  structure Frame = Frame(Psi)

  datatype constraint
    (* transition constraints *)
    = True
    | False
    | Atomic of Psi.Inst.name list * Psi.Inst.assertion * Psi.Inst.condition
    | Conj   of constraint * constraint
    | TermEq of Psi.Inst.term * Psi.Inst.term
    | FreshP of Psi.Inst.name * Psi.psi
    | Disj   of constraint    * constraint
    | Imp    of constraint    * constraint
    | StImp  of Frame.frame * Frame.frame
    | Forall of Psi.Inst.name * constraint
    | Var    of Psi.Inst.name


  open Psi
  open Inst

  structure Nom = Nominal(
  struct
    type atom = name
    type data = constraint
    structure L = NominalNameList(Term)

    structure AtomSort = Term.AtomSort
    structure DataSort = struct datatype sort = SBConstraint fun eq _ = true end
    val atomSort = Term.atomSort
    fun dataSort _ = DataSort.SBConstraint

    fun swap (a,b) True = True
      | swap (a,b) False = False
      | swap (a,b) (Atomic (avec, psi, phi)) =
        Atomic (L.swap (a,b) avec, Assr.swap (a,b) psi, Cond.swap (a,b) phi)
      | swap (a,b) (Conj (c,c'))    = Conj (swap (a,b) c, swap (a,b) c')
      | swap (a,b) (TermEq (n,m))   = TermEq (Term.swap (a,b) n, Term.swap (a,b) m)
      | swap (a,b) (FreshP (x,p))   = FreshP (Term.swapAtom (a,b) x, Psi.swap (a,b) p)
      | swap (a,b) (Disj (c,c'))    = Disj (swap (a,b) c, swap (a,b) c')
      | swap (a,b) (Imp (c,c'))     = Imp (swap (a,b) c, swap (a,b) c')
      | swap (a,b) (StImp (f,g))    = StImp (Frame.swap (a,b) f, Frame.swap (a,b) g)
      | swap (a,b) (Forall (x,c))   = Forall (Term.swapAtom (a,b) x, swap (a,b) c)
      | swap (a,b) (Var x)          = Var (Term.swapAtom (a,b) x)

    fun support True = []
      | support False = []
      | support (Atomic (avec, psi, phi)) =
        Lst.minus ((Assr.support psi) @ (Cond.support phi)) avec
      | support (Conj (c,c'))    = support c @ support c'
      | support (TermEq (n,m))   = Term.support n @ Term.support m
      | support (FreshP (a,p))   = a :: (Psi.support p)
      | support (Disj (c,c'))    = support c @ support c'
      | support (Imp (c,c'))     = support c @ support c'
      | support (StImp (f,g))    = Frame.support f @ Frame.support g
      | support (Forall (x,c))   = Lst.minus (support c) [x]
      | support (Var x)          = [x]

    val new = Term.new
    val newBasedOn = Term.newBasedOn

    fun eq aEq (True,True) = true
      | eq aEq (False,False) = true
      | eq aEq (Atomic ([],psi,phi), Atomic ([],psi',phi')) =
            Assr.eqData (psi, psi') andalso Cond.eqData(phi,phi')
      | eq aEq (Atomic (a::avec,psi,phi), Atomic (a'::avec',psi',phi')) =
            aEq ((a, Atomic (avec,psi,phi)), (a', Atomic (avec', psi', phi')))
      | eq aEq (Atomic _, Atomic _) = false
      | eq aEq (Conj (c1,c1'), Conj (c2,c2')) = eq aEq (c1, c2) andalso eq aEq (c1',c2')
      | eq aEq (Disj (c1,c1'), Disj (c2,c2')) = eq aEq (c1, c2) andalso eq aEq (c1',c2')
      | eq aEq (Imp  (c1,c1'), Imp  (c2,c2')) = eq aEq (c1, c2) andalso eq aEq (c1',c2')
      | eq aEq (TermEq (n,m), TermEq(n',m')) = Term.eqData (n,n') andalso Term.eqData (m,m')
      | eq aEq (FreshP (a,p), FreshP (a',p')) = a = a' andalso Psi.eqData (p,p')
      | eq aEq (StImp (f,g), StImp (f',g')) = Frame.eqData (f,f') andalso Frame.eqData (g,g')
      | eq _ _ = false
  end)
  open Nom

  structure NA = NominalAlpha(Nom)
  local open Missing in

  fun substSupp sigma =
    (map fst sigma) @ (List.concat $ map (Term.support o snd) sigma)


  fun substConst True sigma          = True
    | substConst False sigma         = False
    | substConst (Conj (c,c')) sigma = Conj (substConst c sigma, substConst c' sigma)
    | substConst (Disj (c,c')) sigma = Disj (substConst c sigma, substConst c' sigma)
    | substConst (Imp  (c,c')) sigma = Imp  (substConst c sigma, substConst c' sigma)
    | substConst (TermEq teq) sigma  = TermEq teq
    | substConst (FreshP fp) sigma   = FreshP fp
    | substConst (StImp st) sigma    = StImp st
    | substConst (Atomic at) sigma   = Atomic at
    | substConst (Forall (x,c)) (var,cstr) =
        (let
          val x' = Term.newBasedOn x (var :: support cstr)
        in
          Forall (x', substConst (Nom.swap (x,x') c) (var,cstr))
        end)
    | substConst (Var x) (x',c) = if x = x' then c else Var x


  fun subst True sigma             = True
    | subst False sigma            = False
    | subst (Conj (c,c')) sigma    = Conj (subst c sigma, subst c' sigma)
    | subst (Disj (c,c')) sigma    = Disj (subst c sigma, subst c' sigma)
    | subst (Imp  (c,c')) sigma    = Imp  (subst c sigma, subst c' sigma)
    | subst (TermEq (n,m)) sigma   = TermEq (substT sigma n, substT sigma m)
    | subst (FreshP (a,p)) sigma   = FreshP (a, Psi.subst p sigma)
    | subst (StImp (f,g)) sigma    = StImp (Frame.subst sigma f, Frame.subst sigma g)
    | subst (Atomic (avec, psi, phi)) sigma =
        (* avec # sigma *)
        let
          val sigmaNames = substSupp sigma
        in
          (NA.makeFresh avec (Atomic (avec, psi, phi)) sigmaNames) |>
          (fn (Atomic (avec, psi, phi)) =>
            Atomic (avec, substA sigma psi, substC sigma phi)
            | _ => Err.undefined "SymBisimConstraint.Nom.subst Atomic")
        end
    | subst (Forall (x,c)) sigma =
        (let
          val x' = Term.newBasedOn x (substSupp sigma)
        in
          Forall (x', subst (Nom.swap (x,x') c) sigma)
        end)
    | subst (Var x) sigma =
        List.find (fn (x',_) => x = x') sigma |>
        maybeL (fn () => Err.error
            "Attempted to substitute constraint variable for term")
                (fn _ => (Var x))
  end

  local open Missing in

  fun applyRule [] t = NONE
    | applyRule (r::rs) t =
    case r t of
         NONE => applyRule rs t
       | t' => t'

  fun rbin rules rw'' constr (c,c') =
  let
    val (c,rw)   = rewrite' rules c
    val (c',rw') = rewrite' rules c'
  in
    (constr (c,c'), rw orelse rw' orelse rw'')
  end

  and rewrite' rules c =
  let
    val (c,rw) = case applyRule rules c of
                       NONE    => (c , false)
                     | SOME c' => (c', true )
  in
    case c of
         Imp c  => rbin rules rw Imp  c
       | Conj c => rbin rules rw Conj c
       | Disj c => rbin rules rw Disj c
       | Forall (x,c) => rewrite' rules c |> (fn (c',rw) => (Forall (x, c'), rw))
       | c      => (c,rw)
  end

  fun rewrite rules c =
  let
    val (c, rw) = rewrite' rules c
  in
    if rw then rewrite rules c else c
  end


  end (* local open Missing *)


  fun listOfDisjuncts (Disj (c,c')) = listOfDisjuncts c @ listOfDisjuncts c'
    | listOfDisjuncts c = [c]

  fun listOfConjuncts (Conj (c,c')) = listOfConjuncts c @ listOfConjuncts c'
    | listOfConjuncts c = [c]

  val maybe = Missing.maybe
  val const = Missing.const


  fun findNeg (Imp (c, False)) cs =
    maybe false (const true) (List.find (fn c' => eqData(c, c')) cs)
    | findNeg c cs =
    maybe false (const true)
    (List.find (fn c' => eqData(Imp(c,False), c')) cs)

  fun hasCandNC []      = false
    | hasCandNC [c]     = false
    | hasCandNC (c::cs) = findNeg c cs orelse hasCandNC cs

  val simplificationRules =
    (fn (Conj (False,_)) => SOME False      | _ => NONE) ::
    (fn (Conj (_,False)) => SOME False      | _ => NONE) ::
    (fn (Conj (True,c))  => SOME c          | _ => NONE) ::
    (fn (Conj (c,True))  => SOME c          | _ => NONE) ::
    (fn (Conj (c,c')) =>
        if eqData (c,c') then SOME c else NONE | _ => NONE) ::

    (* c /\ (c' \/ c'') = c *)
    (fn (Conj (c, Disj (c',c''))) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::
    (fn (Conj (Disj (c',c''), c)) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::

    (fn (Disj (True,_))  => SOME True       | _ => NONE) ::
    (fn (Disj (_,True))  => SOME True       | _ => NONE) ::
    (fn (Disj (False,c)) => SOME c          | _ => NONE) ::
    (fn (Disj (c,False)) => SOME c          | _ => NONE) ::
    (fn (Disj (c,c')) =>
        if eqData (c,c') then SOME c else NONE | _ => NONE) ::

    (* c \/ (c' /\ c'') = c *)
    (fn (Disj (c, Conj (c',c''))) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::
    (fn (Disj (Conj (c',c''), c)) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::

    (fn (Imp (False, _)) => SOME True       | _ => NONE) ::
    (fn (Imp (c, True))  => SOME True       | _ => NONE) ::
    (fn (Imp (True, c))  => SOME c          | _ => NONE) ::

    (*
    (fn (Disj (c, c')) =>
        if eqData (c,c') then SOME c else NONE
                                            | _ => NONE) ::
    (fn (Conj (c, c')) =>
        if eqData (c,c') then SOME c else NONE
                                            | _ => NONE) ::
                                            *)

    (* LEM *)
    (fn (c as (Disj (c',c''))) =>
      if hasCandNC (listOfDisjuncts c)  then SOME True else NONE
                                            | _ => NONE) ::

    (* Contradiction *)
    (fn (c as (Conj (c', c''))) =>
        if hasCandNC (listOfConjuncts c) then SOME False else NONE
                                            | _ => NONE) ::

    (* neg neg C = C *)
    (fn (Imp (Imp (c, False), False)) => SOME c
                                            | _ => NONE) ::

    []

  fun simplify c = rewrite simplificationRules c

  fun neg c = Imp (c, False)

  val elimImpRules =
                                            (*
    (fn (Imp (c,False)) => NONE
      | (Imp (c,c'))    => SOME (Disj (c', Imp (c,False)))
                                            | _ => NONE) ::
                                            *)
    (fn (Imp (c,False)) => NONE (* Skip the negation *)
      | (Imp (c,c'))    => SOME (Disj (Imp (c,False), c'))
                                            | _ => NONE) ::
    []


  val deMorganAndNegRules =
    (fn (Imp (Conj (c,c'), False)) =>
        SOME (Disj (neg c, neg c'))
                                            | _ => NONE) ::
    (fn (Imp (Disj (c,c'), False)) =>
        SOME (Conj (neg c, neg c'))
                                            | _ => NONE) ::

    (fn (Imp (Imp (c, False), False)) => SOME c
                                            | _ => NONE) ::

    []

  val disjRules =
    (fn (Disj (c, Conj (c', c''))) =>
        SOME (Conj (Disj (c, c'), Disj (c,c'')))
                                            | _ => NONE) ::
    (fn (Disj (Conj (c,c'), c'')) =>
        SOME (Conj (Disj (c, c''), Disj (c',c'')))
                                            | _ => NONE) ::
    []

  val conjRules =
    (fn (Conj (c, Disj (c', c''))) =>
        SOME (Disj (Conj (c, c'), Conj (c,c'')))
                                            | _ => NONE) ::
    (fn (Conj (Disj (c,c'), c'')) =>
        SOME (Disj (Conj (c, c''), Conj (c',c'')))
                                            | _ => NONE) ::
    []


  local open Missing in

  (* 'c' must be free from 'forall' *)
  fun cnf c = c
    |> simplify
    |> rewrite elimImpRules
    |> rewrite deMorganAndNegRules
    |> rewrite disjRules
    |> simplify


  fun disjToList (Disj (c,c')) = disjToList c @ disjToList c'
    | disjToList c = [c]

  fun cnfToList (Conj (c,c')) = cnfToList c @ cnfToList c'
    | cnfToList c = [disjToList c]

  fun cnfList c = c |> cnf |> cnfToList

  fun dnf c = c
    |> simplify
    |> rewrite elimImpRules
    |> rewrite deMorganAndNegRules
    |> rewrite conjRules
    |> simplify


  end

  open Fun

  fun reduce f base []      = base
    | reduce f base [x]     = x
    | reduce f base (x::xs) = f (x, reduce f base xs)

  fun conj (True,True) = True
    | conj (False,_) = False
    | conj (_,False) = False
    | conj (True,c) = c
    | conj (c,True) = c
    | conj (a,b) = Conj (a,b)

  fun termEq (m, n) =
    if m </Psi.Inst.Term.eqData/> n
        then True
        else TermEq (m,n)

  fun disj (True,_) = True
    | disj (_,True) = True
    | disj (False,False) = False
    | disj (False,c) = c
    | disj (c,False) = c
    | disj (a,b) = Disj (a,b)

  fun imp (False, _) = True
    | imp (True,c) = c
    | imp (a,b) = Imp (a,b)

  fun stImp (st as (Frame.Frame (avec, psi), Frame.Frame (bvec, psi'))) =
    if Psi.Inst.Assr.eqData (psi, psi')
        then True
        else StImp st


  fun disjunct cs = reduce disj False cs
  fun conjunct cs = reduce conj True cs

end;

signature SYMBOLIC_BISIM =
sig
  structure Psi   : PSI
  structure C     : SYMBOLIC_BISIM_CONSTRAINT
  structure ClEnv : PSI_CLAUSE_ENVIRONMENT

  val bisim :
    ClEnv.env -> Psi.psi -> Psi.psi ->
        C.constraint * ((Psi.psi * Psi.psi * C.constraint) list)

  val sim :
    ClEnv.env -> Psi.psi -> Psi.psi ->
        C.constraint * ((Psi.psi * Psi.psi * C.constraint) list)

  sharing Psi = C.Psi = ClEnv.Cl.Psi
end;


signature SYMBOLIC_PSI_REDUCER_BISIM =
sig
  structure Psi : PSI
  structure Env : PSI_CLAUSE_ENVIRONMENT
  structure C   : SYMBOLIC_BISIM_CONSTRAINT
  sharing Psi = Env.Cl.Psi = C.Psi

  datatype action_type
    = ActAny | ActVis | ActIn | ActOut | ActBrOut | ActBrIn | ActTau

  datatype action
    = Silent
    | Tau
    | Output   of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | Input    of Psi.Inst.term * Psi.Inst.name list
    | BrOutput of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | BrInput  of Psi.Inst.term * Psi.Inst.name list


  val silent : Env.env -> Psi.psi ->
        (Psi.psi * action * C.constraint * Psi.psi) list

  val reduce : Env.env -> Psi.psi ->
        (Psi.psi * action * C.constraint * Psi.psi) list

  val reduceA : Env.env -> Psi.psi -> action_type ->
        (Psi.psi * action * C.constraint * Psi.psi) list
end;



functor SymbolicStrongPsiReducerBisim (X: sig
  structure R : SYMBOLIC_PSI_REDUCER
  structure C : SYMBOLIC_BISIM_CONSTRAINT
  sharing R.Sim.Psi = C.Psi
end) : SYMBOLIC_PSI_REDUCER_BISIM =
struct
  open Missing
  open X
  structure Sim = R.Sim
  structure Psi = Sim.Psi
  structure Env = Sim.ClEnv
  structure SC  = Sim.Constraint

  datatype action_type
    = ActAny | ActVis | ActIn | ActOut | ActBrOut | ActBrIn | ActTau

  datatype action
    = Silent
    | Tau
    | Output   of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | Input    of Psi.Inst.term * Psi.Inst.name list
    | BrOutput of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | BrInput  of Psi.Inst.term * Psi.Inst.name list

  fun trAT ActAny   = Sim.ANYa
    | trAT ActVis   = Sim.VISa
    | trAT ActIn    = Sim.INa
    | trAT ActOut   = Sim.OUTa
    | trAT ActBrOut = Sim.BROUTa
    | trAT ActBrIn  = Sim.BRINa
    | trAT ActTau   = Sim.TAUa

  structure Act = Sim.Tr.Act
  fun trA Act.Tau          = Tau
    | trA (Act.Output x)   = Output x
    | trA (Act.Input x)    = Input x
    | trA (Act.BrOutput x) = BrOutput x
    | trA (Act.BrInput x)  = BrInput x

  fun translateOne (bv,psi,[]) = []
    | translateOne (bv,psi,phi::phis) =
      C.Atomic (bv,psi,phi) :: translateOne (bv,psi,phis)

  fun trC []    = C.True
    | trC cstrs = Lst.reduce C.conj $ Lst.flatmapmix translateOne cstrs

  val unitC = SC.unit

  fun silent env p = [(p, Silent, C.True, p)]

  fun reduce env p = 
    R.reduce env p unitC |>
    map (fn (q, act, cstr, sol, q') => (q, trA act, trC cstr, q'))

  fun reduceA env p actT =
    R.reduceA env p (trAT actT) unitC |>
    map (fn (q, act, cstr, sol, q') => (q, trA act, trC cstr, q'))

end;


functor SymbolicWeakPsiReducerBisim (X: sig
  structure R : WEAK_SYMBOLIC_PSI_REDUCER
  structure C : SYMBOLIC_BISIM_CONSTRAINT
  sharing R.Red.Sim.Psi = C.Psi
end) : SYMBOLIC_PSI_REDUCER_BISIM =
struct
  open Missing
  open X
  structure Sim = R.Red.Sim
  structure Psi = Sim.Psi
  structure Env = Sim.ClEnv
  structure SC  = Sim.Constraint

  datatype action_type
    = ActAny | ActVis | ActIn | ActOut | ActBrOut | ActBrIn | ActTau

  datatype action
    = Silent
    | Tau
    | Output   of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | Input    of Psi.Inst.term * Psi.Inst.name list
    | BrOutput of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | BrInput  of Psi.Inst.term * Psi.Inst.name list

  fun trAT ActAny   = Sim.ANYa
    | trAT ActVis   = Sim.VISa
    | trAT ActIn    = Sim.INa
    | trAT ActOut   = Sim.OUTa
    | trAT ActBrOut = Sim.BROUTa
    | trAT ActBrIn  = Sim.BRINa
    | trAT ActTau   = Sim.TAUa

  structure Act = R.Tr
  fun trA Act.Silent       = Silent
    | trA Act.Tau          = Tau
    | trA (Act.Output x)   = Output x
    | trA (Act.Input x)    = Input x
    | trA (Act.BrOutput x) = BrOutput x
    | trA (Act.BrInput x)  = BrInput x

  fun translateOne (bv,psi,[]) = []
    | translateOne (bv,psi,phi::phis) =
      C.Atomic (bv,psi,phi) :: translateOne (bv,psi,phis)

  fun trC []    = C.True
    | trC cstrs = Lst.reduce C.conj $ Lst.flatmapmix translateOne cstrs

  val unitC = SC.unit

  fun silent env p = 
    R.silent env p unitC |>
    map (fn (q, act, c, sol, q') => (q, trA act, trC c, q'))

  fun reduce env p = 
    R.reduce env p unitC |>
    map (fn (q, act, cstr, sol, q') => (q, trA act, trC cstr, q'))

  fun reduceA env p actT =
    R.reduceA env p (trAT actT) unitC |>
    map (fn (q, act, cstr, sol, q') => (q, trA act, trC cstr, q'))

end;




functor Bisim(A: sig
  structure PRed   : SYMBOLIC_PSI_REDUCER_BISIM
  structure QRed   : SYMBOLIC_PSI_REDUCER_BISIM
  structure C      : SYMBOLIC_BISIM_CONSTRAINT

  sharing C.Psi = PRed.Psi = QRed.Psi
  sharing C = PRed.C = QRed.C
  sharing PRed.C = QRed.C = C
  sharing QRed.Env = PRed.Env
end) : SYMBOLIC_BISIM =
struct
  open Missing
  open A

  structure Psi   = PRed.Psi
  structure ClEnv = PRed.Env
  structure F     = C.Frame

  open C

  val log = PwbLog.write "Bisim"

  fun unvar x = hd $ Psi.Inst.Term.support x

  fun permute swap pi t =
    List.foldr (fn ((a,b), t) => swap (a,b) t) t pi

  fun collectCstrDeriv trs = map (fn (p,alpha,c,p') => (c, p')) trs

  fun freshness avec p =
    List.foldr (fn (a,c) => FreshP (a,p) </conj/> c) True avec


  structure NameGen : sig
    val newName : unit -> Psi.Inst.name
    val newNameVec : int -> Psi.Inst.name list
    val reset : unit -> unit
    val init : Psi.Inst.name list -> unit
  end =
  struct
    val names = ref []
    fun reset () = names := []
    fun init nms = names := nms
    fun newName () =
    let
      val y = Psi.Inst.Term.new (!names)
      val () = names := y::(!names)
    in
      y
    end
    fun newNameVec n =
      enum 1 n |> map (fn _ => newName ())
  end;


  structure Table :
  sig
    val reset  : unit -> unit
    val add    : Psi.psi -> Psi.psi -> C.constraint -> unit
    val find   : Psi.psi -> Psi.psi -> C.constraint option
    val toList : unit -> (Psi.psi * Psi.psi * C.constraint) list
    val substConstr : Psi.Inst.name * C.constraint -> unit
  end =
  struct
    val table = ref []
    fun add p q c = table := (p,q,c)::(!table)
    fun reset () = table := []

    fun find p q =
      (!table) |>
      List.find (fn (p',q',c) =>
        p </Psi.eqData/> p' andalso q </Psi.eqData/> q') |>
      some (fn (_,_,c) => c)

    fun toList () = (!table)

    fun substConstr sigma =
      table := (map (fn (p,q,c) => (p,q,substConst c sigma)) (!table))
  end;


  fun foreach f (x::xs) = (f x)::foreach f xs
    | foreach f [] = []


  fun forallC vars c = List.foldr Forall c vars


  structure Imp =
  struct

    (* Flag: if true then check bisimulation, otherwise check simulation *)
    val checkBisim = ref true

    fun bisim env p q =
      (Table.reset ();
      NameGen.reset ();
      close env p q;
      (always id (Table.find p q), Table.toList ()))

    and close env p q =
      case Table.find p q of
           SOME c => (c)
         | NONE =>
             let
               val x = NameGen.newName ()
               val () = Table.add p q (Var x)
               val () = Table.add q p (Var x)
               val c = if !checkBisim
                            then conj (matchAll env p q, matchAll env q p)
                            else matchAll env p q
               val c' = substConst c (x, True)
               val () = Table.substConstr (x, c')
             in
               c'
             end

    and matchAll env p q =
      [matchStImp
      ,matchTau
      ,matchOut
      ,matchIn
      ,matchBrOut
      ,matchBrIn
      ] |> map (fn f => f env p q) |> conjunct

    and matchStImp env p q =
      disjunct (
      QRed.silent env q |>
      foreach (fn (_, _, cqj, qj) =>
          conjunct [cqj, stImp (F.frameOf p, F.frameOf qj),
                    close env p qj]) )

    and matchTau env p q =
      conjunct (
          PRed.reduceA env p PRed.ActTau |>
          foreach (fn (_, _, cpi, pi) =>
              cpi </imp/> disjunct (
                  QRed.silent env q |>
                  foreach (fn (_,_,cqj, qj) =>
                      cqj </conj/> close env pi qj
                  )
              )
          )
      )

    and matchIn env p q =
      conjunct (
          PRed.reduceA env p PRed.ActIn |>
          foreach (fn (_,PRed.Input (y,xs),cpi,pi) =>
          let
            val y' = NameGen.newName ()
            val xs' = NameGen.newNameVec (List.length xs)
            val cpi' = C.swap (unvar y, y') cpi
            val pi' = Lst.foldr Psi.swap pi (zip xs xs')
          in
            forallC (y'::xs') (
              cpi' </imp/> disjunct (
                  QRed.reduceA env q QRed.ActIn |>
                  foreach (fn (_,QRed.Input (y'',xs''),cqj,qj) =>
                      let
                        val cqj' = C.swap (y',unvar y'') cqj
                        val qj' = Lst.foldr Psi.swap qj (zip xs' xs'')
                      in
                          cqj' </conj/> close env pi' qj'
                      end | _ => Err.error "Unexpected simulating transition in matchIn"
                  )
              )
            )
          end | _ => Err.error "Unexpected transition in matchIn" )
      )

    and matchOut env p q =
      conjunct (
          PRed.reduceA env p PRed.ActOut |>
          foreach (fn(_,PRed.Output (y,avec,ns),cpi,pi) =>
          let
            val y' = NameGen.newName ()
            val avec' = NameGen.newNameVec (List.length avec)
            val ns' = map (fn n => Lst.foldr Psi.Inst.Term.swap n (zip avec avec')) ns
            val cpi' = C.swap (unvar y, y') cpi
            val pi' = Lst.foldr Psi.swap pi (zip avec avec')
          in
            forallC [y'] (
              (cpi' </conj/> freshness avec' p </conj/> freshness avec' q)
                  </imp/> disjunct (
                  QRed.reduceA env q QRed.ActOut |>
                  foreach (fn (_,QRed.Output (y'',avec'',ms),cqj,qj) =>
                      let
                        val cqj' = C.swap (y',unvar y'') (cqj)
                        val qj' = Lst.foldr Psi.swap qj (zip avec' avec'')
                        val ms' = map (fn m => Lst.foldr Psi.Inst.Term.swap m (zip avec' avec'')) ms
                      in
                          cqj' </conj/> conjunct (map termEq (zip ns' ms')) </conj/> close env pi' qj'
                      end | _ => Err.error "Unexpected simulating transition in matchOut"
                  )
              )
            )
          end | _ => Err.error "Unexpected transition in matchOut")
      )

    and matchBrIn env p q =
      conjunct (
          PRed.reduceA env p PRed.ActBrIn |>
          foreach (fn(_,PRed.BrInput (y,xs),cpi,pi) =>
          let
            val y' = NameGen.newName ()
            val xs' = NameGen.newNameVec (List.length xs)
            val cpi' = C.swap (unvar y, y') (cpi)
            val pi' = Lst.foldr Psi.swap pi (zip xs xs')
          in
            forallC (y'::xs') (
              cpi' </imp/> disjunct (
                  QRed.reduceA env p QRed.ActBrIn |>
                  foreach (fn (_,QRed.BrInput (y'',xs''),cqj,qj) =>
                      let
                        val cqj' = C.swap (y',unvar y'') (cqj)
                        val qj' = Lst.foldr Psi.swap qj (zip xs' xs'')
                      in
                          cqj' </conj/> close env pi' qj'
                      end | _ => Err.error "Unexpected simulating transition in matchBrIn"
                  )
              )
            )
          end | _ => Err.error "Unexpected transition in matchBrIn" )
      )

    and matchBrOut env p q =
      conjunct (
          PRed.reduceA env p PRed.ActBrOut |>
          foreach (fn(_,PRed.BrOutput (y,avec,ns),cpi,pi) =>
          let
            val y' = NameGen.newName ()
            val avec' = NameGen.newNameVec (List.length avec)
            val ns' = map (fn n => Lst.foldr Psi.Inst.Term.swap n (zip avec avec')) ns
            val cpi' = C.swap (unvar y, y') (cpi)
            val pi' = Lst.foldr Psi.swap pi (zip avec avec')
          in
            forallC [y'] (
              (cpi' </conj/> freshness avec' p </conj/> freshness avec' q)
                  </imp/> disjunct (
                  QRed.reduceA env q QRed.ActBrOut |>
                  foreach (fn (_,QRed.BrOutput (y'',avec'',ms),cqj,qj) =>
                      let
                        val cqj' = C.swap (y',unvar y'') (cqj)
                        val qj' = Lst.foldr Psi.swap qj (zip avec' avec'')
                        val ms' = map (fn m => Lst.foldr Psi.Inst.Term.swap m (zip avec' avec'')) ms
                      in
                          cqj' </conj/> conjunct (map termEq (zip ns' ms')) </conj/> close env pi' qj'
                      end | _ => Err.error "Unexpected simulating transition in matchBrOut"
                  )
              )
            )
          end | _ => Err.error "Unexpected transition in matchBrOut")
      )
  end (* end of Weak structure *)


  fun bisim env p q =
  let
    val () = log "Bisim Started"
    val timer = Timer.startCPUTimer ()
    val () = Imp.checkBisim := true
    val r = Imp.bisim env p q
    val {usr=usr,sys=sys} = Timer.checkCPUTimer timer
    val () = log ("Finished in " ^ Time.toString usr ^ "s")
  in
    r
  end

  fun sim env p q =
  let
    val () = log "Sim Started"
    val timer = Timer.startCPUTimer ()
    val () = Imp.checkBisim := false
    val r = Imp.bisim env p q
    val {usr=usr,sys=sys} = Timer.checkCPUTimer timer
    val () = log ("Finished in " ^ Time.toString usr ^ "s")
  in
    r
  end

end;


functor WeakStrongBisim (X: sig
  structure Psi : PSI
  structure Slv : SYMBOLIC_CONSTRAINT_SOLVER
  structure SPsi : SYMBOLIC_PSI
  structure C      : SYMBOLIC_BISIM_CONSTRAINT

  sharing Psi = SPsi.Psi = C.Psi
  sharing Psi.Inst = Slv.Inst
end):
sig
  structure Strong : SYMBOLIC_BISIM
  structure Weak   : SYMBOLIC_BISIM
  structure C      : SYMBOLIC_BISIM_CONSTRAINT

  sharing Strong.Psi = Weak.Psi = C.Psi
  sharing Strong.C = Weak.C
  sharing Strong.C.Frame = Weak.C.Frame
  sharing Strong.ClEnv = Weak.ClEnv
end =
struct
  open X

  (*structure C = SymBisimConstraint(Psi)*)
  structure C = C

  structure Red = SymbolicPsiReducer(struct
    structure Sim = SymbolicPsiSimulator(SPsi)
    structure Slv = Slv
  end)

  structure StrongRed = SymbolicStrongPsiReducerBisim(struct
    structure R = Red
    structure C = C
  end)

  structure Strong = Bisim(struct
    structure PRed = StrongRed
    structure QRed = StrongRed
    structure C = C
  end)

  structure WRed = WeakSymbolicPsiReducer(struct
    structure Red = Red
    structure Tr = WeakSymbolicTransition(struct
      structure Psi = Psi
      structure Constraint = Red.Sim.Constraint
    end)
  end)

  structure WeakRed = SymbolicWeakPsiReducerBisim(struct
    structure R = WRed
    structure C = C
  end)

  structure Weak = Bisim(struct
    structure PRed = StrongRed
    structure QRed = WeakRed
    structure C = C
  end)
end;

