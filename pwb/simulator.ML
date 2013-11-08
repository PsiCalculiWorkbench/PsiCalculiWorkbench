(* uses pwb/missing,
        pwb/derivation-tree,
        pwb/psi
*)


(*
 * With a simplified input form (without pattern matching)
 *)
signature PSI_STRONG_ACTION =
sig
  structure Inst : PSI_INSTANCE

  datatype action
    = Tau
    | Output of Inst.term * Inst.name list * Inst.term list
    | Input  of Inst.term * Inst.name list
    | BrOutput of Inst.term * Inst.name list * Inst.term list
    | BrInput  of Inst.term * Inst.name list

  val subj     : action -> Inst.term
  val obj      : action -> Inst.term list
  val bn       : action -> Inst.name list
  val subjSupp : action -> Inst.name list
  val names    : action -> Inst.name list

  include NOMINAL
    where type atom = Inst.name
    where type data = action
    sharing AtomSort = Inst.Sort
end;


functor PsiStrongAction(Inst: PSI_INSTANCE) : PSI_STRONG_ACTION =
struct
  structure Inst = Inst
  open Missing

  structure T = Inst.Term
  structure C = Inst.Cond
  structure A = Inst.Assr

  datatype action
    = Tau
    | Output of Inst.term * Inst.name list * Inst.term list
    | Input  of Inst.term * Inst.name list
    | BrOutput of Inst.term * Inst.name list * Inst.term list
    | BrInput  of Inst.term * Inst.name list

  fun subj (Output (t, _, _))   = t
    | subj (Input  (t, _))      = t
    | subj (BrOutput (t, _, _)) = t
    | subj (BrInput  (t, _))    = t
    | subj Tau                  = Err.undefined "PsiStrongAction.subj Tau"

  fun obj (Output (_, _, ns))   = ns
    | obj (BrOutput (_, _, ns)) = ns
    | obj _                     = Err.undefined "PsiStrongAction.obj default"
    (* | obj (Input  (_, x))    = x *)

  fun bn (Output (_, ns, _))   = ns
    | bn (Input  (_, ns))      = ns
    | bn (BrOutput (_, ns, _)) = ns
    | bn (BrInput  (_, ns))    = ns
    | bn  Tau                  = []

  fun subjSupp Tau   = []
    | subjSupp alpha = subj alpha |> T.support

  fun names (Output (y, a_s, ns)) = (T.support y) @ a_s @ (Lst.flatmap T.support ns)
    | names (Input (y, xs)) = (T.support y) @ xs
    | names (BrOutput (y, a_s, ns)) = (T.support y) @ a_s @ (Lst.flatmap T.support ns)
    | names (BrInput (y, xs)) = (T.support y) @ xs
    | names Tau = []


  structure Nom = Nominal(struct
    type atom = Inst.name
    type data = action

    structure L  = NominalNameList(T)
    structure TL = NominalList(T)

    structure AtomSort = T.AtomSort
    structure DataSort = struct
      datatype sort = StrongAction
      fun eq _ = true
    end

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.StrongAction

    val new = T.new
    val newBasedOn = T.newBasedOn

    fun swap _ Tau = Tau
      | swap ab (Output (subj, avec, obj)) =
        Output (T.swap ab subj, L.swap ab avec, TL.swap ab obj)
      | swap ab (Input (subj, x)) =
        Input (T.swap ab subj, L.swap ab x)
      | swap ab (BrOutput (subj, avec, obj)) =
      (BrOutput (T.swap ab subj, L.swap ab avec, TL.swap ab obj))
      | swap ab (BrInput (subj, x)) =
        BrInput (T.swap ab subj, L.swap ab x)

    fun support (Output (m, avec, n)) =
        (T.support m) @ (Lst.minus (TL.support n) avec)
      | support (Input  (m, _)) = T.support m
      | support (BrOutput (m, avec, n)) =
        (T.support m) @ (Lst.minus (TL.support n) avec)
      | support (BrInput  (m, _)) = T.support m
      | support Tau = []

    fun eq aEq (a,b) = Err.undefined "PsiStrongAction.eq"
  end)
  open Nom
end;

signature SYMBOLIC_TRANSITION_CONSTRAINT =
sig
  structure Inst : PSI_INSTANCE

  type constraint = (Inst.name list * Inst.assertion * Inst.condition list) list

  include NOMINAL
    where type data = constraint
    where type atom = Inst.name
    sharing AtomSort = Inst.Sort

  val subst    : (Inst.name * Inst.term) list      -> constraint -> constraint
  val addFrame : (Inst.name list * Inst.assertion) -> constraint -> constraint
  val addCond  : Inst.condition                    -> constraint -> constraint
  val abstract : Inst.name list                    -> constraint -> constraint
  val compose  : constraint                        -> constraint -> constraint

  val unit : constraint
end;


functor SymbolicOSConstraint(I: PSI_INSTANCE): SYMBOLIC_TRANSITION_CONSTRAINT =
struct
  structure Inst = I
  structure T = I.Term
  structure C = I.Cond

  type atomic = Inst.name list * Inst.assertion * Inst.condition list
  type constraint = atomic list

  val unit = []

  open Missing

  structure AtomicNom = Nominal(
  struct
    type atom = Inst.name
    type data = atomic

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = STConstraint fun eq _ = true end

    val atomSort   = T.atomSort
    fun dataSort _ = DataSort.STConstraint

    structure L = NominalNameList(T)
    structure CL = NominalList(C)

    fun swap (a,b) (avec, psi, phis) =
      (L.swap (a,b) avec, I.Assr.swap (a,b) psi, CL.swap (a,b) phis)

    fun support (avec, psi, phis) =
      Lst.minus ((I.Assr.support psi) @ (CL.support phis)) avec

    val new = I.Term.new
    val newBasedOn = I.Term.newBasedOn

    fun eq alphaEq ((avec,psi,phi), (avec',psi',phi')) = Err.undefined "SymbolicOSConstraint.eq"
  end)

  structure NA = NominalAlpha(AtomicNom)

  structure ConstraintNom = NominalList(AtomicNom)
  open ConstraintNom

  fun subst sigma constr =
    (* avec # sigma *)
    let
      val sigmaNames = (map Tpl.fst sigma) @
                   (List.concat (map (I.Term.support o Tpl.snd) sigma))
      fun freshify (avec, psi, phis) = NA.makeFresh avec (avec, psi, phis) sigmaNames
      fun doSubst  (avec, psi, phis) = (avec, Inst.substA sigma psi, List.map (Inst.substC sigma) phis)
    in
      map (doSubst o freshify) constr
    end

  fun addFrame (bn, psi') constr =
    (* avec # sigma *)
    let
      fun freshify    (avec, psi, phis) = NA.makeFresh avec (avec, psi, phis) bn
      fun doAddFrame  (avec, psi, phis) = (bn@avec, Inst.compose (psi',psi), phis)
    in
      map (doAddFrame o freshify) constr
    end

  fun addCond phi (c::cs) =
    (* avec # sigma *)
    let
      fun freshify   (avec, psi, phis) = NA.makeFresh avec (avec, psi, phis) $ I.Cond.support phi
      fun doAddCond  (avec, psi, phis) = (avec, psi, phi::phis)
    in
      ((c |> freshify |> doAddCond)::cs)
    end
    | addCond phi [] = [([],I.unit,[phi])]

  fun abstract bn constr = map (fn (avec, psi, phis) => (bn@avec, psi, phis)) constr

    fun compose x y = x @ y
end;




signature SYMBOLIC_CONSTRAINT_SOLVER =
sig
  structure Inst       : PSI_INSTANCE
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  sharing Constraint.Inst = Inst

  type solution =
    (string, (Inst.name * Inst.term) list * Inst.assertion) Either.either

  val solve : Constraint.constraint -> solution
end;


signature SYMBOLIC_PSI =
sig
  structure Psi        : PSI
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  structure ClEnv      : PSI_CLAUSE_ENVIRONMENT

  val var : Psi.Inst.name -> Psi.Inst.term

  sharing ClEnv.Cl.Psi = Psi
  sharing Constraint.Inst = Psi.Inst
end;


functor PsiGuarded(P: SYMBOLIC_PSI) =
struct
local open P.Psi open P open Missing in

  structure Cl = ClEnv.Cl

  fun clauseP (Cl.Clause (_,_,p)) = p
  fun clauseArgs (Cl.Clause (_,xvec,_)) = xvec
  fun clauseProcessesWithSameArity e a ar =
    ClEnv.find e a |>
    filter (fn cls => length (clauseArgs cls) = ar) |>
    map clauseP

  fun isInvCycleFree e v Nil = true
    | isInvCycleFree e v (Tau _)                 = true
    | isInvCycleFree e v (Output _)              = true
    | isInvCycleFree e v (Input _)               = true
    | isInvCycleFree e v (BrOutput _)            = true
    | isInvCycleFree e v (BrInput _)             = true
    | isInvCycleFree e v (Assertion _)           = true
    | isInvCycleFree e v (Restriction (_, p))    = isInvCycleFree e v p
    | isInvCycleFree e v (Replication p)         = isInvCycleFree e v p
    | isInvCycleFree e v (Parallel (p, q))       =
        isInvCycleFree e v p andalso isInvCycleFree e v q
    | isInvCycleFree e v (Case cs)               =
        all (fn (phi,p) => isInvCycleFree e v p) cs
    | isInvCycleFree e v (Invocation (a,mvec))   =
    let val ar = length mvec in
        if member (a,ar) v
            then false
            else (clauseProcessesWithSameArity e a ar) |>
                 all (fn p => isInvCycleFree e ((a,ar)::v) p)
    end


  fun guarded' e v Nil                     = true
    | guarded' e v (Tau _)                 = true
    | guarded' e v (Output _)              = true
    | guarded' e v (Input _)               = true
    | guarded' e v (BrOutput _)            = true
    | guarded' e v (BrInput _)             = true
    | guarded' e v (Case cs)               = guarded_case e v cs
    | guarded' e v (Restriction (_, p))    = guarded' e v p
    | guarded' e v (Parallel (p, q))       =
        (guarded' e v p) andalso (guarded' e v q)
    | guarded' e v (Replication p)         = guarded' e v p
    | guarded' e v (Assertion _)           = false
    | guarded' e v (Invocation (a,mvec))   =
        let
          val arity = length mvec
          val visited = Lst.exists
            (fn (a',arity') => arity' = arity andalso
                               a = a') v
          val cls = ClEnv.find e a
          (* consider only those clauses with matching arities *)
          val ps = filter
            (fn cl => arity = length (clauseArgs cl)) cls
        in
          not visited andalso Lst.all (guarded' e ((a,arity)::v) o clauseP) ps
        end
  and guarded_case e v cs = Lst.all (guarded' e v o Tpl.snd) cs

  fun guarded e p = guarded' e [] p
end
end;



signature STRONG_SYMBOLIC_TRANSITION =
sig
  structure Psi        : PSI
  structure Act        : PSI_STRONG_ACTION
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT

  type transition
    = Psi.psi * Act.action * Constraint.constraint * Psi.psi

  val addFrame : (Psi.atom list * Psi.Inst.assertion) -> transition -> transition
        (*
        * TODO: currently I do not need this
        *)
        (*
  include NOMINAL
    where type atom = Psi.Inst.name
    where type data = action
    *)

  sharing Psi.Inst = Constraint.Inst = Act.Inst
end;

signature STRONG_SYMBOLIC_TRANSITION_RESIDUAL =
sig
  structure Tr : STRONG_SYMBOLIC_TRANSITION

  type residual = Tr.Act.action * Tr.Psi.psi

  include NOMINAL
    where type atom = Tr.Psi.Inst.name
    where type data = residual
    sharing AtomSort = Tr.Psi.Inst.Sort
end;

functor StrongSymbolicTransition(A :
    sig
      structure Psi        : PSI
      structure Act        : PSI_STRONG_ACTION
      structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
      sharing Psi.Inst = Constraint.Inst = Act.Inst
    end): STRONG_SYMBOLIC_TRANSITION =
struct
  open A

  type transition
    = Psi.psi * Act.action * Constraint.constraint * Psi.psi

  fun addFrame fr (p,act,c,q) = (p,act,Constraint.addFrame fr c,q)
end;


functor StrongSymbolicTransitionResidual(Tr : STRONG_SYMBOLIC_TRANSITION):
    STRONG_SYMBOLIC_TRANSITION_RESIDUAL =
struct
  structure Tr = Tr
  structure T = Tr.Psi.Inst.Term
  type residual = Tr.Act.action * Tr.Psi.psi

  structure Nom = Nominal(struct
    type atom = T.atom
    type data = residual

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = SSTResidual fun eq _ = true end

    structure TL = NominalList(Tr.Psi.Inst.Term)

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.SSTResidual

    fun swap pi (alpha, p) = (Tr.Act.swap pi alpha, Tr.Psi.swap pi p)

    fun support (Tr.Act.Tau, p) = Tr.Psi.support p
      | support (alpha,p) =
      let
        val obj = case alpha of
                       Tr.Act.Output (_,_,ms) => TL.support ms
                     | _ => []
      in (Tr.Act.subjSupp alpha) @
         (Lst.minus (obj @ (Tr.Psi.support p)) (Tr.Act.bn alpha))
      end
    val new = Tr.Psi.Inst.Term.new
    val newBasedOn = Tr.Psi.Inst.Term.newBasedOn

    fun eq _ _ = Err.undefined "StrongSymbolicTransitionResidual.eq"
  end)
  open Nom
end;


signature SYMBOLIC_PSI_SIMULATOR =
sig
  structure Psi        : PSI
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  structure Tr         : STRONG_SYMBOLIC_TRANSITION
  structure ClEnv      : PSI_CLAUSE_ENVIRONMENT

  datatype action_type = ANYa | VISa | OUTa | INa | BROUTa | BRINa | TAUa

  val reduce :
    ClEnv.env -> Psi.psi -> Tr.transition list

  val reduceA :
    ClEnv.env -> Psi.psi -> action_type -> Tr.transition list

  sharing Psi = ClEnv.Cl.Psi = Tr.Psi
  sharing Psi.Inst = Constraint.Inst
end;


signature SYMBOLIC_PSI_REDUCER =
sig
  structure Sim : SYMBOLIC_PSI_SIMULATOR
  structure Slv : SYMBOLIC_CONSTRAINT_SOLVER
  sharing Sim.Psi.Inst = Slv.Inst

  val reduce :
    Sim.ClEnv.env -> Sim.Psi.psi -> Sim.Constraint.constraint ->
        (Sim.Psi.psi * Sim.Tr.Act.action * Sim.Constraint.constraint *
         Slv.solution * Sim.Psi.psi) list

  val reduceA :
    Sim.ClEnv.env -> Sim.Psi.psi -> Sim.action_type ->
        Sim.Constraint.constraint ->
        (Sim.Psi.psi * Sim.Tr.Act.action * Sim.Constraint.constraint *
         Slv.solution * Sim.Psi.psi) list
end;


functor SymbolicPsiReducer(A: sig
  structure Sim : SYMBOLIC_PSI_SIMULATOR
  structure Slv : SYMBOLIC_CONSTRAINT_SOLVER
  sharing Sim.Psi.Inst = Slv.Inst
end): SYMBOLIC_PSI_REDUCER =
struct
  open Missing
  open A
  structure C = Sim.Constraint

  fun onlySolvable trs =
    List.filter (fn (tr as (_,_,_,s,_)) =>
        s |> either (const false) (const true)) trs

  fun solve c trs = trs |>
    map (fn (tr as (p,act,cstr,p')) =>
        let val aggrC = c <//C.compose//> cstr
        in (p, act, aggrC, Slv.solve aggrC, p') end)

  fun reduce env proc c =
    Sim.reduce env proc |> solve c |> onlySolvable

  fun reduceA env proc tAct c =
    Sim.reduceA env proc tAct |> solve c |> onlySolvable
end;


functor SymbolicPsiSimulator (SI: SYMBOLIC_PSI)
    : SYMBOLIC_PSI_SIMULATOR =
struct
  structure P          = SI.Psi
  structure Psi        = P
  structure Constraint = SI.Constraint
  structure Env        = SI.ClEnv
  structure ClEnv      = Env
  structure Clause     = SI.ClEnv.Cl
  structure Tr         = StrongSymbolicTransition(struct
                            structure Psi        = P
                            structure Act        = PsiStrongAction(Psi.Inst)
                            structure Constraint = Constraint
                          end)
local
  open Fun
  open Either
  open Tr
in
  structure I          = P.Inst
  structure T          = I.Term
  structure A          = I.Assr
  structure C          = I.Cond
  structure Cl         = Clause

  structure Frame      = Frame(P)
  structure L          = NominalNameList(T)
  structure TL         = NominalList(T)
  structure N          = NominalName(T)
  structure PAlpha     = NominalAlpha(P)
  structure FrameAlpha = NominalAlpha(Frame)

  type name       = I.name
  type term       = I.term
  type assertion  = I.assertion
  type condition  = I.condition
  type constraint = Constraint.constraint

  type channeleq = (name list * assertion * term * term)
  datatype suspended_constraint =
         Constr   of constraint
       | BrConstr of name list * constraint
       | IOConstr of channeleq * constraint


  structure G = PsiGuarded(SI)
  val guarded = G.guarded

  structure K : NOMINAL =
  struct
    type atom = name
    type data = suspended_constraint

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = KSort fun eq _ = true end

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.KSort

    val swapAtom = P.swapAtom

    fun swap (a,b) (Constr(c)) =
      Constr(Constraint.swap (a,b) c)
      | swap (a,b) (BrConstr(bs, c)) =
      BrConstr(L.swap (a,b) bs,
             Constraint.swap (a,b) c)
      | swap (a,b) (IOConstr((bs,psi,m,n), c)) =
      IOConstr((L.swap (a,b) bs,
              A.swap (a,b) psi,
              T.swap (a,b) m,
              T.swap (a,b) n),
             Constraint.swap (a,b) c)

    fun support (Constr(c))      = Constraint.support c
      | support (BrConstr(_, c)) = Constraint.support c
      | support (IOConstr((bs,psi,m,n), c)) =
      (Lst.minus ((T.support n) @ (A.support psi) @ (T.support m)) bs)
      @ (Constraint.support c)

    fun fresh x c = not $ Lst.member x (support c)

    val new = P.new
    val newBasedOn = P.newBasedOn
    val newsBasedOn = P.newsBasedOn

    fun eqData _ = Err.undefined "SymbolicPsiSimulator.K.eqData"
  end;
  structure KAlpha = NominalAlpha(K)


  fun isTau Act.Tau = true
    | isTau _       = false

  fun isOutput (Act.Output _) = true
    | isOutput _              = false

  fun isInput (Act.Input _) = true
    | isInput _             = false

  fun isBrOutput (Act.BrOutput _) = true
    | isBrOutput _                = false

  fun isBrInput (Act.BrInput _) = true
    | isBrInput _               = false

  val agentBinders = Frame.binders o Frame.frameOf

  structure ActAlpha = NominalAlpha(Act);
  structure Residual = StrongSymbolicTransitionResidual(Tr)
  structure ResidualAlpha = NominalAlpha(Residual)

  type symbolic_transition
    = P.psi * Act.action * suspended_constraint * P.psi

  datatype action_type = ANYa | VISa | OUTa | INa | BROUTa | BRINa | TAUa

  datatype symbolic_rules
    = IN | OUT | BRIN | BROUT | TAU
    | CASE  of condition
    | RES of name (* the SCOPE and OPEN rules are handled by this one *)
    | PARLEFT
    | PARRIGHT
    | COMLEFT
    | COMRIGHT
    | REPCOM
    | REPI
    | INVOCATION

  fun abstractP ns p = List.foldr P.Restriction p ns

  fun abstractK ns (Constr(c)) = Constr(Constraint.abstract ns c)
    | abstractK ns (BrConstr(bs, c)) =
      (* What to do if ns and bs intersect? *)
      BrConstr(bs,Constraint.abstract ns c)
    | abstractK ns (IOConstr((bs,psi,m,n), c)) =
      IOConstr((ns@bs,psi,m,n), Constraint.abstract ns c)

  fun addCond phi (Constr(c))      = Constr(      Constraint.addCond phi c)
    | addCond phi (BrConstr(br,c)) = BrConstr(br, Constraint.addCond phi c)
    | addCond phi (IOConstr(io,c)) = IOConstr(io, Constraint.addCond phi c)

  fun addFrame fr (Constr(c)) = Constr(Constraint.addFrame fr c)
    | addFrame fr (BrConstr(bs,c)) = BrConstr(bs,Constraint.addFrame fr c)
    | addFrame (cs,psi') (IOConstr(io as (bs,_,_,_),c)) =
      case KAlpha.makeFresh bs (IOConstr(io,[])) cs of
        IOConstr((bs,psi,m,n),_) =>
        IOConstr((cs@bs, I.compose (psi',psi), m,n),
               Constraint.addFrame (cs,psi') c)
      |_ =>  Err.undefined "SymbolicPsiSimulator.addFrame makeFresh"

  fun swapPremises2 ([a, b], r, d) = ([b, a], r, d)
    | swapPremises2 _ = Err.undefined "SymbolicPsiSimulator.swapPremises2"

  fun unvar n = n |> T.support |> List.hd

  structure DT =
  struct
    type source  = (P.psi * (action_type list))
    type premise = symbolic_transition
    type rule    = symbolic_rules
    type context = SI.ClEnv.env

    fun mem (a:action_type) l = Lst.exists (fn x => x=a) l

    fun inferTAU (P.Tau _, acts) = if mem TAUa acts then SOME ([], TAU) else NONE
      | inferTAU _ = NONE

    fun inferIN (P.Input _, acts) =
        if mem INa acts then SOME ([], IN) else NONE
      | inferIN _ = NONE

    fun inferOUT (P.Output _, acts) =
        if mem OUTa acts then SOME ([], OUT) else NONE
      | inferOUT _ = NONE

    fun inferBRIN (P.BrInput _, acts) =
        if mem BRINa acts then SOME ([], BRIN) else NONE
      | inferBRIN _ = NONE

    fun inferBROUT (P.BrOutput _, acts) =
        if mem BROUTa acts then SOME ([], BROUT) else NONE
      | inferBROUT _ = NONE

    fun inferRES (P.Restriction (a,p),ac) = SOME ([ (p,ac) ], RES a)
      | inferRES _ = NONE

    fun inferREPI e (P.Replication(p),ac) =
        if guarded e p
      then SOME ([(p,ac)], REPI)
        else Err.error "Unguarded process under !."
      | inferREPI _ _ = NONE

    fun inferREPCOM e (P.Replication(p), ac) =
        if mem TAUa ac then
          if guarded e p
            then SOME ([(p,[INa]),(p,[OUTa])], REPCOM)
            else Err.error "Unguarded process under !."
        else NONE
      | inferREPCOM _ _ = NONE

    fun inferPARs (P.Parallel (p,q),ac)  =
        [ ([(p,ac)], PARLEFT),
        ([(q,ac)], PARRIGHT) ]
      | inferPARs _ = []

    fun both f (a,b) = (f a, f b)

    fun inferCOMs (P.Parallel (p,q), ac) =
        (if mem TAUa ac
         then [(OUTa,INa,true),(INa,OUTa,false) ]
         else [])@
        (if mem BROUTa ac
         then [(BROUTa,BRINa,true), (BRINa,BROUTa,false)]
         else [])@
        (if mem BRINa ac
         then [(BRINa,BRINa,true)]
         else [])
            |>
        List.foldr
        (fn ((a,b,c),((l1,l2),(r1,r2))) =>
                if c
                then ((a::l1,b::l2),(r1,r2))
                else ((l1,l2),(a::r1,b::r2)))
            (([],[]),([],[]))
        |> both (fn (l1,l2) => [(p,l1),(q,l2)])
        |> (fn (l,r) => [(l,COMLEFT),(r,COMRIGHT)])
        |> List.filter (fn (l,_) =>
              List.all (fn (_,l') =>
                 not $ List.null l') l)
      | inferCOMs _ = []

    fun inferCASEs e (P.Case cs,ac) =
            map (fn (phi, p) =>
                    if guarded e p
                then ([(p,ac)], CASE phi)
                    else Err.error "Unguarded process under CASE."
                ) cs
      | inferCASEs _ _ = []

    fun inferINVOCATIONs e (P.Invocation (a, mvec),ac) =
        let
            val clauses = SI.ClEnv.find e a
            val valid = List.filter
                            (fn (cl as (Cl.Clause (a, xvec, p))) =>
                                (List.length xvec = List.length mvec) andalso
                                guarded e p andalso
                                (Cl.support cl = [])
                            ) clauses
        in
            case valid of
                [] => []
              | _  => map (fn p => ([ (p,ac) ], INVOCATION)) $
                          map (fn (Cl.Clause (a,xvec,p)) =>
                                  P.subst p (Lst.zip xvec mvec)) valid
        end
      | inferINVOCATIONs _ _ = []


    fun infer e a =
    let
      val rules = [ inferOUT, inferIN, inferTAU, inferBROUT, inferBRIN, inferRES, inferREPI e, inferREPCOM e ]
      val r = (inferPARs a) @ (inferCASEs e a) @ (inferINVOCATIONs e a) @ (inferCOMs a)
      val s = rules |> map (fn rule => rule a) |> Opt.filterSome
    in
      r @ s
    end

    (* TODO: add a wellformedness condition before simulating *)

    fun eval_axiom e (TAU, (ip as (P.Tau p), _)) =
      SOME (ip, Act.Tau, Constr [], p)

      | eval_axiom e (IN, (ip as (P.Input (m, xs, _, p)),_)) =
        (* y # psi, m, p, x   *)
        let val y = P.new (xs @ (T.support m) @ (P.support p))
        in SOME (ip, Act.Input (SI.var y, xs),
              IOConstr(([], I.unit, m, SI.var y),[]), p)
        end

      | eval_axiom e (OUT, (ip as (P.Output (m, ns, p)),_)) =
        (* y # psi, m, p, ns    *)
        let val y = (P.new ((TL.support ns) @ (T.support m) @ (P.support p)))
        in SOME ( ip, Act.Output (SI.var y, [], ns),
              IOConstr(([], I.unit, m, SI.var y),[]), p)
        end
      | eval_axiom e (BRIN, (ip as (P.BrInput (m, xs, _, p)),_)) =
        (* y # psi, m, p, x   *)
        let val y = P.new (xs @ (T.support m) @ (P.support p))
        in SOME ( ip, Act.BrInput (SI.var y, xs),
              BrConstr(T.support m,[([], I.unit, [I.brReceive(SI.var y,m)])]), p)
        end

      | eval_axiom e (BROUT, (ip as (P.BrOutput (m, ns, p)),_)) =
        (* y # psi, m, p, ns    *)
        let val y = (P.new ((TL.support ns) @ (T.support m) @ (P.support p)))
        in SOME ( ip, Act.BrOutput (SI.var y, [], ns),
              BrConstr(T.support m,[([], I.unit, [I.brTransmit(m, SI.var y)])]), p)
        end
      | eval_axiom _ _ = Err.undefined "Simulator.eval_axiom default"


    fun switchSubj (alpha, c) name =
    let
      val alpha' =
        case alpha of
             Act.Output   (_, avec, ns) => Act.Output   (name, avec, ns)
           | Act.Input    (_, xs)       => Act.Input    (name, xs)
         (*| Act.BrOutput (_, avec, ns) => Act.BrOutput (name, avec, ns)
           | Act.BrInput  (_, xs)       => Act.BrInput  (name, xs) *)
           | _ => Err.undefined "Simulator.switchSubj 1"
      val c' =
        case c of
             (IOConstr((avec, psi, ms, y),cs)) =>
            IOConstr((avec, psi, ms, name),cs)
           | _ => Err.undefined "Simulator.switchSubj 2"
    in
      (alpha', c')
    end



    fun evalPAR ([(iP, alpha, c, dP)], pq as (P.Parallel (p, q))) =
        let
          fun permuteL swap pi l = Lst.foldl swap l pi

          (* bn(alpha) # Q *)

          val pi = ResidualAlpha.freshNames (Act.bn alpha) $
                   (Act.subjSupp alpha)@(P.support q)
          val dP = PAlpha.permute pi dP
          val alpha = case alpha of
                           Act.Tau => Act.Tau
                         | Act.Output (m,avec,ns) =>
                           Act.Output(m, permuteL L.swap pi avec,
                              permuteL TL.swap pi ns)
                         | Act.Input (m,xs) =>
                     Act.Input(m, permuteL L.swap pi xs)
                         | Act.BrOutput (m,avec,ns) =>
                           Act.BrOutput(m, permuteL L.swap pi avec,
                              permuteL TL.swap pi ns)
                         | Act.BrInput (m,xs) =>
                     Act.BrInput(m, permuteL L.swap pi xs)

          val bqvec' = Frame.binders (Frame.frameOf q)
          val pi = FrameAlpha.freshNames bqvec' (P.support p)
          val q = PAlpha.permute pi q
          val fQ = Frame.frameOf q
          val bqvec = Frame.binders fQ
          val psiQ = Frame.assertion fQ
        in
          SOME (pq, alpha, addFrame (bqvec,psiQ) c, P.Parallel (dP,q))
        end
      | evalPAR _ = Err.undefined "Simulator.evalPAR default"


    fun evalCOM ([(iP, oP as Act.Output(_,avec,ns), (IOConstr(ioP as (bpvec, psiP, _, _),cp)), dP),
                  (iQ, Act.Input (z, xs),          (IOConstr(ioQ as (bqvec, psiQ, _, _),cq)), dQ)]
                  ,_,
                  (oPQ,_)) sym =
    if not (Lst.all (fn (x,n) => I.canSubs (I.Term.atomSort x) (I.Term.dataSort n))
                    (Lst.zip xs ns))
      then NONE
      else
        let
          (* avec # Q *)
          val (avec, ns, dP) =
            case ResidualAlpha.makeFresh avec (oP, dP) (P.support iQ)
             of (Act.Output(_,avec,ns),dp) => (avec,ns,dp)
              | _ => Err.undefined "Simulator.evalCOM makeFresh"

          val pq' = (if sym then Tpl.swap else id) (dP, P.subst dQ (Lst.zip xs ns))
          val pq = abstractP avec (P.Parallel pq')
          val c =
          case KAlpha.makeFresh bpvec  (IOConstr(ioP,[])) (bqvec @ (P.support iQ)) of
                IOConstr((bvec1, psiP, m, _),_) =>
            (case KAlpha.makeFresh bqvec (IOConstr(ioQ,[])) (bpvec @ (P.support iP)) of
                IOConstr((bvec2, psiQ, n, _),_) =>
              (bvec1 @ bvec2, psiP </I.compose/> psiQ, [I.chaneq (m, n)])
              | _ => Err.undefined "Simulator.evalCOM makeFresh 2")
              | _ => Err.undefined "Simulator.evalCOM makeFresh 1"
        in
          SOME (oPQ, Act.Tau,
            Constr(c :: Constraint.addFrame (bqvec, psiQ) cp
                      @ Constraint.addFrame (bpvec, psiP) cq),
              pq)
    end
      | evalCOM _ _ = Err.undefined "Simulator.evalCOM default"


    fun evalBRCOM ([(iP, oP as Act.BrOutput(_,avec,_), (BrConstr(np,cp)), dP),
                    (iQ,       Act.BrInput (z, xs),    (BrConstr(nq,cq)), dQ)]
                  ,_,
                  (oPQ,_)) sym =
      let
      (* avec # Q *)
      val (ch,avec,ns, dP) =
        case ResidualAlpha.makeFresh avec (oP, dP) (P.support iQ)
         of (Act.BrOutput(ch,avec,ns),dp) => (ch,avec,ns,dp)
          | _ => Err.undefined "Simulator.evalBRCOM makeFresh"

      val (bpvec,psiP) = case Frame.frameOf iP of Frame.Frame f => f
      val (bqvec,psiQ) = case Frame.frameOf iQ of Frame.Frame f => f
      val pq = P.Parallel $ (if sym then Tpl.swap else id) (dP, P.subst dQ (Lst.zip xs ns))
    in
      SOME (oPQ, Act.BrOutput(ch,avec,ns),
        BrConstr(Lst.intersection np nq,
             Constraint.addFrame (bqvec, psiQ) cp
                 @ Constraint.addFrame (bpvec, psiP) (Constraint.swap (unvar ch, unvar z) cq)),
          pq)
    end
      | evalBRCOM _ _ = Err.undefined "Simulator.evalBRCOM default"



    fun swaps p [] = p
      | swaps p (ab::l) = swaps (P.swap ab p) l


    fun evalBRMERGE ([(iP, oP as Act.BrInput(x,xs), (BrConstr(np,cp)), dP),
                      (iQ,       Act.BrInput(y,ys), (BrConstr(nq,cq)), dQ)]
                  ,_,
                  (oPQ,_)) =
      let
      val (ch, ns, dP') =
        case ResidualAlpha.makeFresh ((T.support x)@xs) (oP, dP) (P.support iQ)
         of (Act.BrInput(ch,ns),dp) => (ch,ns,dp)
          | _ => Err.undefined "Simulator.evalBRMERGE makeFresh"

      val (bpvec,psiP) = case Frame.frameOf iP of Frame.Frame f => f
      val (bqvec,psiQ) = case Frame.frameOf iQ of Frame.Frame f => f
      val pq = P.Parallel(dP', swaps dQ (Lst.zip ys ns))
    in
      SOME (oPQ, Act.BrInput(ch,xs),
        BrConstr(Lst.intersection np nq,
             Constraint.addFrame (bqvec, psiQ) cp
                 @ Constraint.addFrame (bpvec, psiP) (Constraint.swap (unvar ch, unvar y) cq)),
          pq)
    end
      | evalBRMERGE _ = Err.undefined "Simulator.evalBRMERGE default"


    fun evalREPCOM ([(p1, alpha1 as Act.Output (y, avec, ns),
                            (IOConstr(c1 as (bvec1, _, _, _),cs1)), dP1),
                     (p2, Act.Input (z, xs),
                            (IOConstr(c2 as (bvec2, _, _, _),cs2)), dP2)],
                    REPCOM,
                    (p,_)) sym =
    let
      val sw = if sym then Tpl.swap else id
      val (alpha1, dP1) =
        ResidualAlpha.makeFresh avec (alpha1, dP1) (P.support p)
      val c =
      case KAlpha.makeFresh bvec1  (IOConstr(c1,[])) (bvec2 @ (P.support p2)) of
            IOConstr((bvec1, _, m, _),_) =>
        (case KAlpha.makeFresh bvec2 (IOConstr(c2,[])) (bvec1 @ (P.support p1)) of
            IOConstr((bvec2, _, n, _),_) => (* frame of p1=p2 is equivalent to I.unit. *)
           Constr((bvec1 @ bvec2, I.unit, [I.chaneq (m, n)]) :: (cs1 @ cs2))
          | _ => Err.undefined "Simulator.evalREPCOM makeFresh 2")
          | _ => Err.undefined "Simulator.evalREPCOM makeFresh 1"
      val (xs,dP2) =
        case ResidualAlpha.makeFresh xs (Act.Input(z,xs), dP2) (P.support p) of
          (Act.Input(_,xs), dP2) => (xs,dP2)
          | _ => Err.undefined "Simulator.evalREPCOM makeFresh 3"
      val dP = abstractP avec $ P.Parallel $
            sw (dP1, P.subst (P.Parallel (dP2, p)) (Lst.zip xs ns))
    in
        SOME (p, Act.Tau, c, dP)
    end
      | evalREPCOM _ _ = Err.undefined  "Simulator.evalREPCOM default"


    fun eval e (premises as [(iP, alpha, c, dP)], PARLEFT,  (P.Parallel (p, q),_)) =
        evalPAR (premises, P.Parallel (p, q))

      | eval e (premises as [(iQ, alpha, c, dQ)], PARRIGHT, (P.Parallel (p, q),_)) =
        Opt.some
            (fn (P.Parallel(q,p), alpha, c, P.Parallel(dq,dp)) =>
                (P.Parallel(p,q), alpha, c, P.Parallel(dp,dq))
              | _ => Err.undefined "Simulator.eval PAR RIGHT")
            (evalPAR (premises, (P.Parallel (q, p))))

      | eval e (r as ([(_,Act.Output(_,_,ns),_,_), (_,Act.Input(_,xs),_,_)], COMLEFT, (oPQ, _))) =
        if List.length ns <> List.length xs then NONE else evalCOM r false

      | eval e (r as ([(_,Act.BrOutput(_,_,ns),_,_), (_,Act.BrInput(_,xs),_,_)], COMLEFT, (oPQ, _))) =
        if List.length ns <> List.length xs then NONE else evalBRCOM r false

      | eval e (r as ([(_,Act.BrInput(_,ns),_,_), (_,Act.BrInput(_,xs),_,_)], COMLEFT, (oPQ, _))) =
        if List.length ns <> List.length xs then NONE else evalBRMERGE r

      | eval e (_, COMLEFT, _) = NONE

      | eval e (r as ([(_,Act.Input(_,xs),_,_), (_,Act.Output(_,_,ns),_,_)], COMRIGHT, (oPQ, _))) =
        if List.length ns <> List.length xs then NONE else evalCOM (swapPremises2 r) true

      | eval e (r as ([(_,Act.BrInput(_,xs),_,_), (_,Act.BrOutput(_,_,ns),_,_)], COMRIGHT, (oPQ, _))) =
        if List.length ns <> List.length xs then NONE else evalBRCOM (swapPremises2 r) true

      | eval e (_, COMRIGHT, _) = NONE

      | eval e ([(iP, alpha, c, dP)], RES a, (cP as (P.Restriction (_, p)),_)) =
      (*
        (*
         * TODO: this needs more investigation. I, rg, cannot understand why the
         * commented out versions does not work, but the short version below
         * does.
         *)

        if isTau alpha then (* SCOPE trivially a # alpha *)
            SOME (cP, alpha, abstractK [a] c, P.Restriction (a, dP))
        else
          let
            (* in case alpha needs a subject change *)
            val (alpha, c) = if Lst.member a (Act.subjSupp alpha)
                                (* TODO: add more stuff to the support *)
                                (* XXX: does not switch subjects of broadcast actions *)
                                then switchSubj (alpha, c) $ SI.var $
                                        L.new (a :: K.support c)
                                else (alpha, c)

            val alphaNames = Act.names alpha
          in
            (* in semantics presentation, alpha contains all names in its
             * support including the binders. *)
            case alpha of
                 Act.Input (y, a_s) => (* SCOPE when alpha = input action *)
                    (* when a is NOT fresh for alpha *)
                    if Lst.member a alphaNames
                    then let val a' = L.newBasedOn a (a::(a_s @ P.support dP)) in
                           SOME (cP, alpha, abstractK [a'] c,
                                 P.Restriction (a', P.swap (a,a') dP))
                         end
                    else (* when a is fresh for alpha *)
                      SOME (cP, alpha, abstractK [a] c, P.Restriction (a, dP))

               | Act.Output (y, a_s, ns) =>
                   let
                     val objSupp = Lst.flatmap T.support ns
                     val (memAs, memNs) = (Lst.member a a_s, Lst.member a objSupp)
                   in
                     case (memAs, memNs) of
                          (false, true) =>  (* OPEN *)
                            SOME (cP, Act.Output (y, a::a_s, ns), abstractK [a] c, dP)
                        | (false, false) => (* SCOPE *)
                            SOME (cP, alpha, abstractK [a] c, P.Restriction (a,dP))
                        | (true, _) => (* SCOPE *)
                            let val a' = L.newBasedOn a
                                    (a::(T.support y @ a_s @ objSupp @ K.support c @
                                    P.support dP))
                            in SOME (cP, alpha, abstractK [a'] c,
                                     P.Restriction (a', P.swap (a,a') dP))
                            end
                   end

               | Act.Tau => Err.undefined "Undefined case in Simulator.eval REP case"

               (* XXX: WARNING the code below is just a copy & paste of the
                * above where Input and Ouput are replace with BrInput and
                * BrOutout respectively *)
               | Act.BrInput (y, a_s) => (* SCOPE when alpha = input action *)
                    (* when a is NOT fresh for alpha *)
                    if Lst.member a alphaNames
                    then let val a' = L.newBasedOn a (a::(a_s @ P.support dP)) in
                           SOME (cP, alpha, abstractK [a'] c,
                                 P.Restriction (a', P.swap (a,a') dP))
                         end
                    else (* when a is fresh for alpha *)
                      SOME (cP, alpha, abstractK [a] c, P.Restriction (a, dP))

               | Act.BrOutput (y, a_s, ns) =>
                   let
                     val objSupp = Lst.flatmap T.support ns
                     val (memAs, memNs) = (Lst.member a a_s, Lst.member a objSupp)
                   in
                     case (memAs, memNs) of
                          (false, true) =>  (* OPEN *)
                            SOME (cP, Act.Output (y, a::a_s, ns), abstractK [a] c, dP)
                        | (false, false) => (* SCOPE *)
                            SOME (cP, alpha, abstractK [a] c, P.Restriction (a,dP))
                        | (true, _) => (* SCOPE *)
                            let val a' = L.newBasedOn a
                                    (a::(T.support y @ a_s @ objSupp @ K.support c @
                                    P.support dP))
                            in SOME (cP, alpha, abstractK [a'] c,
                                     P.Restriction (a', P.swap (a,a') dP))
                            end
                   end
          end
          *)

        if      isTau alpha orelse Act.fresh a alpha                        (* SCOPE *)
        then
            SOME (cP, alpha, abstractK [a] c, P.Restriction(a,dP))
        else if Lst.member a (Act.subjSupp alpha)
        then
          let val (alpha, c) = switchSubj (alpha, c) $
                                SI.var $ L.newBasedOn a (a :: K.support c)
          in SOME (cP, alpha, abstractK [a] c, P.Restriction(a,dP))
          end
        else
          (case alpha of     (* OPEN *)
              Act.Output (y, a_s, ns) =>
              if Lst.member a (TL.support ns)
              then SOME (cP, Act.Output (y, (a :: a_s), ns), abstractK [a] c, dP)
              else NONE
            | Act.BrOutput (y, a_s, ns) =>
              if Lst.member a (TL.support ns)
              then SOME (cP, Act.BrOutput (y, (a :: a_s), ns), abstractK [a] c, dP)
              else NONE
            |_=>NONE)   (* What to do if a is an input variable? *)




      | eval e (_, RES _, _) = NONE

      (* TODO: clear this with Magnus *)
      | eval e ([(iP, alpha, c, dP)], CASE cond, (cases,_)) =
        let
            val n = L.new ((Act.subjSupp alpha) @ C.support cond @ K.support c)
            val (alpha, c) = if isTau alpha
                             then (alpha,c)
                             else switchSubj (alpha,c) (SI.var n)
        in
            SOME (cases, alpha, addCond cond c, dP)
        end

      | eval e ([(iP, alpha, c, dP)], REPI,  (p,_)) =
        SOME (p, alpha, c, P.Parallel (dP, p))

      | eval e (r as ([(_, Act.Output(_,_,ns), _, _), (_, Act.Input(_,xs), _, _)], REPCOM, _)) =
        if List.length ns <> List.length xs then NONE else evalREPCOM r true
      | eval e (_,REPCOM,_) = NONE

      | eval e ([(ps, alpha, c, dP)], INVOCATION, (amvec,_)) = SOME (amvec, alpha, c, dP)

      | eval _ _ = Err.undefined "Simulator.eval default"

  end; (* END : DT *)

  structure D = DerivationTree(DT)


  fun advance (IOConstr((bs,psi,m,n), c)) = (bs, psi, [I.chaneq(m, n)])::c
    | advance (BrConstr(_, c)) = c
    | advance (Constr(c)) = c


  fun reduceA e p ac =
  let
    val ac' = case ac of
                  ANYa => [INa,OUTa,BRINa,BROUTa,TAUa]
                | VISa => [INa,OUTa,BRINa,BROUTa]
                | _    => [ac]
    val tree = D.eval_all e (p,ac')
    val tr  = map (fn (D.EInf (_,_,conclusion)) => conclusion) tree
    val tr' = map (fn (p, alpha, c, p') => (p,alpha, advance c, p')) tr
  in
    tr'
  end

  fun reduce e p = reduceA e p ANYa

  fun debugTree p =
    D.eval_all ClEnv.empty p


end;
end;

