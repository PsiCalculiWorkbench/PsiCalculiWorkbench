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

  val subj : action -> Inst.term
  val obj  : action -> Inst.term list
  val bn   : action -> Inst.name list

  include NOMINAL
    where type atom = Inst.name
    where type data = action
    sharing AtomSort = Inst.Sort
end;


functor PsiStrongAction(Inst: PSI_INSTANCE) : PSI_STRONG_ACTION =
struct
  structure Inst = Inst

  datatype action
    = Tau
    | Output of Inst.term * Inst.name list * Inst.term list
    | Input  of Inst.term * Inst.name list

  fun subj (Output (t, _, _)) = t
    | subj (Input  (t, _))    = t
    | subj _                  = Err.undefined ()

  fun obj (Output (_, _, ns)) = ns
    | obj _                   = Err.undefined ()
    (* | obj (Input  (_, x))    = x *)

  fun bn (Output (_, ns, _)) = ns
    | bn (Input  (_, ns))    = ns
    | bn  Tau                = []


  structure Nom = Nominal(struct
    type atom = Inst.name
    type data = action


    structure T = Inst.Term
    structure C = Inst.Cond
    structure A = Inst.Assr

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
      | swap (a,b) (Input (subj, x)) =
        Input (T.swap (a,b) subj, L.swap (a,b) x)

    fun support (Output (m, avec, n)) =
        (T.support m) @ (Lst.minus (TL.support n) avec)
      | support (Input  (m, _)) = T.support m
      | support Tau = []

    fun eq aEq (a,b) = Err.error "TODO: define alpha equivalence"
  end)
  open Nom
end;

signature SYMBOLIC_TRANSITION_CONSTRAINT =
sig
  structure Inst : PSI_INSTANCE

  (* Constraints used in the operational semantics *)
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
end;


functor SymbolicOSConstraint(I: PSI_INSTANCE): SYMBOLIC_TRANSITION_CONSTRAINT =
struct
  structure Inst = I
  structure T = I.Term
  structure C = I.Cond

  type atomic = Inst.name list * Inst.assertion * Inst.condition list
  type constraint = atomic list

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

    fun eq alphaEq ((avec,psi,phi), (avec',psi',phi')) = Err.undefined ()
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

  (* If constraint can't be solved, returns LEFT with a list of unsolvable
   * conditions. If constraint can be solved then returns RIGHT with solutions
   *)
  val solve :
    Constraint.constraint ->
    ( Inst.condition list list (* counter examples *)
      (*    [ ( sigma               ,       psi ) ] *)
    , ((Inst.name * Inst.term) list * Inst.assertion) list (* solutions *)
    ) Either.either


  sharing Constraint.Inst = Inst
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

  fun clauseP (_,_,p) = p
  fun clauseArgs (_,xvec,_) = xvec

  fun guarded' e v Nil                     = true
    | guarded' e v (Output _)              = true
    | guarded' e v (Input _)               = true
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
      in (T.support (Tr.Act.subj alpha)) @
         (Lst.minus (obj @ (Tr.Psi.support p)) (Tr.Act.bn alpha))
      end
    val new = Tr.Psi.Inst.Term.new
    val newBasedOn = Tr.Psi.Inst.Term.newBasedOn

    fun eq _ _ = Err.error "Define alpha equivalence for residual"
  end)
  open Nom
end;


signature SYMBOLIC_PSI_SIMULATOR =
sig
  structure Psi        : PSI
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  structure Tr         : STRONG_SYMBOLIC_TRANSITION
  structure ClEnv      : PSI_CLAUSE_ENVIRONMENT

  datatype action_type = ANYa | VISa | OUTa | INa | TAUa

  val reduce :
    ClEnv.env -> Psi.psi -> Tr.transition list

  val reduceA :
    ClEnv.env -> Psi.psi -> action_type -> Tr.transition list

  sharing Psi = ClEnv.Cl.Psi = Tr.Psi
  sharing Psi.Inst = Constraint.Inst
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

    fun swap (a,b) (Constr(c)) = Constr(Constraint.swap (a,b) c)
      | swap (a,b) (IOConstr((bs,psi,m,n), c)) = 
	IOConstr((L.swap (a,b) bs, 
		  A.swap (a,b) psi, 
		  T.swap (a,b) m, 
		  T.swap (a,b) n),
	 	 Constraint.swap (a,b) c)

    fun support (Constr(c)) = Constraint.support c
      | support (IOConstr((bs,psi,m,n), c)) = 
	(Lst.minus ((T.support n) @ (A.support psi) @ (T.support m)) bs)
	@ (Constraint.support c)

    fun fresh x c = not $ Lst.member x (support c)

    val new = P.new
    val newBasedOn = P.newBasedOn
    val newsBasedOn = P.newsBasedOn

    fun eqData _ = Err.error "TODO: define alpha equivalence"
  end;
  structure KAlpha = NominalAlpha(K)


  fun isTau Act.Tau = true
    | isTau _       = false

  fun isOutput (Act.Output _) = true
    | isOutput _              = false

  fun isInput (Act.Input _) = true
    | isInput _             = false


  val agentBinders = Frame.binders o Frame.f

  structure ActAlpha = NominalAlpha(Act);
  structure Residual = StrongSymbolicTransitionResidual(Tr)
  structure ResidualAlpha = NominalAlpha(Residual)

  type symbolic_transition
    = P.psi * Act.action * suspended_constraint * P.psi

  datatype action_type = ANYa | VISa | OUTa | INa | TAUa

  datatype symbolic_rules
    = IN | OUT
    | CASE  of condition
    | RES of name
    | PARLEFT
    | PARRIGHT
    | COMLEFT
    | COMRIGHT
    | REPCOM
    | REPI
    | INVOCATION

  fun abstractP ns p = List.foldr P.Restriction p ns

  fun abstractK ns (Constr(c)) = Constr(Constraint.abstract ns c)
    | abstractK ns (IOConstr((bs,psi,m,n), c)) = 
	IOConstr((ns@bs,psi,m,n), Constraint.abstract ns c)

  fun addCond phi (Constr(c))      = Constr(      Constraint.addCond phi c)
    | addCond phi (IOConstr(io,c)) = IOConstr(io, Constraint.addCond phi c)

  fun addFrame fr (Constr(c)) = Constr(Constraint.addFrame fr c)
    | addFrame (cs,psi') (IOConstr(io as (bs,_,_,_),c)) = 
      case KAlpha.makeFresh bs (IOConstr(io,[])) cs of
	  IOConstr((bs,psi,m,n),_) =>
	  IOConstr((cs@bs, I.compose (psi',psi), m,n), 
	 	   Constraint.addFrame (cs,psi') c)
	|_ =>  Err.undefined ()

  fun swapPremises2 ([a, b], r, d) = ([b, a], r, d)
    | swapPremises2 _ = Err.undefined ()

  structure DT =
  struct
    type source  = (P.psi * action_type)
    type premise = symbolic_transition
    type rule    = symbolic_rules
    type context = SI.ClEnv.env

    fun inferIN (P.Input _, ANYa) = SOME ([], IN)
      | inferIN (P.Input _, VISa) = SOME ([], IN)
      | inferIN (P.Input _, INa)  = SOME ([], IN)
      | inferIN _ = NONE

    fun inferOUT (P.Output _, ANYa) = SOME ([], OUT)
      | inferOUT (P.Output _, VISa) = SOME ([], OUT)
      | inferOUT (P.Output _, OUTa) = SOME ([], OUT)
      | inferOUT _ = NONE

    fun inferRES (P.Restriction (a,p),ac) = SOME ([ (p,ac) ], RES a)
      | inferRES _ = NONE

    fun inferREPI e (P.Replication(p),ac) =
        if guarded e p 
	then SOME ([(p,ac)], REPI)
        else Err.error "Unguarded process under !."
      | inferREPI _ _ = NONE

    fun inferREPCOM e (P.Replication(p), ac) =
        if ac <> TAUa andalso ac <> ANYa then NONE
	else if guarded e p
        then SOME ([(p,INa),(p,OUTa)], REPCOM)
        else Err.error "Unguarded process under !."
      | inferREPCOM _ _ = NONE

    fun inferPARs (P.Parallel (p,q),ac)  =
        [ ([(p,ac)], PARLEFT), 
	  ([(q,ac)], PARRIGHT) ]
      | inferPARs _ = []

    fun inferCOMs (P.Parallel (p,q), ac) =
        if ac <> TAUa andalso ac <> ANYa then []
	else [([ (p,OUTa),(q,INa) ], COMLEFT), 
	      ([ (p,INa),(q,OUTa) ], COMRIGHT)]
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
                            (fn (cl as (a, xvec, p)) =>
                                (List.length xvec = List.length mvec) andalso
                                guarded e p andalso
                                (Cl.support cl = [])
                            ) clauses
        in
            case valid of
                [] => []
              | _  => map (fn p => ([ (p,ac) ], INVOCATION)) $
                          map (fn (a,xvec,p) =>
                                  P.subst p (Lst.zip xvec mvec)) valid
        end
      | inferINVOCATIONs _ _ = []


    fun infer e a =
    let
      val rules = [ inferOUT, inferIN, inferRES, inferREPI e, inferREPCOM e ]
      val r = (inferPARs a) @ (inferCASEs e a) @ (inferINVOCATIONs e a) @ (inferCOMs a)
      val s = rules |> map (fn rule => rule a) |> Opt.filterSome
    in
      r @ s
    end

    (* TODO: add a wellformedness condition before simulating *)

    fun eval_axiom e (IN, (ip as (P.Input (m, xs, _, p)),_)) =
        (* y # psi, m, p, x   *)
        let
          val y = P.new (xs @ (T.support m) @ (P.support p))
        in
          SOME ( ip, Act.Input (SI.var y, xs), IOConstr(([], I.unit, m, SI.var y),[]), p)
        end

      | eval_axiom e (OUT, (ip as (P.Output (m, ns, p)),_)) =
        (* y # psi, m, p, ns    *)
        let val y = (P.new ((TL.support ns) @ (T.support m) @ (P.support p)))
        in SOME ( ip, Act.Output (SI.var y, [], ns), IOConstr(([], I.unit, m, SI.var y),[]), p)
        end
      | eval_axiom _ _ = Err.undefined ()


    fun switchSubj (alpha, c) name =
    let
      val alpha' =
        case alpha of
             Act.Output (_, avec, ns) => Act.Output (name, avec, ns)
           | Act.Input  (_, xs)       => Act.Input  (name, xs)
           | _ => Err.error "An undefined case in Simulator.switchSubj 1"
      val c' =
        case c of
             (IOConstr((avec, psi, ms, y),cs)) =>
	      IOConstr((avec, psi, ms, name),cs)
           | _ => Err.error "An undefined case in Simulator.switchSubj 2"
    in
      (alpha', c')
    end



    fun evalPAR ([(iP, alpha, c, dP)], pq as (P.Parallel (p, q))) =
        let
          fun permuteL swap pi l = Lst.foldl swap l pi

          (* bn(alpha) # Q *)
          val pi = ResidualAlpha.freshNames (Act.bn alpha) $ 
                   (T.support (Act.subj alpha))@(P.support q)
          val dP = PAlpha.permute pi dP
          val alpha = case alpha of
                           Act.Tau => Act.Tau
                         | Act.Output (m,avec,ns) =>
                             Act.Output(m, permuteL L.swap pi avec,
                                     permuteL TL.swap pi ns)
                         | Act.Input (m,xs) => Act.Input(m,
				     permuteL L.swap pi xs)

          val bqvec' = Frame.binders (Frame.f q)
          val pi = FrameAlpha.freshNames bqvec' (P.support p)
          val q = PAlpha.permute pi q
          val fQ = Frame.f q
          val bqvec = Frame.binders fQ
          val psiQ = Frame.assertion fQ
        in
          SOME (pq, alpha, addFrame (bqvec,psiQ) c, P.Parallel (dP,q))
        end
      | evalPAR _ = Err.undefined ()


    fun evalCOM ([(iP, oP as Act.Output(_,avec,_), (IOConstr(ioP as (bpvec, psiP, _, _),cp)), dP),
                  (iQ, Act.Input (z, xs),          (IOConstr(ioQ as (bqvec, psiQ, _, _),cq)), dQ)]
                  ,_,
                  (oPQ,ANYa)) sym =
	let
      (* avec # Q *)
      val (avec,ns, dP) =
        case ResidualAlpha.makeFresh avec (oP, dP) (P.support iQ)
         of (Act.Output(_,avec,ns),dp) => (avec,ns,dp)
          | _ => Err.undefined ()

      val pq' = (if sym then Tpl.swap else id) (dP, P.subst dQ (Lst.zip xs ns))
      val pq = abstractP avec (P.Parallel pq')
      val c =
	case KAlpha.makeFresh bpvec  (IOConstr(ioP,[])) (bqvec @ (P.support iQ)) of
            IOConstr((bvec1, psiP, m, _),_) =>
        (case KAlpha.makeFresh bqvec (IOConstr(ioQ,[])) (bpvec @ (P.support iP)) of
            IOConstr((bvec2, psiQ, n, _),_) => 
	    (bvec1 @ bvec2, psiP </I.compose/> psiQ, [I.chaneq (m, n)])
          | _ => Err.undefined ())
          | _ => Err.undefined ()
    in
      SOME (oPQ, Act.Tau,
        Constr(c :: Constraint.addFrame (bqvec, psiQ) cp 
                  @ Constraint.addFrame (bpvec, psiP) cq),
          pq)
    end
      | evalCOM _ _ = Err.undefined ()


    fun evalREPCOM ([(p1, alpha1 as Act.Output (y, avec, ns),
                            (IOConstr(c1 as (bvec1, _, _, _),cs1)), dP1),
                     (p2, Act.Input (z, xs),
                            (IOConstr(c2 as (bvec2, _, _, _),cs2)), dP2)],
                    REPCOM,
                    (p,ANYa)) sym =
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
          | _ => Err.undefined ())
          | _ => Err.undefined ()
      val (xs,dP2) =
        case ResidualAlpha.makeFresh xs (Act.Input(z,xs), dP2) (P.support p) of
	    (Act.Input(_,xs), dP2) => (xs,dP2)
          | _ => Err.undefined ()
      val dP = abstractP avec $ P.Parallel $ 
		sw (dP1, P.subst (P.Parallel (dP2, p)) (Lst.zip xs ns))
    in
        SOME (p, Act.Tau, c, dP)
    end
      | evalREPCOM _ _ = Err.undefined ()


    fun eval e (premises as [(iP, alpha, c, dP)], PARLEFT,  (P.Parallel (p, q),_)) =
        evalPAR (premises, P.Parallel (p, q))

      | eval e (premises as [(iQ, alpha, c, dQ)], PARRIGHT, (P.Parallel (p, q),_)) =
        Opt.some
            (fn (P.Parallel(q,p), alpha, c, P.Parallel(dq,dp)) =>
                (P.Parallel(p,q), alpha, c, P.Parallel(dp,dq))
              | _ => Err.error "Impossible case in Simulator.eval PAR RIGHT")
            (evalPAR (premises, (P.Parallel (q, p))))

      | eval e (r as ([(_,Act.Output(_,_,ns),_,_), (_,Act.Input(_,xs),_,_)], COMLEFT, (oPQ, ANYa))) = 
        if List.length ns <> List.length xs then NONE else evalCOM r false

      | eval e (_, COMLEFT, _) = NONE

      | eval e (r as ([(_,Act.Input(_,xs),_,_), (_,Act.Output(_,_,ns),_,_)], COMRIGHT, (oPQ, ANYa))) = 
        if List.length ns <> List.length xs then NONE else evalCOM (swapPremises2 r) true
      | eval e (_, COMRIGHT, _) = NONE

      | eval e ([(iP, alpha, c, dP)], RES a, (cP as (P.Restriction (_, p)),_)) =
        if isTau alpha orelse Act.fresh a alpha then
            SOME (cP, alpha, abstractK [a] c, P.Restriction(a,dP)) (* SCOPE *)
        else if not $ T.fresh a (Act.subj alpha)
	then let val (alpha, c) = switchSubj (alpha, c) $
				  SI.var $ L.newBasedOn a (a :: K.support c)
             in SOME (cP, alpha, abstractK [a] c, P.Restriction(a,dP))
	     end
	else (case alpha of 	(* OPEN *)
		  Act.Output (y, a_s, ns) =>
		  if Lst.member a (TL.support ns)
		  then SOME (cP, Act.Output (y, (a :: a_s), ns), abstractK [a] c, dP)
		  else NONE
		|_=>NONE) 	(* What to do if a is an input variable? *)
      | eval e (_, RES _, _) = NONE

      (* TODO: clear this with Magnus *)
      | eval e ([(iP, alpha, c, dP)], CASE cond, (cases,_)) =
        let
            val sbj = if isTau alpha then [] else T.support $ Act.subj alpha
            val n = L.new (sbj @ C.support cond @ K.support c)
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

      | eval _ _ = Err.error "Unhandled case in Simulator.eval"

  end; (* END : DT *)

  structure D = DerivationTree(DT)


  fun advance (IOConstr((bs,psi,m,n), c)) = (bs, psi, [I.chaneq(m, n)])::c
    | advance (Constr(c)) = c


  fun reduceA e p ac =
  let
    val tree = D.eval_all e (p,ac)
    val tr  = map (fn (D.EInf (_,_,conclusion)) => conclusion) tree
    val tr' = map (fn (p, alpha, c, p') => (p,alpha, advance c, p')) tr
  in
    tr'
  end

  fun reduce e p = reduceA e p ANYa

  fun debugTree p =
    D.eval_all ClEnv.empty p

                    (*
  fun valid_trees tree =
    List.filter
        (fn (D.EInf (_,_,(psi,iP,alpha,constraint,dP)))
                => Either.either
                    (const false)
                    (const true) $ solve $ advance constraint) tree


  fun reduce e agent =
  let
    val t = D.eval_all e (I.unit, agent)
    val valid = valid_trees t
    val agents = map (fn (D.EInf (_,_,(_,_,_,_,p))) => p) valid
  in
    agents
  end

  fun solve_transitions tree =
    List.partition (fn (_,_,_,RIGHT _,_) => true | _ => false) $
    map (fn (D.EInf (_,_,(psi,iP,alpha,sc,dP))) =>
            let val constraint = advance sc in
            (psi, alpha, constraint, solve constraint, dP) end) tree

  fun symbolic_reduce e agent =
    solve_transitions $ D.eval_all e (I.unit, agent)

  fun symbolic_reduce_psi e psi agent =
    solve_transitions $ D.eval_all e (psi, agent)

  *)

end;
end;

