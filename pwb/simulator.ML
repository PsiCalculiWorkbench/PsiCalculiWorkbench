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
    | Output   of Inst.name * Inst.name list * Inst.term
    | Input    of Inst.name * Inst.name
    | BrOutput of Inst.name * Inst.name list * Inst.term
    | BrInput  of Inst.name * Inst.name

  val subj : action -> Inst.name
  val obj  : action -> Inst.term
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
    | Output   of Inst.name * Inst.name list * Inst.term
    | Input    of Inst.name * Inst.name
    | BrOutput of Inst.name * Inst.name list * Inst.term
    | BrInput  of Inst.name * Inst.name

  fun subj (Output (t, _, _))   = t
    | subj (Input  (t, _))      = t
    | subj (BrOutput (t, _, _)) = t
    | subj (BrInput  (t, _))    = t
    | subj _                    = Err.undefined ()

  fun obj (Output (_, _, n))   = n
    | obj (BrOutput (_, _, n)) = n
    | obj _                    = Err.undefined ()
    (* | obj (Input  (_, x))    = x *)

  fun bn (Output (_, ns, _))   = ns
    | bn (Input  (_, n))       = [n]
    | bn (BrOutput (_, ns, _)) = ns
    | bn (BrInput  (_, n))     = [n]
    | bn  Tau                  = []


  structure Nom = Nominal(struct
    type atom = Inst.name
    type data = action


    structure T = Inst.Term
    structure C = Inst.Cond
    structure A = Inst.Assr
    structure L = NominalNameList(T)


    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = StrongAction fun eq _ = true end


    val atomSort = T.atomSort
    fun dataSort _ = DataSort.StrongAction

    val new = T.new
    val newBasedOn = T.newBasedOn


    fun swap _ Tau = Tau
      | swap ab (Output (subj, avec, obj)) =
        Output (T.swapAtom ab subj, L.swap ab avec, T.swap ab obj)
      | swap (a,b) (Input (subj, x)) =
        Input (T.swapAtom (a,b) subj, T.swapAtom (a,b) x)
      | swap ab (BrOutput (subj, avec, obj)) =
        BrOutput (T.swapAtom ab subj, L.swap ab avec, T.swap ab obj)
      | swap (a,b) (BrInput (subj, x)) =
        BrInput (T.swapAtom (a,b) subj, T.swapAtom (a,b) x)

    fun support (Output (m, avec, n)) =
        m ::(Lst.minus (T.support n) avec)
      | support (Input  (m, _)) = [m]
      | support (BrOutput (m, avec, n)) =
        m :: (Lst.minus (T.support n) avec)
      | support (BrInput  (m, _)) = [m]
      | support Tau = []

    fun eq aEq (a,b) = Err.error "TODO: define alpha equivalence"
  end)
  open Nom
end;

signature SYMBOLIC_TRANSITION_CONSTRAINT =
sig
  structure Inst : PSI_INSTANCE

  (* Constraints used in the operational semantics *)
  datatype constraint = Atomic      of Inst.assertion * Inst.condition
		      | Conjunction of constraint list
		      | Exists      of Inst.name * Inst.name * constraint
		      | Restriction of (Inst.name list) * constraint

  include NOMINAL
    where type data = constraint
    where type atom = Inst.name
    sharing AtomSort = Inst.Sort

  val subst :   constraint -> (Inst.name * Inst.term) list -> constraint

  (* Add restrictions to a constraint. 
   * Defined modulo semantic equivalence. *)
  val restrict: constraint -> Inst.name list -> constraint

  (* Compose two constraints with logical and. 
   * Defined modulo semantic equivalence. *)
  val compose:  constraint -> constraint -> constraint

  (* Rename bound names in the constraint to avoid clashes *)
  val freshen:  constraint -> Inst.name list -> constraint
end;


functor SymbolicOSConstraint(I: PSI_INSTANCE): SYMBOLIC_TRANSITION_CONSTRAINT =
struct
  structure Inst = I
  structure T = I.Term

  datatype constraint = Atomic      of Inst.assertion * Inst.condition
		      | Conjunction of constraint list
		      | Exists      of Inst.name * Inst.name * constraint
		      | Restriction of (Inst.name list) * constraint

  structure ConstraintNom = Nominal(
  struct
    type atom = Inst.name
    type data = constraint

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = STConstraint fun eq _ = true end

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.STConstraint

    structure L = NominalNameList(T)

    fun swap (a,b) (Atomic (psi,phi)) = 
	     Atomic (I.Assr.swap (a,b) psi, I.Cond.swap (a,b) phi)
      | swap (a,b) (Conjunction cl) = 
	     Conjunction (List.map (swap (a,b)) cl)
      | swap (a,b) (Exists(a',b',c)) = 
	     Exists (T.swapAtom (a,b) a', T.swapAtom (a,b) b',swap (a,b) c)
      | swap (a,b) (Restriction(nl,c)) =
	     Restriction(L.swap (a,b) nl, swap (a,b) c)

    fun support (Atomic (psi,phi))  = (I.Assr.support psi)@(I.Cond.support phi)
      | support (Conjunction cl)    = Lst.flatmapmix support cl
      | support (Exists(a,b,c))     = Lst.minus (b::(support c)) [a]
      | support (Restriction(nl,c)) = Lst.minus (support c) nl

    val new = I.Term.new
    val newBasedOn = I.Term.newBasedOn

    fun eq _ _ = Err.undefined ()
  end)

  open ConstraintNom
  structure NA = NominalAlpha(ConstraintNom)
  structure NN = NominalAlpha(NominalAtom(ConstraintNom))

  fun freshen (Atomic (psi,phi)) avec = 
               Atomic (psi,phi)
    | freshen (Conjunction cl) avec = 
               Conjunction (List.map((Tpl.flip freshen) avec) cl)
    | freshen (Exists(a,b,c)) avec = 
      NA.makeFresh [a] (Exists (a, b,freshen c avec)) avec
    | freshen (Restriction(nl,c)) avec = 
      NA.makeFresh nl (Restriction(nl, freshen c avec)) avec

  fun subst constr sigma =
      let
	  val sigmaNames = Lst.flatmapmix (fn (a,b) => a::(I.Term.support b)) sigma
	  fun subs sigma (Atomic (psi,phi)) = 
	     Atomic (I.substA sigma psi, I.substC sigma phi)
	    | subs sigma (Conjunction cl)    = Conjunction (List.map (subs sigma) cl)
	    | subs sigma (Exists(a,b,c))     = Exists (a, b,subs sigma c)
	    | subs sigma (Restriction(nl,c)) = Restriction(nl, subs sigma c)
    (* avec # sigma *)
    in
      subs sigma (freshen constr sigmaNames)
    end

    fun restrict (Restriction(nl,c)) l = Restriction(l@nl,c)
      | restrict c l = Restriction(l,c)

    fun compose (Conjunction(cl)) (Conjunction(cl')) = Conjunction(cl@cl')
      | compose c (Conjunction(cl))                  = Conjunction(c::cl)
      | compose c c'                                 = Conjunction(c::[c'])
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

  fun guarded' e v repl Nil                     = true
    | guarded' e v repl (Output _)              = true
    | guarded' e v repl (Input _)               = true
    | guarded' e v repl (BrOutput _)            = not repl
    | guarded' e v repl (BrInput _)             = true
    | guarded' e v repl (Case cs)               = guarded_case e v repl cs
    | guarded' e v repl (Restriction (_, p))    = guarded' e v repl p
    | guarded' e v repl (Parallel (p, q))       =        
      (guarded' e v repl p) andalso (guarded' e v repl q)
    | guarded' e v repl (Replication p)         = guarded' e v true p
    | guarded' e v repl (Assertion _)           = false
    | guarded' e v repl (Invocation (a,mvec))   =
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
          not visited andalso Lst.all (guarded' e ((a,arity)::v) repl o clauseP) ps
        end
  and guarded_case e v repl cs = Lst.all (guarded' e v repl o Tpl.snd) cs

  fun guarded e p = guarded' e [] false p
end
end;



signature STRONG_SYMBOLIC_TRANSITION =
sig
  structure Psi        : PSI
  structure Act        : PSI_STRONG_ACTION
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT

  type transition
    = Psi.Inst.assertion
        * Psi.psi * Act.action * Constraint.constraint * Psi.psi

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

  datatype transitiontype = BCAST | BREC | SYMM
  type channeleq = (transitiontype * 
                    (Tr.Psi.Inst.name list) * 
                    Tr.Psi.Inst.assertion * 
                    Tr.Psi.Inst.term * 
                    Tr.Psi.Inst.term) option
  type suspended_constraint = channeleq * Tr.Constraint.constraint
  type residual = Tr.Act.action * suspended_constraint * Tr.Psi.psi

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
    = Psi.Inst.assertion
        * Psi.psi * Act.action * Constraint.constraint * Psi.psi

end;


functor StrongSymbolicTransitionResidual(Tr : STRONG_SYMBOLIC_TRANSITION):
    STRONG_SYMBOLIC_TRANSITION_RESIDUAL =
struct
  structure Tr = Tr
  structure T = Tr.Psi.Inst.Term

  datatype transitiontype = BCAST | BREC | SYMM
  type channeleq = (transitiontype * 
                    (Tr.Psi.Inst.name list) * 
                    Tr.Psi.Inst.assertion * 
                    Tr.Psi.Inst.term * 
                    Tr.Psi.Inst.term) option
  type suspended_constraint = channeleq * Tr.Constraint.constraint
  type residual = Tr.Act.action * suspended_constraint * Tr.Psi.psi

  structure Nom = Nominal(struct
    type atom = T.atom
    type data = residual

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = SSTResidual fun eq _ = true end

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.SSTResidual

    fun swap pi (alpha, (NONE,constr), p) = 
        (Tr.Act.swap pi alpha, 
         (NONE,Tr.Constraint.swap pi constr), 
         Tr.Psi.swap pi p)
      | swap pi (alpha, (SOME (tt,avec,psi,m,n), constr), p) = 
        (Tr.Act.swap pi alpha, 
         (SOME (tt,
               map (T.swapAtom pi) avec,
               Tr.Psi.Inst.Assr.swap pi psi,
               T.swap pi m,
               T.swap pi n),
          Tr.Constraint.swap pi constr),  
         Tr.Psi.swap pi p)

    fun support (alpha, (che,constr), p) = 
      let
        val cheSupp = case che of NONE => []
        | (SOME (_,avec,psi,m,n)) => 
           Lst.minus ((Tr.Psi.Inst.Assr.support psi) @ 
                      (T.support m)@ (T.support n)) avec
      in
        (Tr.Act.support alpha)@
        cheSupp@
        (Tr.Constraint.support constr)@
        (Tr.Psi.support p)
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
  structure Tr         : STRONG_SYMBOLIC_TRANSITION
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  structure ClEnv      : PSI_CLAUSE_ENVIRONMENT

  val reduce :
    ClEnv.env -> Psi.Inst.assertion -> Psi.psi -> Tr.transition list

  sharing Psi = ClEnv.Cl.Psi = Tr.Psi
  sharing Psi.Inst = Constraint.Inst = ClEnv.Cl.Psi.Inst = Tr.Psi.Inst
  sharing Constraint = Tr.Constraint
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
  structure N          = NominalName(T)
  structure PAlpha     = NominalAlpha(P)
  structure FrameAlpha = NominalAlpha(Frame)
  structure ActAlpha   = NominalAlpha(Act);
  structure Res        = StrongSymbolicTransitionResidual(Tr)
  structure ResAlpha   = NominalAlpha(Res)

  type name      = I.name
  type term      = I.term
  type assertion = I.assertion
  type condition = I.condition

  structure G = PsiGuarded(SI)
  val guarded = G.guarded

  structure K : NOMINAL =
  struct
    type atom = name
    type data = Res.suspended_constraint

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = KSort fun eq _ = true end

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.KSort

    val swapAtom = P.swapAtom

    fun swap (a,b) (NONE, constr) = (NONE, Constraint.swap (a,b) constr)
      | swap (a,b) (SOME (tt, avec, psi, m, n), constr) = 
        (SOME (tt, 
	       L.swap (a,b) avec,
	       A.swap (a,b) psi,
	       T.swap (a,b) m,
	       T.swap (a,b) n), 
         Constraint.swap (a,b) constr)

    fun support (NONE, constr) = Constraint.support constr
      | support (SOME (tt, avec, psi, m, n), constr) = 
       (Constraint.support constr)@
       Lst.minus ((T.support n) @ (A.support psi) @ (T.support m)) avec

    fun fresh x c = not $ Lst.member x (support c)

    val new = P.new
    val newBasedOn = P.newBasedOn

    fun eqData _ = Err.error "TODO: define alpha equivalence"
  end;
  structure KAlpha = NominalAlpha(K)

  fun isTau Act.Tau = true
    | isTau _       = false

  fun isOutput (Act.Output _)   = true
    | isOutput (Act.BrOutput _) = true
    | isOutput _                = false

  val agentBinders = Frame.binders o Frame.f

  type psi_source
    = assertion * P.psi

  type symbolic_transition
    = assertion * P.psi * Act.action * Res.suspended_constraint * P.psi

  datatype symbolic_rules
    = IN | OUT | BRIN | BROUT
    | CASE  of condition
    | PAR   of (name list, name list) either
    | SCOPE of name
    | OPEN  of name
    | BROPEN  of name
    | BRCLOSE  of name
    | COM1
    | COM2
    | BRCOM1
    | BRCOM2
    | BRMERGE
    | REPCOM
    | REPI
    | INVOCATION


  fun abstractVec _ [] p = p
    | abstractVec abs (n::ns) p = abstractVec abs ns (abs n p)

  fun abstractKVec ns (NONE,c) = (NONE, Constraint.restrict c ns)
    | abstractKVec ns (SOME (b, avec, a, t1, t2), c) =
      (SOME (b, ns@avec,a,t1,t2), Constraint.restrict c ns)

  val abstractP = Tpl.curry P.Restriction

  fun swapPremises2 ([a, b], r, d) = ([b, a], r, d)
    | swapPremises2 _ = Err.undefined ()

  fun restrictAtomic (nl,psi,phi) = 
      Constraint.Restriction(nl,Constraint.Atomic(psi,phi))

  fun castEq (Res.SYMM,  avec, psi, m, y) = restrictAtomic (avec, psi, I.chaneq(m, y))
    | castEq (Res.BCAST, avec, psi, m, y) = restrictAtomic (avec, psi, I.brTransmit(m, y))
    | castEq (Res.BREC,  avec, psi, m, y) = restrictAtomic (avec, psi, I.brReceive(m, y)) 

  fun channelEq (tt,psi,m,n) = (SOME (tt,[],psi,m,n), Constraint.Conjunction [])

  val noConstraint = (NONE, Constraint.Conjunction [])

  structure DT =
  struct
    type source  = psi_source
    type premise = symbolic_transition
    type rule    = symbolic_rules
    type context = SI.ClEnv.env

    fun inferIN _ (psi, p)  =
      case p of
           P.Input _ => [SOME ([], IN)]
         | _ => [NONE]

    fun inferBRIN _ (psi, p)  =
      case p of
           P.BrInput _ => [SOME ([], BRIN)]
         | _ => [NONE]

    fun inferOUT _ (psi, p)  =
      case p of
           P.Output _ => [SOME ([], OUT)]
         | _ => [NONE]

    fun inferBROUT _ (psi, p)  =
      case p of
           P.BrOutput _ => [SOME ([], BROUT)]
         | _ => [NONE]


    fun inferCASEs e (psi, caseP) =
      case caseP of
           P.Case cs =>
            map (fn (phi, p) =>
                    if guarded e p then
                      SOME ([(psi, p)], CASE phi)
                    else
                      NONE) cs
         | _ => [NONE]



    fun comFresh psi p q =
    let
      val pfr   = Frame.f p
      val bpvec = Frame.binders pfr
      (* bpvec # psi, bqvec, q *)
      val bqvec = Frame.binders (Frame.f q)
      val qsup  = P.support q
      val psisup = A.support psi

      val pi = PAlpha.freshNames bpvec (psisup @ bqvec @ qsup)

      val p = PAlpha.permute pi p
      val pfr = FrameAlpha.permute pi pfr
    in
      (p,pfr)
    end

    fun inferCOMs comrulenames (psi, pq) =
      case pq of
           P.Parallel (p,q) =>
           let
             val (p,pfr) = comFresh psi p q
             val (q,qfr) = comFresh psi q p

             val psiQ = psi </I.compose/> Frame.assertion pfr
             val psiP = psi </I.compose/> Frame.assertion qfr
           in
             comrulenames |> map (fn rulename => 
				     SOME ([ (psiQ, p), (psiP, q) ], rulename))
           end
         | _ => [NONE]

    fun inferCOM     _ = inferCOMs [COM1, COM2]
    fun inferBRCOM   _ = inferCOMs [BRCOM1, BRCOM2]
    fun inferBRMERGE _ = inferCOMs [BRMERGE]

    fun inferREPCOM e (psi, bangP) =
      case bangP of
           P.Replication p =>
           if guarded e p then
             let
               val b1vec = agentBinders p
               val p1 = PAlpha.makeFresh b1vec p $
                            (A.support psi) @ (P.support bangP)

               val b1vec = agentBinders p1
               val b2vec = agentBinders p
               val p2 = PAlpha.makeFresh b2vec p $
                            (A.support psi) @ (P.support bangP) @ b1vec
             in
               [ SOME ([(psi, p1), (psi, p2)], REPCOM) ]
             end
           else [NONE]
         | _ => [NONE]


    fun inferREPI e (psi, bangP) =
      case bangP of
           P.Replication p =>
           if guarded e p then
             [SOME ([ (psi, p) ], REPI)]
           else [NONE]
         | _ => [NONE]


    fun inferPAR _ (psi, parP)  =
    let
      fun par p q =
      let
        (* bqvec # psi, p, alpha *)
        val qfr   = Frame.f q
        val bqvec = Frame.binders qfr

        val pi = FrameAlpha.freshNames bqvec
            (A.support psi @ P.support p)

        val psiQ = Frame.assertion (FrameAlpha.permute pi qfr)

        val psiPsiQ = psi </I.compose/> psiQ

        (*
        val fq = Frame.f q
        val bqvec = Frame.binders fq

        (* Frame.f Q = (nu bqvec) Psiq, bqvec # psi, p *)
        val bpvec = Frame.binders $ Frame.f p
        val fq = FrameAlpha.makeFresh bqvec fq $
                            (P.support p) @ (A.support psi) @ bpvec
        val newPsi = I.compose (psi, Frame.assertion fq)
        val bqvec = Frame.binders fq *)
      in
        ((psiPsiQ, p), [])
        (* ((newPsi, p), bqvec) *)
      end
    in
      case parP of
           P.Parallel (p,q) =>
           let
             val (parL, bqvec) = par p q
             val (parR, bpvec) = par q p
           in
            [ SOME ([parL], PAR (LEFT bqvec)), SOME ([parR], PAR (RIGHT bpvec)) ]
           end
         | _ => [NONE]
    end

    fun inferSCOPE _ (psi, resP)  =
      case resP of
           P.Restriction (a,p) =>
                if (A.fresh a psi)
                    then [SOME ([(psi, p)], (SCOPE a))]
                    else
                      let val nn = P.newBasedOn a (A.support psi)
                      in [SOME ([(psi, P.swap (a,nn) p)], (SCOPE nn))]
                      end
         | _ => [NONE]

    fun inferOPENs rulename (psi, resP) =
      case resP of
           P.Restriction (a,p) =>
            if (A.fresh a psi)
                then [SOME ([(psi, p)], OPEN a)]
                else
                  let val nn = P.newBasedOn a (A.support psi)
                  in [SOME ([(psi, P.swap (a,nn) p)], (rulename nn))]
                  end
         | _ => [NONE]

    fun inferOPEN    _ = inferOPENs OPEN
    fun inferBROPEN  _ = inferOPENs BROPEN
    fun inferBRCLOSE _ = inferOPENs BRCLOSE

    fun inferINVOCATION e (psi, invP) =
      case invP of
           P.Invocation (a, mvec) =>
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
                  [] => [NONE]
                | _  => map (fn p => SOME ([(psi, p)], INVOCATION)) $
                    map (fn (a,xvec,p) =>
                            P.subst p (Lst.zip xvec mvec)) valid
           end
         | _ => [NONE]


    fun infer e a =
    let
      val rules   = [inferOPEN, inferBROPEN, inferBRCLOSE, inferSCOPE, 
		     inferOUT,  inferIN,     inferBROUT,   inferBRIN,
		     inferPAR,  inferCASEs,  inferREPI,    inferINVOCATION,
		     inferCOM,  inferREPCOM, inferBRCOM,   inferBRMERGE]
      val forest = Lst.flatmap (fn rule => rule e a) rules
    in
      Opt.filterSome $ Lst.flatmap (fn rule => rule e a) rules
    end



    (* TODO: add a wellformedness condition before simulating *)

    fun eval_axiom e (IN,  (psi, ip as (P.Input (m, [x], _, p)))) =
        (* y # psi, m, p, x   *)
        let
          val y = P.new (* x *)
            (x :: (A.support psi) @ (T.support m) @ (P.support p))
        in
          SOME ( psi, ip, Act.Input (y, x), 
                 channelEq (Res.SYMM, psi, m, SI.var y), p)
        end

      | eval_axiom e (OUT, (psi, ip as (P.Output (m, n, p)))) =
        (* y # psi, m, p, n    *)
        let val y = (P.new
            ((T.support n) @ (A.support psi) @ (T.support m) @ (P.support p)))
        in SOME ( psi, ip, Act.Output (y, [], n), 
                  channelEq (Res.SYMM, psi, m, SI.var y), p)
        end

      | eval_axiom e (BRIN,  (psi, ip as (P.BrInput (m, [x], _, p)))) = 
        (* y # psi, m, p, x   *)
        let
          val y = P.newBasedOn x
            (x :: (A.support psi) @ (T.support m) @ (P.support p))
        in
          SOME ( psi, ip, Act.BrInput (y, x), 
                 channelEq (Res.BREC, psi, SI.var y, m), p)
        end
      | eval_axiom e (BROUT, (psi, ip as (P.BrOutput (m, n, p)))) =
        (* y # psi, m, p, n    *)
        let val y = (P.new
            ((T.support n) @ (A.support psi) @ (T.support m) @ (P.support p)))
        in SOME ( psi, ip, Act.BrOutput (y, [], n), 
                  channelEq (Res.BCAST, psi, m, SI.var y), p)
        end
      | eval_axiom _ _ = Err.undefined ()


    fun switchSubj (Act.Output (_,    avec, n),   (SOME (Res.SYMM, bvec, psi, m, _),cs)) name =
		   (Act.Output (name, avec, n),   (SOME (Res.SYMM, bvec, psi, m, SI.var name),cs))
      | switchSubj (Act.Input (_,    x),          (SOME (Res.SYMM, avec, psi, m, _),cs)) name =
                   (Act.Input (name, x),          (SOME (Res.SYMM, avec, psi, m, SI.var name),cs))
      | switchSubj (Act.BrOutput (oldn, avec, n), (SOME (Res.BCAST, bvec, psi, m, _),cs)) name =
		   (Act.BrOutput (name, avec, n), (SOME (Res.BCAST, bvec, psi, m, SI.var name),cs))
      | switchSubj (Act.BrInput (oldn, x),        (SOME (Res.BREC, avec, psi, _, m),cs)) name =
                   (Act.BrInput (name, x),        (SOME (Res.BREC, avec, psi, SI.var name, m),cs))
      | switchSubj (Act.Tau,_) _ = Err.error "Simulator.switchSubj called on Tau"
      | switchSubj _ _           = Err.error "An undefined case in Simulator.switchSubj"



    fun evalPAR ([(psiQ, iP, alpha, c, dP)],
                  (psi, (pq as (P.Parallel (p, q))))) bqvec =
        let
          (*
          fun obj_support (AOutput (_,_,n)) = T.support n
            | obj_support _ = []

          fun m_support ((LEFT (ChannelEq (_,_,m,_)))::_) = T.support m
            | m_support _ = []

          val qSupport = P.support q

            *)
          fun permuteL swap pi l = Lst.foldl swap l pi

          (* bn(alpha) # Q *)
          val pi = ResAlpha.freshNames (Act.bn alpha) (P.support q)
          val dP = PAlpha.permute pi dP
          val alpha = case alpha of
                           Act.Tau => Act.Tau
                         | Act.Output (m,avec,n) =>
                           Act.Output (m, permuteL L.swap pi avec,
                                       permuteL T.swap pi n)
                         | Act.Input (m,x) => 
			   Act.Input (m, hd (permuteL L.swap pi [x]))
                         | Act.BrOutput (m,avec,n) =>
                           Act.BrOutput (m, permuteL L.swap pi avec,
					 permuteL T.swap pi n)
                         | Act.BrInput (m,x) => 
			   Act.BrInput (m, hd (permuteL L.swap pi [x]))

          val bqvec = Frame.binders (Frame.f q) (* XXX: works if (binders o f) is deterministic,
						 * i.e, if psi_Q has the same binders. *)
          val pi = FrameAlpha.freshNames bqvec
                    (A.support psi @ P.support p)
          val q = PAlpha.permute pi q
          val bqvec = Frame.binders (Frame.f q)
        in
          SOME (psi, pq, alpha, abstractKVec bqvec c,
                P.Parallel (dP,q))
          (*
          (* bn(alpha) # Q *)
          ResAlpha.makeFresh (bn alpha) (alpha, dP) qSupport |>
          (fn (alpha, dP) =>
            let
            (* subj(alpha) # Q *)
            (* y, z # psi, bpvec, p, bqvec, q, n, avec *)
            val (alpha, c) =
              if ((isTau alpha) orelse
                        (P.fresh (hd (T.support (subj alpha))) q))
                  then (alpha, c)
                  else
                     let
                       val n = P.new
                         (qSupport @ (A.support psiQ) @ (P.support dP) @
                         (bn alpha) @ (obj_support alpha) @ (m_support c))
                     in switchSubj (alpha, c) (SI.var n) end

            (* bqvec # alpha *)
            val c = abstractKVec bqvec c
            val c = KAlpha.makeFresh bqvec c (Act.support alpha)
          in
            SOME (psi, pq, alpha, c, P.Parallel (dP, q))
          end) *)
        end
      | evalPAR _ _ = Err.undefined ()


    fun evalCOM ([(psiQ, iP, Act.Output (y, avec, n),
                            (SOME (_, bpvec, psiPQ1, mp, _),cp), dP),
                 (psiP, iQ, Act.Input (z, x),
                            (SOME (_, bqvec, psiPQ2, mq, _),cq), dQ)]
                  ,_,
                  (psi, oPQ)) sym =
    let
      (* avec # Q *)
      val (out, _, dP) =
        ResAlpha.makeFresh avec (Act.Output(y,avec,n), noConstraint, dP) (P.support iQ)

      val pq = (if sym then Tpl.swap else id) (dP, P.subst dQ [(x, n)])
      val pq = abstractVec abstractP avec (P.Parallel pq)
    in
      SOME (psi, oPQ, Act.Tau, (NONE,
        Constraint.Conjunction
            [restrictAtomic (bpvec @ bqvec, psiPQ1 </I.compose/> psiPQ2, mp </I.chaneq/> mq),
             Constraint.restrict cp bqvec, Constraint.restrict cq bpvec]), 
          pq)
    end
      | evalCOM _ _ = Err.undefined ()


    fun evalBRCOM ([(psiQ, iP, oldOut as Act.BrOutput (y, avec, _), c1, dP),
                    (psiP, iQ, Act.BrInput (z, x), c2, dQ)]
                   ,_,
                   (psi, oPQ)) sym =
    let
      (* y,avec # Q *)
      val (out as (y,avec,n), oute as (_,bpvec,_,_,_), c1, dP) = 
          case ResAlpha.makeFresh (y::avec) (oldOut, c1, dP) (P.support iQ) of
              ((Act.BrOutput (y, avec, n)), (SOME oute, cp), dP) => 
              ((y, avec, n), oute, cp, dP)
	    | _ => Err.undefined ()
      val (eqq as (_,bqvec,_,_,_),cq) = 
          case K.swap (y,z) c2 of (SOME eqq, cq) => (eqq,cq)
	                        | _ => Err.undefined ()

      val pq = (dP, P.subst dQ [(x, n)]) |> (if sym then Tpl.swap else id)
    in
      SOME (psi, oPQ, Act.BrOutput out,
            (SOME oute,
             Constraint.Conjunction 
                 [Constraint.restrict c1 bqvec, 
                  castEq eqq, 
                  Constraint.restrict cq bpvec]),
            pq)
    end
      | evalBRCOM _ _ = Err.undefined ()


    fun evalBRMERGE ([(psiQ, iP, oldIn1 as Act.BrInput (z1, x1), 
                       (ep as SOME(_,bpvec,_,_,_),cp), dP),
                      (psiP, iQ, oldIn2 as Act.BrInput (z2, x2), c2, dQ)]
                   ,_,
                   (psi, oPQ)) sym =
    let			(* TBD: Freshen z1,x1,z2,x2 for P resp Q *)
      val (eqq as (_,bqvec,_,_,_),cq) =
          case K.swap (z1,z2) c2 of (SOME eqq, cq) => (eqq,cq)
                                  | _ => Err.undefined ()
      val dQ = P.swap (x1, x2) dQ  
    in
      SOME (psi, oPQ, oldIn1,
            (ep,
             Constraint.Conjunction 
                 [Constraint.restrict cp bqvec,
                  castEq eqq,
                  Constraint.restrict cq bpvec]),
            (dP,dQ))
    end
      | evalBRMERGE _ _ = Err.undefined ()

    fun evalREPCOM ([(_, p1, alpha1 as Act.Output (y, avec, n),
                         c1 as (SOME (_, bvec1, _, m, _),cs1), dP1),
                     (_, p2, Act.Input (z, x),
                         c2 as (SOME (_, bvec2, _, mp, _),cs2), dP2)],
                    _,
                    (psi, p)) =
    let
      val (_, _, dP1) =
        ResAlpha.makeFresh avec (alpha1, noConstraint, dP1) (P.support p)
    in
      case KAlpha.makeFresh bvec1 c1 (bvec2 @ (A.support psi) @ (P.support p2)) of
        (SOME (_, bvec1, psi, m, _),cs1) =>
        (case KAlpha.makeFresh bvec2 c2 (bvec1 @ (A.support psi) @ (P.support p1)) of
          (SOME (_, bvec2, psi, mp, _),cs2) =>
          let
            val c = Constraint.Conjunction
                        [restrictAtomic (bvec1 @ bvec2, psi, I.chaneq (m, mp)),
                         Constraint.restrict cs1 bvec2,
                         Constraint.restrict cs2 bvec1]
            in
              ResAlpha.makeFresh [x] (Act.Input(z,x), noConstraint, dP2) (P.support p) |>
              (* x # !P *)
              (fn (Act.Input(z,x), _, dP2) =>
               let
                 val dP = P.Parallel (dP1, P.subst (P.Parallel (dP2, p)) [(x, n)])
                 val dP = abstractVec abstractP avec dP
               in
                 SOME (psi, p, Act.Tau, (NONE,c), dP)
               end
              | _ => Err.undefined ())
            end
            | _ => Err.undefined ())
         | _ => Err.undefined ()
    end
      | evalREPCOM _ = Err.undefined ()


    fun eval e (premises as [(psi1, iP, alpha, c, dP)],
              PAR (LEFT bqvec),
              conclusion as (psi, (pq as (P.Parallel (p, q))))) =
                evalPAR (premises, conclusion) bqvec

      | eval e (premises as [(psi1, iQ, alpha, c, dQ)],
              PAR (RIGHT bpvec),
              (assert, (P.Parallel (p, q)))) =
              Opt.some
                (fn (psi, P.Parallel(q,p), alpha, c, P.Parallel(dq,dp)) =>
                    (psi, P.Parallel(p,q), alpha, c, P.Parallel(dp,dq))
                  | _ => Err.error "Impossible case in Simulator.eval PAR RIGHT")
                (evalPAR (premises, (assert, P.Parallel (q, p))) bpvec)

      | eval e (r as ([(t1 as (_,_,a1,_,_)), (t2 as (_,_,a2,_,_))],
              COM1,
              (psi, oPQ))) =
          (case (a1, a2) of
               (Act.Output _, Act.Input  _) => evalCOM r false
             | _ => NONE)

      | eval e (r as ([(t1 as (_,_,a1,_,_)), (t2 as (_,_,a2,_,_))],
              COM2,
              (psi, oPQ))) =
          (case (a1, a2) of
               (Act.Input _,  Act.Output _) => evalCOM (swapPremises2 r) true
             | _ => NONE)

      | eval e ([(_, iP, alpha, c, dP)],
              SCOPE a,
              (psi, (cP as (P.Restriction (_, p))))) =

          if isTau alpha orelse Act.fresh a alpha then
            SOME (psi, cP, alpha, abstractKVec [a] c, abstractP a dP)
          else if isOutput alpha andalso not $ T.fresh a (Act.obj alpha) then
            NONE
          else let val (alpha, c) = 
		       switchSubj (alpha, c) 
                                  (L.newBasedOn a (a :: (A.support psi)@ K.support c))
               in SOME (psi, cP, alpha, abstractKVec [a] c, abstractP a dP)
               end

      | eval e ([(_, iP, alpha, c, dP)],
              OPEN a,
              (psi, (cP as (P.Restriction (_, p))))) =
        (case alpha of
             Act.Output (y, a_s, n) =>
                  if Lst.member a (T.support n)
                    then SOME (psi, cP, Act.Output (y, (a :: a_s), n),
                            abstractKVec [a] c, dP)
                    else NONE
           | _ => NONE)

      (* TODO: clear this with Magnus *)
      | eval e ([(_, iP, alpha, c, dP)],
              CASE cond,
              (psi, cases)) =
              let
                val sbj = if isTau alpha then [] else [Act.subj alpha]
                val n = L.new (sbj @ C.support cond @ K.support c)
                val (alpha, (cheq,constr)) = 
                    if isTau alpha 
                    then (alpha,c) 
                    else switchSubj (alpha,c) n
              in
                SOME (psi, cases, alpha, 
                      (cheq, (Constraint.compose (Constraint.Atomic(psi, cond)) constr)),
                      dP)
              end

      | eval e ([(_, iP, alpha, c, dP)],
              REPI,
              (psi, p)) =
        SOME (psi, p, alpha, c, P.Parallel (dP, p))

      | eval e (r as ([(_, p1, alpha1, c1, dP1), (_, p2, alpha2, c2, dP2)],
                    REPCOM,
                    (psi, p))) =
        (case (alpha1, alpha2) of
              (Act.Output _, Act.Input _) => evalREPCOM r
            | _ => NONE)

      | eval e ([(p, ps, alpha, c, dP)], INVOCATION, (psi, amvec)) =
        SOME (psi, amvec, alpha, c, dP)
      | eval _ (_,BRMERGE,_) = NONE
      | eval _ (_,BRCOM1,_) = NONE
      | eval _ (_,BRCOM2,_) = NONE
      | eval _ (_,BRCLOSE _,_) = NONE
      | eval _ (_,BROPEN _,_) = NONE
      | eval _ (_,BRIN,_) = NONE
      | eval _ (_,BROUT,_) = NONE

      | eval _ _ = Err.error "Unhandled case in Simulator.eval"

  end; (* END : DT *)

  structure D = DerivationTree(DT)

  fun reduce e psi p =
  let
    val tree = D.eval_all e (psi, p)
    val tr  = map (fn (D.EInf (_,_,conclusion)) => conclusion) tree
    val tr' = map (fn (psi, p, alpha, (NONE,c), p') => (psi,p,alpha, c, p')
                    | (psi, p, alpha, (SOME ec,c), p') => 
		      (psi,p,alpha, Constraint.compose (castEq ec) c, p')) tr
  in
    tr'
  end

  fun debugTree p =
    D.eval_all ClEnv.empty (I.unit, p)

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

