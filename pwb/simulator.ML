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
    | Output of Inst.term * Inst.name list * Inst.term
    | Input  of Inst.term * Inst.name

  val subj : action -> Inst.term
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
    | Output of Inst.term * Inst.name list * Inst.term
    | Input  of Inst.term * Inst.name

  fun subj (Output (t, _, _)) = t
    | subj (Input  (t, _))    = t
    | subj _                  = Err.undefined ()

  fun obj (Output (_, _, n)) = n
    | obj _                   = Err.undefined ()
    (* | obj (Input  (_, x))    = x *)

  fun bn (Output (_, ns, _)) = ns
    | bn (Input  (_, n))     = [n]
    | bn  Tau                = []


  structure Nom = Nominal(struct
    type atom = Inst.name
    type data = action


    structure T = Inst.Term
    structure C = Inst.Cond
    structure A = Inst.Assr
    structure L = NominalNameList(T)


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
        Output (T.swap ab subj, L.swap ab avec, T.swap ab obj)
      | swap (a,b) (Input (subj, x)) =
        Input (T.swap (a,b) subj, T.swapAtom (a,b) x)

    fun support (Output (m, avec, n)) =
        (T.support m) @ (Lst.minus (T.support n) avec)
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
  type atomic     = Inst.name list * Inst.assertion * Inst.condition
  type constraint = atomic list (* conjuct list *)

  include NOMINAL
    where type data = constraint
    where type atom = Inst.name
    sharing AtomSort = Inst.Sort

  val subst : constraint -> (Inst.name * Inst.term) list -> constraint
end;


functor SymbolicOSConstraint(I: PSI_INSTANCE): SYMBOLIC_TRANSITION_CONSTRAINT =
struct
  structure Inst = I
  structure T = I.Term

  type atomic     = Inst.name list * Inst.assertion * Inst.condition
  type constraint = atomic list

  structure AtomicNom = Nominal(
  struct
    type atom = Inst.name
    type data = atomic

    structure AtomSort = T.AtomSort
    structure DataSort = struct datatype sort = STConstraint fun eq _ = true end

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.STConstraint

    structure L = NominalNameList(T)

    fun swap (a,b) (avec, psi, phi) =
      (L.swap (a,b) avec, I.Assr.swap (a,b) psi, I.Cond.swap (a,b) phi)

    fun support (avec, psi, phi) =
      Lst.minus ((I.Assr.support psi) @ (I.Cond.support phi)) avec

    val new = I.Term.new
    val newBasedOn = I.Term.newBasedOn

    fun eq alphaEq ((avec,psi,phi), (avec',psi',phi')) = Err.undefined ()
  end)

  structure ConstraintNom = NominalList(AtomicNom)
  open ConstraintNom
  structure NA = NominalAlpha(AtomicNom)

  fun x |> f = f x

  fun subst' sigma (avec, psi, phi) =
    (* avec # sigma *)
    let
      val sigmaNames = (map Tpl.fst sigma) @
                       (List.concat (map (I.Term.support o Tpl.snd) sigma))
    in
      (NA.makeFresh avec (avec, psi, phi) sigmaNames) |>
      (fn (avec, psi, phi) =>
        (avec, Inst.substA sigma psi, Inst.substC sigma phi))
    end

  fun subst cnstr sigma = map (subst' sigma) cnstr
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

  (* XXX: this name appears in the input and output actions, as a name
   * placeholder in a constraint, and in bisimulation algorithm.
   *)
  val nameOfConstrSort : unit -> Psi.Inst.name

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
    = Psi.Inst.assertion
        * Psi.psi * Act.action * Constraint.constraint * Psi.psi

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

    val atomSort = T.atomSort
    fun dataSort _ = DataSort.SSTResidual

    fun swap pi (alpha, p) = (Tr.Act.swap pi alpha, Tr.Psi.swap pi p)

    fun support (Tr.Act.Tau, p) = Tr.Psi.support p
      | support (alpha,p) =
      let
        val obj = case alpha of
                       Tr.Act.Output (_,_,m) => T.support m
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

  val reduce :
    ClEnv.env -> Psi.Inst.assertion -> Psi.psi -> Tr.transition list


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
  structure N          = NominalName(T)
  structure PAlpha     = NominalAlpha(P)
  structure FrameAlpha = NominalAlpha(Frame)

  type name      = I.name
  type term      = I.term
  type assertion = I.assertion
  type condition = I.condition

  type atomic = Constraint.atomic

  datatype channeleq =
    ChannelEq of (name list * assertion * term * term)
  type suspended_constraint = (channeleq, atomic) either list


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

    fun swap (a,b) constraint =
      map (fn (RIGHT ((avec, psi, cond))) =>
      RIGHT $ (L.swap (a,b) avec,
      A.swap (a, b) psi,
      C.swap (a, b) cond)
      | (LEFT (ChannelEq (avec, psi, m, n))) =>
          LEFT $ ChannelEq (
          L.swap (a,b) avec,
          A.swap (a,b) psi,
          T.swap (a,b) m,
          T.swap (a,b) n)) constraint

    fun support constraint =
      List.concat $
      map (fn RIGHT ((avec, psi, cond)) =>
            Lst.minus ((A.support psi) @ (C.support cond)) avec
            | LEFT (ChannelEq (avec, psi, m, n)) =>
            Lst.minus ((T.support n) @ (A.support psi) @ (T.support m)) avec)
            constraint

    fun fresh x c = not $ Lst.member x (support c)

    val new = P.new
    val newBasedOn = P.newBasedOn

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

  type psi_source
    = assertion * P.psi

  type symbolic_transition
    = assertion * P.psi * Act.action * suspended_constraint * P.psi

  datatype symbolic_rules
    = IN | OUT
    | CASE  of condition
    | PAR   of (name list, name list) either
    | SCOPE of name
    | OPEN  of name
    | COM1
    | COM2
    | REPCOM1
    | REPCOM2
    | REPI
    | INVOCATION


  fun constraintSupport' (LEFT (ChannelEq (avec,psi,t,a))) =
    Lst.minus (T.support a @ (A.support psi @ T.support t)) avec
    | constraintSupport' (RIGHT ((avec,psi,cond))) =
    Lst.minus (A.support psi @ C.support cond) avec

  fun constraintSupport c =
    List.concat $ map constraintSupport' c

  fun abstractVec _ [] p = p
    | abstractVec abs (n::ns) p = abstractVec abs ns (abs n p)

  fun abstractK n c =
      map (fn (RIGHT ((ns, a, c))) =>
               RIGHT $ (n :: ns, a,c)
            | (LEFT (ChannelEq (ns, a, t1, t2))) =>
               LEFT  $ ChannelEq (n :: ns,a,t1,t2)) c

  val abstractP = Tpl.curry P.Restriction

  fun swapPremises2 ([a, b], r, d) = ([b, a], r, d)
    | swapPremises2 _ = Err.undefined ()

  structure DT =
  struct
    type source  = psi_source
    type premise = symbolic_transition
    type rule    = symbolic_rules
    type context = SI.ClEnv.env

    fun inferIN (psi, p)  =
      case p of
           P.Input _ => SOME ([], IN)
         | _ => NONE

    fun inferOUT (psi, p)  =
      case p of
           P.Output _ => SOME ([], OUT)
         | _ => NONE

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

    fun inferCOM (psi, pq) =
      case pq of
           P.Parallel (p,q) =>
           let
             val (p,pfr) = comFresh psi p q
             val (q,qfr) = comFresh psi q p

             val psiQ = psi </I.compose/> Frame.assertion pfr
             val psiP = psi </I.compose/> Frame.assertion qfr
           in
             [SOME ([ (psiQ, p), (psiP, q) ], COM1)
             ,SOME ([ (psiQ, p), (psiP, q) ], COM2)]
           end
         | _ => [NONE]

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
               [ SOME ([(psi, p1), (psi, p2)], REPCOM1)
               , SOME ([(psi, p2), (psi, p1)], REPCOM2) ]
             end
           else [NONE]
         | _ => [NONE]


    fun inferREPI e (psi, bangP) =
      case bangP of
           P.Replication p =>
           if guarded e p then
             SOME ([ (psi, p) ], REPI)
           else NONE
         | _ => NONE


    fun inferPAR (psi, parP)  =
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

    fun inferSCOPE (psi, resP)  =
      case resP of
           P.Restriction (a,p) =>
                if (A.fresh a psi)
                    then SOME ([(psi, p)], (SCOPE a))
                    else
                      let val nn = P.newBasedOn a (A.support psi)
                      in SOME ([(psi, P.swap (a,nn) p)], (SCOPE nn))
                      end
         | _ => NONE

    fun inferOPEN (psi, resP)  =
      case resP of
           P.Restriction (a,p) =>
            if (A.fresh a psi)
                then SOME ([(psi, p)], OPEN a)
                else
                  let val nn = P.newBasedOn a (A.support psi)
                  in SOME ([(psi, P.swap (a,nn) p)], (OPEN nn))
                  end
         | _ => NONE

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


    fun infer e (a as (psi, term)) =
    let
      val rules = [inferOPEN, inferSCOPE, inferOUT, inferIN
                  ,(inferREPI e)]
      val r = (inferCOM a)
            @ (inferREPCOM e a)
            @ (inferPAR a)
            @ (inferCASEs e a)
            @ (inferINVOCATION e a)
            @ (map (fn rule => rule a) rules)
      val res = Opt.filterSome r
    in
      res
    end


    (* TODO: add a wellformedness condition before simulating *)

    fun eval_axiom e (IN,  (psi, ip as (P.Input (m, [x], _, p)))) =
        (* y # psi, m, p, x   *)
        let
          val y = P.newBasedOn x
            (x :: (A.support psi) @ (T.support m) @ (P.support p))
        in
          SOME ( psi, ip, Act.Input (SI.var y, x), [LEFT $ ChannelEq ([], psi, m, SI.var y)], p)
        end

      | eval_axiom e (OUT, (psi, ip as (P.Output (m, n, p)))) =
        (* y # psi, m, p, n    *)
        let val y = (P.new
            ((T.support n) @ (A.support psi) @ (T.support m) @ (P.support p)))
        in SOME ( psi, ip, Act.Output (SI.var y, [], n), [LEFT $ ChannelEq ([], psi, m, SI.var y)], p)
        end
      | eval_axiom _ _ = Err.undefined ()


    fun switchSubj (alpha, c) name =
    let
      val alpha =
        case alpha of
             Act.Output (_, avec, n) => Act.Output (name, avec, n)
           | Act.Input  (_, x)       => Act.Input  (name, x)
           | _ => Err.error "An undefined case in Simulator.switchSubj 1"
      val c =
        case c of
             (LEFT (ChannelEq (avec, psi, m, y)))::cs =>
                (LEFT $ ChannelEq (avec, psi, m, name))::cs
           | _ => Err.error "An undefined case in Simulator.switchSubj 2"
    in
      (alpha, c)
    end



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
          val pi = ResidualAlpha.freshNames (Act.bn alpha) (P.support q)
          val dP = PAlpha.permute pi dP
          val alpha = case alpha of
                           Act.Tau => Act.Tau
                         | Act.Output (m,avec,n) =>
                             Act.Output(m, permuteL L.swap pi avec,
                                     permuteL T.swap pi n)
                         | Act.Input (m,x) => Act.Input(m,
                                hd (permuteL L.swap pi [x]))

          val bqvec = Frame.binders (Frame.f q)
          val pi = FrameAlpha.freshNames bqvec
                    (A.support psi @ P.support p)
          val q = PAlpha.permute pi q
          val bqvec = Frame.binders (Frame.f q)
        in
          SOME (psi, pq, alpha, abstractVec abstractK bqvec c,
                P.Parallel (dP,q))
          (*
          (* bn(alpha) # Q *)
          ResidualAlpha.makeFresh (bn alpha) (alpha, dP) qSupport |>
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
            val c = abstractVec abstractK bqvec c
            val c = KAlpha.makeFresh bqvec c (Act.support alpha)
          in
            SOME (psi, pq, alpha, c, P.Parallel (dP, q))
          end) *)
        end
      | evalPAR _ _ = Err.undefined ()


    fun evalCOM ([(psiQ, iP, Act.Output (y, avec, n),
                            (c1 as (LEFT (ChannelEq (bpvec, psiPQ1, mp, _)))::cp), dP),
                 (psiP, iQ, Act.Input (z, x),
                            (c2 as (LEFT (ChannelEq (bqvec, psiPQ2, mq, _)))::cq), dQ)]
                  ,_,
                  (psi, oPQ)) sym =
    let
      (* avec # Q *)
      val (out, dP) =
        ResidualAlpha.makeFresh avec (Act.Output(y,avec,n), dP) (P.support iQ)

      val pq = (if sym then Tpl.swap else id) (dP, P.subst dQ [(x, n)])
      val pq = abstractVec abstractP avec (P.Parallel pq)
    in
      SOME (psi, oPQ, Act.Tau,
        (RIGHT (bpvec @ bqvec, psiPQ1 </I.compose/> psiPQ2, mp </I.chaneq/> mq))
          :: (abstractVec abstractK bqvec cp @ abstractVec abstractK bpvec cq),
          pq)
    end
      | evalCOM _ _ = Err.undefined ()


    fun evalREPCOM ([(_, p1, alpha1 as Act.Output (y, avec, n),
                            (c1 as (LEFT (ChannelEq (bvec1, _, m, _)))::cs1), dP1),
                     (_, p2, Act.Input (z, x),
                            (c2 as (LEFT (ChannelEq (bvec2, _, mp, _)))::cs2), dP2)],
                    _,
                    (psi, p)) sym =
    let
      val sw = if sym then Tpl.swap else id

      val (alpha1, dP1) =
        ResidualAlpha.makeFresh avec (alpha1, dP1) (P.support p)
    in
      KAlpha.makeFresh bvec1 c1 (bvec2 @ (A.support psi) @ (P.support p2)) |>
        (fn ((LEFT (ChannelEq (bvec1, psi, m, _)))::cs1) =>
            KAlpha.makeFresh bvec2 c2 (bvec1 @ (A.support psi) @ (P.support p1)) |>
            (fn ((LEFT (ChannelEq (bvec2, psi, mp, _)))::cs2) =>
            let
              val c = (RIGHT $ (bvec1 @ bvec2, psi, I.chaneq (m, mp)))
                    :: ((abstractVec abstractK bvec2 cs1)
                    @ (abstractVec abstractK bvec1 cs2))
            in
              ResidualAlpha.makeFresh [x] (Act.Input(z,x), dP2) (P.support p) |>
              (* x # !P *)
              (fn (Act.Input(z,x), dP2) =>
               let
                 val dP = P.Parallel $ sw (dP1, P.subst (P.Parallel (dP2, p)) [(x, n)])
                 val dP = abstractVec abstractP avec dP
               in
                 SOME (psi, p, Act.Tau, c, dP)
               end
              | _ => Err.undefined ())
            end
            | _ => Err.undefined ())
         | _ => Err.undefined ())
    end
      | evalREPCOM _ _ = Err.undefined ()


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
            SOME (psi, cP, alpha, abstractK a c, abstractP a dP)
          else if isOutput alpha andalso not $ T.fresh a (Act.obj alpha) then
            NONE
          else let val (alpha, c) = switchSubj (alpha, c) $
                                        SI.var $ L.newBasedOn a (a :: (A.support psi)
                                                       @ K.support c)
               in SOME (psi, cP, alpha, abstractK a c, abstractP a dP)
               end

      | eval e ([(_, iP, alpha, c, dP)],
              OPEN a,
              (psi, (cP as (P.Restriction (_, p))))) =
        (case alpha of
             Act.Output (y, a_s, n) =>
                  if Lst.member a (T.support n)
                    then SOME (psi, cP, Act.Output (y, (a :: a_s), n),
                            abstractK a c, dP)
                    else NONE
           | _ => NONE)

      (* TODO: clear this with Magnus *)
      | eval e ([(_, iP, alpha, c, dP)],
              CASE cond,
              (psi, cases)) =
              let
                val sbj = if isTau alpha then [] else [Act.subj alpha]
                val sbj = List.concat $ map T.support sbj
                val n = L.new (sbj @ C.support cond @ constraintSupport c)
                val (alpha, c) = if isTau alpha
                                    then (alpha,c)
                                    else switchSubj (alpha,c) (SI.var n)
              in
                SOME (psi, cases, alpha, c @ [RIGHT $ ([], psi, cond)], dP)
              end

      | eval e ([(_, iP, alpha, c, dP)],
              REPI,
              (psi, p)) =
        SOME (psi, p, alpha, c, P.Parallel (dP, p))


      | eval e (r as ([(_, p1, alpha1, c1, dP1), (_, p2, alpha2, c2, dP2)],
                    REPCOM1,
                    (psi, p))) =
        (case (alpha1, alpha2) of
              (Act.Output _, Act.Input _) => evalREPCOM r false
            | _ => NONE)

      | eval e (r as ([(_, p1, alpha1, c1, dP1), (_, p2, alpha2, c2, dP2)],
              REPCOM2,
              (psi, p))) =
        (case (alpha1, alpha2) of
              (Act.Input _, Act.Output _) =>
                evalREPCOM (swapPremises2 r) true
            | _ => NONE)

      | eval e ([(p, ps, alpha, c, dP)], INVOCATION, (psi, amvec)) =
        SOME (psi, amvec, alpha, c, dP)

      | eval _ _ = Err.error "Unhandled case in Simulator.eval"

  end; (* END : DT *)

  structure D = DerivationTree(DT)


  val advance =
    map $ either (fn ChannelEq (avec, psi, m, y) =>
                    (avec, psi, I.chaneq(m, y)))
                  id


  fun reduce e psi p =
  let
    val tree = D.eval_all e (psi, p)
    val tr  = map (fn (D.EInf (_,_,conclusion)) => conclusion) tree
    val tr' = map (fn (psi, p, alpha, c, p') =>
                    (psi,p,alpha, advance c, p')) tr
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

