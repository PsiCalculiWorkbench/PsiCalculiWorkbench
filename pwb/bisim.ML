(* uses pwb/missing,
        pwb/psi,
        pwb/simulator,
        pwb/weak-simulator
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

  include NOMINAL
    where type atom = Psi.Inst.name
    where type data = constraint
    sharing AtomSort = Psi.Inst.Sort

  val subst : constraint -> (Psi.Inst.name * Psi.Inst.term) list -> constraint

  val simplify : constraint -> constraint
  val cnf      : constraint -> constraint
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
    (string -> Constraint.constraint -> unit) ->
    Constraint.constraint ->
        ( Psi.Inst.condition list list ,
        ((Psi.Inst.name * Psi.Inst.term) list * Psi.Inst.assertion) list)
    Either.either


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

  fun cnf c = c
    |> simplify
    |> rewrite elimImpRules
    |> rewrite deMorganAndNegRules
    |> rewrite disjRules
    |> simplify

  fun dnf c = c
    |> simplify
    |> rewrite elimImpRules
    |> rewrite deMorganAndNegRules
    |> rewrite conjRules
    |> simplify


  end

  fun reduce f base []      = base
    | reduce f base [x]     = x
    | reduce f base (x::xs) = f (x, reduce f base xs)

  fun disjunct cs = reduce Disj False cs
  fun conjunct cs = reduce Conj True cs

end;

signature BISIM =
sig
  structure Psi   : PSI
  structure C     : SYMBOLIC_BISIM_CONSTRAINT
  structure ClEnv : PSI_CLAUSE_ENVIRONMENT

  val bisim :
    ClEnv.env ->
    Psi.psi * Psi.psi ->
        C.constraint * (((Psi.psi * Psi.psi) * C.constraint) list)

  sharing Psi = C.Psi = ClEnv.Cl.Psi
end;


functor Bisim(A: sig
  structure WSim   : WEAK_SYMBOLIC_PSI_SIMULATOR
  structure C      : SYMBOLIC_BISIM_CONSTRAINT
  structure SymPsi : SYMBOLIC_PSI

  sharing C.Psi = WSim.Sim.Psi = SymPsi.Psi
end) : BISIM =
struct
  open Missing
  open A

  structure Psi   = WSim.Sim.Psi
  structure TC    = WSim.Tr.Constraint
  structure R     = StrongSymbolicTransitionResidual(WSim.Sim.Tr)
  structure RA    = NominalAlpha(R)
  structure L     = NominalNameList(Psi.Inst.Term)
  structure F     = C.Frame
  structure ClEnv = WSim.Sim.ClEnv

  open C

  fun permute swap pi t =
    List.foldr (fn ((a,b), t) => swap (a,b) t) t pi

  fun unvar x = hd $ Psi.Inst.Term.support x


  val emptyT        = []
  fun joinT (w,w')  = w @ w'
  fun unionT ts     = List.foldr joinT emptyT ts
  fun snglT (p,q) c = [((p,q), c)]

  fun inW ((p,q), w) =
    maybe false (const true) $
        List.find (fn (p',q') => Psi.eqData (p,p') andalso Psi.eqData (q,q')) w


  val unitPsi = Psi.Inst.unit   (* Carry around an assertion some day. *)

  fun translateOne (bv,psi,[]) = []
    | translateOne (bv,psi,phi::phis) = 
      Atomic (bv,psi,phi) :: translateOne (bv,psi,phis)

  fun translateC []    = True
    | translateC cstrs = 
      Lst.reduce Conj $ Lst.flatmapmix translateOne cstrs

  fun collectCstrDeriv trs =
    map (fn (p,alpha,c,p') => (translateC c, p')) trs


  fun freshness avec p =
    List.foldr (fn (a,c) => FreshP (a,p) </Conj/> c) True avec

  fun strictTau env p = WSim.Sim.reduceA env p WSim.Sim.TAUa
  fun strictOut env p = WSim.Sim.reduceA env p WSim.Sim.OUTa
  fun strictIn  env p = WSim.Sim.reduceA env p WSim.Sim.INa

  fun silent  env p = WSim.silent  env p
  fun weakOut env p = WSim.reduceA env p WSim.Sim.OUTa
  fun weakIn  env p = WSim.reduceA env p WSim.Sim.INa

  val xNames       = ref ([] : Psi.Inst.name list)
  fun addName a    = xNames := (a :: !xNames)
  fun usedNames () = !xNames
  fun resetNames ()= xNames := []
  fun newName xvec =
  let
    val y = Psi.Inst.Term.new xvec
    val () = addName y
  in
    y
  end

  fun matchStImp env (p,q) c w =
  let
    val qtr = collectCstrDeriv $ silent env q
    val (cvec,tvec) = ListPair.unzip $ map
        (fn (cqi, qi) =>
            let val (ci, ti) = close env (p,qi) (c </Conj/> cqi) ((p,q)::w)
            in (cqi </Conj/> ci </Conj/>
                ((ci </Conj/> cqi) </Imp/> StImp (F.f p, F.f qi)),
                ti)
            end) qtr
  in
    (True </Imp/> disjunct cvec, unionT tvec)
  end


  and matchTau env (p,q) c w =
  let
    val ptr = collectCstrDeriv $ strictTau env p
    val qtr = collectCstrDeriv $ silent env q
    val (cvec,tvec) = ListPair.unzip $ map (fn (cpi,pi) =>
        let val (civec, tivec) = ListPair.unzip $ map (fn (cqj,qj) =>
            let val (cij,tij) =
                close env (pi,qj) (c </Conj/> cpi </Conj/> cqj) ((p,q) :: w)
            in
              (cqj </Conj/> cij, tij)
            end) qtr
        in
          (cpi </Imp/> disjunct civec, unionT tivec)
        end) ptr
  in
    (conjunct cvec, unionT tvec)
  end


  and matchOut env (p,q) c w =
  let
    val ptr = (strictOut env p) |> map
        (fn (p,(WSim.Sim.Tr.Act.Output (y', avec, n)), cpi, pi) =>
            let
              val supP = Psi.support p
              val supQ = Psi.support q
              val supC = C.support c
              val y    = newName (supP @ supQ @ supC @ usedNames ())
              val cpi  = C.swap (y, unvar y') (translateC cpi)
            in
              (RA.makeFresh avec (WSim.Sim.Tr.Act.Output (y',avec,n), pi)
                ([y] @ supP @ supQ @ supC @ (C.support cpi))) |>
                (fn (WSim.Sim.Tr.Act.Output (_, avec, n), pi) =>
                    ((y, avec, n), cpi, pi)
                  | _ => Err.undefined "Bisim.matchOut makeFresh")
            end
          | _ => Err.undefined "Bisim.matchOut default")

    val (cvec, tvec) = ListPair.unzip $ map (fn ((y,avec,ns), cpi, pi) =>
        let
          val qtr = weakOut env q
            |> List.filter (fn (_,WSim.Tr.Output (z,cvec,ns'),_,_) =>
                length cvec = length avec | _ => false)
            |> map
            (fn (q,WSim.Tr.Output (z,cvec,ns'),cqj,qj) =>
                ((y, avec, List.map (permute Psi.Inst.Term.swap (zip avec cvec)) ns'),
                 C.swap (unvar z, y) (translateC cqj),
                 permute Psi.swap (zip avec cvec) qj)
              | _ => Err.undefined "Bisim.matchOut default 2" )
          val (civec,tivec) = ListPair.unzip $ map (fn ((z,cvec,ns'),cqj,qj) =>
            let
              val (cij,tij) =
                close env
                      (pi,qj)
                      (Lst.reduce Conj (Lst.zipwith TermEq ns ns') </Conj/>
                        (c </Conj/> cpi </Conj/> cqj </Conj/>
                          freshness avec p </Conj/> freshness avec q))
                      ((p,q)::w)
            in
              (cpi </Conj/> (Lst.reduce Conj (Lst.zipwith TermEq ns ns')) </Conj/> cij, tij)
            end ) qtr
        in
          (Forall (y, (cpi </Conj/> freshness avec p </Conj/> freshness avec q)
            </Imp/> disjunct civec),
            unionT tivec)
        end) ptr
  in
    (conjunct cvec, unionT tvec)
  end


  and matchIn env (p,q) c w =
  let
    fun folder ((x,x'),pi) = Psi.swap (x,x') pi
    val ptr = strictIn env p |> map
        (fn (p,WSim.Sim.Tr.Act.Input (y',xs'),cpi,pi) =>
         let
           val supP = Psi.support p
           val supQ = Psi.support q
           val supC = C.support c
           val y    = newName (supP @ supQ @ supC @ usedNames ())
           val cpi  = C.swap (y, unvar y')
                             (translateC cpi)
           val supCpi = C.support cpi
           val xs = Psi.Inst.Term.newsBasedOn xs' (y :: supP @ supQ @ supC @ supCpi)
           val pi= List.foldr folder pi (Lst.zip xs xs')
         in
           ((y, xs), cpi, pi)
         end | _ => Err.undefined "Bisim.matchIn default" )
    val (cvec,tvec) = ListPair.unzip (map (fn ((y,xs), cpi, pi) =>
        let
          val qtr = weakIn env q |> map (fn (q,WSim.Tr.Input (z,xs'),cqj,qj) =>
            ((y, xs), C.swap (y,unvar z) (translateC cqj), List.foldr folder qj $ Lst.zip xs xs')
            | _ => Err.undefined "Bisim.matchIn default 2" )
          val (civec,tivec) = ListPair.unzip (map (fn ((z,x),cqj,qj) =>
            let
              val (cij,tij) =
                close env
                      (pi,qj)
                      (c </Conj/> cpi </Conj/> cqj)
                      ((p,q)::w)
            in (cqj </Conj/> cij, tij) end) qtr)
        in
          (Forall (y, cpi </Imp/> disjunct civec), unionT tivec)
        end) ptr)
  in
    (conjunct cvec, unionT tvec)
  end

  and close env (p,q) c w =
    if (p,q) </inW/> w then
      (True, emptyT)
    else
      let
        val (c_stimp,  t_stimp ) = matchStImp env (p,q) c w
        val (c'_stimp, t'_stimp) = matchStImp env (q,p) c w
        val (c_tau, t_tau)       = matchTau env (p,q) c w
        val (c'_tau, t'_tau)     = matchTau env (q,p) c w
        val (c_out, t_out)       = matchOut env (p,q) c w
        val (c'_out, t'_out)     = matchOut env (q,p) c w
        val (c_in, t_in)         = matchIn env (p,q) c w
        val (c'_in, t'_in)       = matchIn env (q,p) c w
      in
        (c </Conj/> c_stimp </Conj/> c'_stimp </Conj/>
         c_tau </Conj/> c'_tau </Conj/>
         c_out </Conj/> c'_out </Conj/>
         c_in </Conj/> c'_in
        ,
        (t_stimp </joinT/> t'_stimp </joinT/>
        t_tau </joinT/> t'_tau </joinT/>
        t_out </joinT/> t'_out </joinT/>
        t_in </joinT/> t'_in </joinT/>
        (snglT (p,q) (c </Conj/> c_stimp </Conj/> c_tau </Conj/>
                      c_out </Conj/> c_in)) </joinT/>
        (snglT (q,p) (c </Conj/> c'_stimp </Conj/> c'_tau </Conj/>
                      c'_out </Conj/> c'_in)) ) )
      end

  and bisim env (p,q) =
  let
    val () = resetNames ()
  in
    close env (p,q) True emptyT
  end

end;
