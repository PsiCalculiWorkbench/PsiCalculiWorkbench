(* uses pwb/missing,
        pwb/nominal
*)

signature PSI_INSTANCE =
sig
  eqtype name

  structure Term: NOMINAL
  structure Cond: NOMINAL
  structure Assr: NOMINAL

  sharing type name = Term.atom = Cond.atom = Assr.atom

  structure Sort : SORT

  sharing Term.AtomSort = Cond.AtomSort = Assr.AtomSort = Sort
  sharing Term.DataSort = Sort

  val canRecv : Sort.sort -> Sort.sort -> bool
  val canSend : Sort.sort -> Sort.sort -> bool
  val canSubs : Sort.sort -> Sort.sort -> bool
  val canRstr : Sort.sort -> bool

  val isNameSort : Sort.sort -> bool

  type term      = Term.data
  type condition = Cond.data
  type assertion = Assr.data

  val chaneq     : term * term -> condition
  val brReceive  : term * term -> condition
  val brTransmit : term * term -> condition
  val compose    : assertion * assertion -> assertion
  val unit       : assertion
  val entails    : assertion * condition -> bool

  val substT     : (name * term) list -> term      -> term
  val substC     : (name * term) list -> condition -> condition
  val substA     : (name * term) list -> assertion -> assertion


  val isWellFormedOutSubj : term -> (string, string) Either.either
  val isWellFormedInSubj  : term -> (string, string) Either.either
  val isWellFormedInvArg  : term list -> (string, string) Either.either
  val isWellFormedOutObj  : term list -> (string, string) Either.either
  val isWellFormedCond    : condition -> (string, string) Either.either
  val isWellFormedAssr    : assertion -> (string, string) Either.either
end;


signature PSI =
sig
  structure Inst: PSI_INSTANCE

  (* TODO: reimplement this using views                     *)
  (* Something along the lines of                           *)
  (* http://hackage.haskell.org/trac/ghc/wiki/ViewPatterns  *)

  datatype psi
    = Nil
    | Tau         of psi
    (* Output (m, n, p) == 'M<Nvec>.P  *)
    | Output      of Inst.term * (Inst.term list) * psi
    | BrOutput    of Inst.term * (Inst.term list) * psi
    (* Input (m, xvec, n, p) == M(\xvec)Nvec.P *)
    | Input       of Inst.term * (Inst.name list) * (Inst.term list) * psi
    | BrInput     of Inst.term * (Inst.name list) * (Inst.term list) * psi
    | Case        of (Inst.condition * psi) list
    | Restriction of Inst.name * psi
    | Parallel    of psi * psi
    | Replication of psi
    | Assertion   of Inst.assertion
    (* Invocation (a, mvec) == A<Mvec> *)
    | Invocation  of string * (Inst.term list)

  include NOMINAL
    where type atom = Inst.name
    where type data = psi
    sharing AtomSort = Inst.Sort
    (* sharing DataSort = Inst.Sort *)

  (* Substitution function *)
  val subst : psi -> (Inst.name * Inst.term) list -> psi

  val isWellformed : psi -> (string * psi, string) Either.either
  val isSubstSeqWellformed : (Inst.name * Inst.term) list ->
                ((string * (Inst.name * Inst.term)) list,
                  string) Either.either
end;




signature FRAME =
sig
  structure Psi: PSI

  datatype frame = Frame of Psi.Inst.name list * Psi.Inst.assertion

  (* compute the frame of a psi agent *)
  val frameOf    : Psi.psi -> frame
  val unitFrame : frame
  val compose    : frame -> frame -> frame

  val assertion  : frame -> Psi.Inst.assertion
  val binders    : frame -> Psi.Inst.name list

  val subst      : (Psi.Inst.name * Psi.Inst.term) list -> frame -> frame

  include NOMINAL
  sharing AtomSort = Psi.AtomSort
  sharing type atom = Psi.Inst.name
  sharing type data = frame
end;


functor Frame(P: PSI): FRAME =
struct
  structure Psi = P
  local open P in

  datatype frame = Frame of Inst.name list * Inst.assertion

  val unitFrame                       = Frame ([], Inst.unit)
  fun extend_names ns (Frame (fns, a)) = Frame (ns @ fns, a)

  fun assertion (Frame ( _, a)) = a
  fun binders   (Frame ( n,_))  = n
  fun frame n a = Frame (n,a)

  structure L = NominalNameList(Inst.Term)

  structure Nom = Nominal(
  struct
    structure AtomSort = Psi.Inst.Sort
    structure DataSort = struct datatype sort = FrameSort fun eq _ = true end
    type atom = Inst.name
    type data = frame

    val atomSort = Psi.Inst.Term.atomSort
    fun dataSort _ = DataSort.FrameSort

    fun swap pi (Frame (n, a)) =
      Frame (L.swap pi n, Inst.Assr.swap pi a)

    fun support (Frame (avec, psi)) =
      Lst.minus (Inst.Assr.support psi) avec

    val new = P.new
    val newBasedOn = P.newBasedOn

    fun eq alphaEq (Frame ([], psi1), Frame ([], psi2)) =
            Inst.Assr.eqData (psi1, psi2)
      | eq alphaEq (Frame ([], psi1), Frame (bvec, psi2)) = false
      | eq alphaEq (Frame (avec, psi1), Frame ([], psi2)) = false
      | eq alphaEq (Frame (a::avec, psi1), Frame (b::bvec, psi2)) =
            List.length avec = List.length bvec andalso
            alphaEq ((a, Frame (avec, psi1)),
                     (b, Frame (bvec, psi2)))
  end)
  open Nom

  structure FrameAlpha = NominalAlpha(Nom)

  fun compose (fA as Frame (avecA, psiA)) (Frame (avecB, psiB)) =
  let (* avecA # avecB *)
    val Frame (avecA, psiA) = FrameAlpha.makeFresh avecA fA avecB
  in
    Frame (avecA @ avecB, P.Inst.compose (psiA, psiB))
  end

  fun frameOf (Tau _)               = unitFrame
    | frameOf (Input _)             = unitFrame
    | frameOf (BrInput _)           = unitFrame
    | frameOf (Output _)            = unitFrame
    | frameOf (BrOutput _)          = unitFrame
    | frameOf (Case _)              = unitFrame
    | frameOf (Replication _)       = unitFrame
    | frameOf (Assertion a)         = Frame ([], a)
    | frameOf (Parallel (p, q))     = compose (frameOf p) (frameOf q)
    | frameOf (Restriction (ns, p)) = extend_names [ns] (frameOf p)
    | frameOf (Nil)                 = unitFrame
    | frameOf (Invocation _)        = unitFrame


  local open Missing in
  fun subst sigma (f as Frame (avec, psi)) =
  let
    val sn = (map fst sigma) @ (Lst.flatmap (P.Inst.Term.support o snd) sigma)
    val Frame (avec, psi) = FrameAlpha.makeFresh avec f sn
  in
    Frame (avec, P.Inst.substA sigma psi)
  end
  end

end;
end;


signature PSI_CLAUSE =
sig
  structure Psi: PSI

  datatype clause =
    Clause of string * Psi.atom list * Psi.psi
    (*string * Psi.Inst.name list * Psi.psi*)

  include NOMINAL
    where type atom = Psi.atom
    where type data = clause

end;


functor PsiClause(P: PSI): PSI_CLAUSE =
struct
  structure Psi = P

  structure AtomSort = Psi.Inst.Sort
  structure DataSort = struct datatype sort = ClauseSort fun eq _ = true end

  datatype clause =
    Clause of string * P.Inst.name list * P.psi

  type atom = P.Inst.name
  type data = clause

  val atomSort = Psi.Inst.Term.atomSort
  fun dataSort _ = DataSort.ClauseSort

  val swapAtom = P.Inst.Term.swapAtom
  val new = P.Inst.Term.new
  val newBasedOn = P.Inst.Term.newBasedOn
  val newsBasedOn = P.Inst.Term.newsBasedOn

  fun eqData _ = Err.error "TODO: define alpha equivalence for clauses"

  structure L = NominalNameList(Psi.Inst.Term)

  fun swap pi (Clause (a, xvec, p)) = Clause (a, L.swap pi xvec, P.swap pi p)
  fun support (Clause (a, xvec, p)) = Lst.minus (P.support p) xvec
  fun fresh n cl = not (Lst.member n (support cl))
end;


signature PSI_CLAUSE_ENVIRONMENT =
sig
  structure Cl : PSI_CLAUSE
  
  type env

  val extend : env -> string -> Cl.clause -> env
  val remove : env -> string -> env
  val find   : env -> string -> Cl.clause list
  val dom    : env -> string list
  val empty  : env
end;

functor PsiClauseEnvironment(C : PSI_CLAUSE) : PSI_CLAUSE_ENVIRONMENT =
struct
  open Missing
  structure Cl = C

  type key   = string
  type value = C.clause
  type env   = (key * value) list

  fun eq a b = a = b

  fun extend e k v = (k,v)::e

  fun find e k =
    map snd $ Lst.filter ((eq k) o fst) e

  fun dom e = map fst e

  fun remove e k = Lst.filter (not o eq k o fst) e

  val empty = []
end;


functor Psi(I: PSI_INSTANCE): PSI =
struct
  open Fun

  type name      = I.name
  type term      = I.term
  type assertion = I.assertion
  type condition = I.condition

  datatype psi
    = Nil
    | Tau         of psi
    (* Output (m, n, p) == 'M<N>.P  *)
    | Output      of term * (term list) * psi
    | BrOutput    of term * (term list) * psi
    (* Input (m, xvec, n, p) == M(\xvec)N.P *)
    | Input       of term * (name list) * (term list) * psi
    | BrInput     of term * (name list) * (term list) * psi
    | Case        of (condition * psi) list
    | Restriction of name * psi
    | Parallel    of psi * psi
    | Replication of psi
    | Assertion   of assertion
    | Invocation  of string * (term list)

  (* aliases *)
  val swapT      = I.Term.swap
  val swapC      = I.Cond.swap
  val swapA      = I.Assr.swap
  val supportT   = I.Term.support
  val supportC   = I.Cond.support
  val supportA   = I.Assr.support
  val substT     = I.substT
  val substC     = I.substC
  val substA     = I.substA

  structure Inst = I


  structure Nom = Nominal(
  struct
    type atom = name
    type data = psi

    structure AtomSort = Inst.Sort
    structure DataSort = struct datatype sort = PsiSort fun eq _ = true end

    val atomSort = Inst.Term.atomSort
    fun dataSort _ = DataSort.PsiSort

    val new        = I.Term.new
    val newBasedOn = I.Term.newBasedOn
    val newsBasedOn = I.Term.newsBasedOn

    structure L = NominalNameList(I.Term)
    structure TL = NominalList(I.Term)

    fun swap _  Nil = Nil
      | swap ab (Tau p) = Tau (swap ab p)
      | swap ab (Output (m, nvec, p)) =
          Output (swapT ab m, TL.swap ab nvec, swap ab p)
      | swap ab (BrOutput (m, nvec , p)) =
          BrOutput (swapT ab m, TL.swap ab nvec, swap ab p)
      | swap ab (BrInput (m, xvec, nvec, p)) =
          BrInput (swapT ab m, L.swap ab xvec, TL.swap ab nvec, swap ab p)
      | swap ab (Input (m, xvec, nvec, p)) =
          Input (swapT ab m, L.swap ab xvec, TL.swap ab nvec, swap ab p)
      | swap ab (Case cases) =
          Case (map (fn (c, p) => (swapC ab c, swap ab p)) cases)
      | swap ab (Restriction (n, p)) =
          Restriction (I.Term.swapAtom ab n, swap ab p)
      | swap ab (Parallel (p, q)) =
          Parallel (swap ab p, swap ab q)
      | swap ab (Replication p) =
          Replication (swap ab p)
      | swap ab (Assertion psi) =
          Assertion (swapA ab psi)
      | swap ab (Invocation (a,mvec)) =
          Invocation (a, map (swapT ab) mvec)

    fun filter_binders names name_list =
      List.filter (fn n => not(Lst.member n names)) name_list


    fun support Nil = []
      | support (Tau p) = support p
      | support (Output (m,nvec,p)) = supportT m @ Lst.flatmapmix supportT nvec @ support p
      | support (Input (m,xvec,nvec,p)) =
        supportT m @ Lst.minus (Lst.flatmapmix supportT nvec @ support p) xvec
      | support (BrOutput (m,nvec,p)) = support (Output (m,nvec,p))
      | support (BrInput (m,xvec,nvec,p)) = support (Input (m,xvec,nvec,p))
      | support (Case cases) =
        List.concat (map (fn (phi,p) =>
                            supportC phi @ support p) cases)
      | support (Restriction (a,p)) = Lst.minus (support p) [a]
      | support (Parallel (p,q)) = support p @ support q
      | support (Replication p) = support p
      | support (Assertion psi) = supportA psi
      | support (Invocation (a, mvec)) = List.concat (map supportT mvec)

    structure TVec = NominalList(I.Term)

    fun eq alphaEq (Nil,Nil) = true
      | eq alphaEq (Output (m,nvec,p), Output (m',nvec',p')) =
        I.Term.eqData (m,m') 
	andalso List.length nvec = List.length nvec' 
	andalso Lst.all I.Term.eqData (Lst.zip nvec nvec') 
	andalso eq alphaEq (p,p')
      | eq alphaEq (BrOutput (m,nvec,p), BrOutput (m',nvec',p')) =
	eq alphaEq (Output   (m,nvec,p), Output   (m',nvec',p'))
      | eq alphaEq (Input (m,xvec,nvec,p), Input (m',xvec',nvec',p')) =
        List.length xvec = List.length xvec'
        andalso List.length nvec = List.length nvec'
        andalso I.Term.eqData(m, m')
        andalso
            (case xvec of
                 [] => Lst.all I.Term.eqData (Lst.zip nvec nvec') andalso eq alphaEq (p,p')
               | xs::xss =>
                   let
                     val permute = Lst.foldr
                     val x = newBasedOn xs
                              $ xvec @ xvec' @ TL.support nvec
                              @ TL.support nvec' @ support p @ support p'
                     val pi  = map (Tpl.tuple x) xvec
                     val pi' = map (Tpl.tuple x) xvec'

                     val n   = permute TL.swap nvec pi
                     val n'  = permute TL.swap nvec' pi'
                     val p   = permute swap p pi
                     val p'  = permute swap p' pi
                   in
                     Lst.all I.Term.eqData (Lst.zip n n') 
		     andalso eq alphaEq (p,p')
                   end)
      | eq alphaEq (BrInput (m,xvec,nvec,p), BrInput (m',xvec',nvec',p')) =
	eq alphaEq (Input   (m,xvec,nvec,p), Input   (m',xvec',nvec',p'))
      | eq alphaEq (Case cs, Case cs') =
        caseEq alphaEq cs cs'
      | eq alphaEq (Restriction (a,p), Restriction (a',p')) =
        alphaEq ((a,p), (a',p'))
      | eq alphaEq (Parallel (p,q), Parallel (p',q')) =
        eq alphaEq (p,p') andalso eq alphaEq (q,q')
      | eq alphaEq (Replication p, Replication p') =
        eq alphaEq (p,p')
      | eq alphaEq (Assertion psi, Assertion psi') =
        I.Assr.eqData (psi,psi')
      | eq alphaEq (Invocation (a,mvec), Invocation (a',mvec')) =
        a = a' andalso TVec.eqData (mvec, mvec')
      | eq alphaEq (Tau p, Tau p') = p </eq alphaEq/> p'
      | eq alphaEq _ = false
    and caseEq alphaEq [] [] = true
      | caseEq alphaEq [] _  = false
      | caseEq alphaEq _  [] = false
      | caseEq alphaEq ((phi,p)::cs) ((phi',p')::cs') =
        I.Cond.eqData (phi,phi') andalso
        eq alphaEq (p,p') andalso
        caseEq alphaEq cs cs'

  end)

  open Nom

  structure NN = NominalName(Nom)
  structure PA = NominalAlpha(Nom)

  fun subst' _ Nil = Nil
    | subst' s (Tau p) = Tau (subst' s p)
    | subst' s (Output (m,nvec,p)) =
        Output (substT s m, map (substT s) nvec, subst' s p)
    | subst' s (BrOutput (m,nvec,p)) =
        BrOutput (substT s m, map (substT s) nvec, subst' s p)
    | subst' s (Case cases) =
        Case (map (fn (cond, p) => (substC s cond, subst' s p)) cases)
    | subst' s (Parallel (p, q)) =
        Parallel (subst' s p, subst' s q)
    | subst' s (Replication p) =
        Replication (subst' s p)
    | subst' s (Assertion a) =
        Assertion (substA s a)
    | subst' s (res as (Restriction (y,p))) =
        (* y # xvec, y # tvec *)
        let
          val xvec = map Tpl.fst s
          val tvec = List.concat $ map (supportT o Tpl.snd) s
        in
          PA.makeFresh [y] (Restriction (y,p)) (xvec @ tvec) |>
            (fn (Restriction (y,p)) =>
                Restriction (y, subst' s p)
              | _ => Err.undefined "Psi.subst' Restriction" )
        end
    | subst' s (inp as (Input (m, xvec, nvec, p))) =
        (* xvec # yvec, tvec *)
        let
          val yvec = map Tpl.fst s
          val tvec = List.concat $ map (supportT o Tpl.snd) s
          val pvec = support p
        in
          PA.makeFresh xvec inp (yvec @ tvec @ pvec) |>
             (fn (Input (_, xvec, nvec, p)) =>
               Input (substT s m, xvec, map (substT s) nvec, subst' s p)
               | _ => Err.undefined "Psi.subst' Input")
        end
    | subst' s (BrInput args) =
    (case subst' s (Input args) of
	   (Input args') => BrInput args'
         | _             => Err.undefined "Psi.subst' BrInput")
    | subst' s (Invocation (k, mvec)) =
        Invocation (k, map (substT s) mvec)

  fun subst agent sigma = subst' sigma agent


  local open Either open Tpl open Inst in
  fun e >>= f = bindE e f
  fun e >> e' = e >>= (fn _ => e')
  fun lf p e = either (LEFT o swap o tuple p) RIGHT e
  fun bindAll es = foldr (op>>) (returnE "OK") es

  fun isWellformed Nil = returnE "OK"
    | isWellformed (Tau p) = isWellformed p
    | isWellformed (p as (Output (m,nvec,p'))) =
        (lf p $ isWellFormedOutSubj m >>
                isWellFormedOutObj nvec) >> isWellformed p'
    | isWellformed (BrOutput args) = 
      isWellformed (Output args)   (* For now, let's wait until sorts happen. *)
    | isWellformed (p as (Input (m, _, _, p'))) =
        (lf p $ isWellFormedInSubj m) >> isWellformed p'
    | isWellformed (BrInput args) = 
      isWellformed (Input args)    (* For now, let's wait until sorts happen. *)
    | isWellformed (p as (Case cnds)) =
        (lf p (bindAll (map (isWellFormedCond o fst) cnds))) >>
         bindAll (map (isWellformed o snd) cnds)
    | isWellformed (Restriction (_,p)) = isWellformed p
    | isWellformed (Parallel (p,q)) = isWellformed p >> isWellformed q
    | isWellformed (Replication p) = isWellformed p
    | isWellformed (p as (Assertion psi)) =
        lf p $ isWellFormedAssr psi
    | isWellformed (p as (Invocation (_,ms))) =
        lf p $ isWellFormedInvArg ms
  end

  fun isSubstSeqWellformed' [] err = err
    | isSubstSeqWellformed' ((a,m)::sigma) err =
    if Inst.canSubs (Inst.Term.atomSort a) (Inst.Term.dataSort m)
        then isSubstSeqWellformed' sigma err
        else isSubstSeqWellformed' sigma
                (("cannot be substituted", (a,m))::err)

  fun isSubstSeqWellformed sigma =
    case isSubstSeqWellformed' sigma [] of
         [] => Either.RIGHT "OK"
       | e  => Either.LEFT e


end;

