(* uses pwb/free/cnames,
        pwb/free/signature,
        pwb/free/conditions,
        pwb/nominal,
        pwb/missing,
        pwb/psi,
        pwb/simulator
 *)


functor NomUnitAssertion(N: sig 
                              structure AtomSort: SORT
                              eqtype atom
                              val atomSort : atom -> AtomSort.sort
                              val new      : atom -> atom list -> atom
                            end): 
                            sig
                              include NOMINAL 
                              val compose : data * data -> data
                              val unit : data
                            end =
struct
  open N

  datatype unt = Unit

  structure Nom = Nominal(struct
    type atom = atom
    type data = unt
    structure AtomSort = AtomSort
    val atomSort = atomSort
    structure DataSort = Unsorted
    fun dataSort _ = Unsorted.SORT
    fun swap _ _ = Unit
    fun support _ = []
    val new = new
    fun eq _ _ = true
  end)
  open Nom

  val unit = Unit
  fun compose _ = unit
end;



functor PreFreeTermPsiInstance(A:
  sig 
    structure Sort    : SORT
    structure Name    : NOMINAL
    structure TermSig : NOM_SIGMA
    structure AtmSig  : ATOMIC_CONDITIONS_SIGNATURE
    structure CndSig  : CONDITIONS_SIGNATURE

    val absSort    : Sort.sort -> Sort.sort -> Sort.sort
    val canRecv    : Sort.sort -> Sort.sort -> bool
    val canSend    : Sort.sort -> Sort.sort -> bool
    val canSubs    : Sort.sort -> Sort.sort -> bool
    val isNameSort : Sort.sort -> bool

    sharing Name.AtomSort = Sort
    sharing TermSig.Sort = Sort
  end) =
struct
  open A
  open Missing

  structure Sort = Sort
  type name = Name.atom

  structure Term = NomTermAlgebra(struct
    structure Sigma = TermSig
    open Name
    val absSort = absSort
  end)
  type term = Term.data

  structure Atm = NomAtomicTermConditions(struct
    structure Sig = AtmSig
    structure Trm = Term
  end)

  structure Cnd = NomTermConditions(struct
    structure Sig = CndSig
    structure Atm = Atm 
  end)
  structure Cond = Cnd
  type condition = Cnd.condition_term

  structure Assr = NomUnitAssertion(Term)
  type assertion = Assr.data


  fun substT sigma trm =
    Term.subst (map (fn (a,t) => (Term.var a, t)) sigma) trm

  fun right (Either.LEFT _) = Err.error "instance.ML: Should not occur"
    | right (Either.RIGHT r) = r

  fun substC sigma cnd =
    case Cnd.des cnd of
         LEFT  (s, cnds) => right $ Cnd.app (s, map (substC sigma) cnds)
       | RIGHT p => 
           case Cnd.Atm.des p of
                (ps, trms) => 
                Cnd.cnd $ right $ Cnd.Atm.app (ps, map (substT sigma) trms)

  fun substA sigma psi = psi

  val compose = Assr.compose
  val unit = Assr.unit

end;


structure FiniteSorts =
struct local open Missing in

  type substitutable = bool
  datatype sortsymb = NamedSort of string
                    | ConstraintNameSort

  datatype sorts
    = Sorts of (sortsymb * sortsymb) list       (* canRecv *)
             * (sortsymb * sortsymb) list       (* canSend *)
             * (sortsymb * substitutable) list  (* Name *)

  type sort = sortsymb
  val eq : sort * sort -> bool = (op=)

  fun unCanRecv (Sorts (srts,_,_)) = srts
  fun unCanSend (Sorts (_,srts,_)) = srts
  fun unName    (Sorts (_,_,srts)) = srts

  fun canRecv srts s s' = Lst.member (s,s') (unCanRecv srts)
  fun canSend srts s s' = Lst.member (s,s') (unCanSend srts)

  fun canSubs srts s s' =
    s = s' andalso maybe false snd $
                    List.find (fn (s'',b) => s = s'') (unName srts)

  fun isNameSort srts s = Lst.member s (fst $ ListPair.unzip $ unName srts)

  fun absSort _ _ = Err.undefined ()

  fun addCanRecv (Sorts (cr,cs,ns)) s s' = Sorts ((s,s')::cr,cs,ns)
  fun addCanSend (Sorts (cr,cs,ns)) s s' = Sorts (cr,(s,s')::cs,ns)
  fun addName (Sorts (cr,cs,ns)) s = Sorts (cr,cs,(s,false)::ns)

  (* TODO: Should this possibly fail? *)
  fun makeSubstitutableName (Sorts (cr,cs,ns)) s = 
  let 
    val names = List.foldr (fn ((n,sb),ns) =>
                              (if s = n then (n,true) else (n,sb))::ns) [] ns
  in
    Sorts (cr,cs,names)
  end

  fun toString (NamedSort s) = s
    | toString ConstraintNameSort =
        Err.error "FiniteSorts.toString shoudl not be called " ^
                  "on ConstraintNameSort"
end
end;


structure FinitelySortedCountedName =
struct
  structure N = CountedNames(struct
    structure S = FiniteSorts
    val toString = FiniteSorts.toString
  end)
  open N
end;


functor FinitelySortedFiniteTermSig(A:
    sig 
      val sorts : unit -> FiniteSorts.sorts
    end): 
    sig
      include NOM_SIGMA
      type sigma
      val constants : sigma -> function_symbol list
      val symbols : sigma -> function_symbol list
    end =
struct
  open A
  open Missing

  structure Sort = FiniteSorts
  datatype function_symbol = FS of string * (Sort.sort list * Sort.sort)
  type sigma = function_symbol list

  val eq = (op=)
  fun ar (FS (_,a)) = a
  val isAtomSort = FiniteSorts.isNameSort (sorts ())

  val symbols = id
  val constants = Lst.filter (fn (FS (_,(a,_))) => null a) o symbols
end;



structure FreeTermPsiReq'FinSort'ChEq (* : PSI_INSTANCE *) =
struct
  structure Sorts = FiniteSorts

  fun srts () = Sorts.Sorts ([],[],[])

  val absSort    = Sorts.absSort (srts ())
  val isNameSort = Sorts.isNameSort (srts ())
  val canSend    = Sorts.canSend (srts ())
  val canSubs    = Sorts.canSubs (srts ())
  val canRecv    = Sorts.canRecv (srts ())

  structure TermSig = FinitelySortedFiniteTermSig(struct val sorts = srts end)

  datatype cheq = ChanEq of unit
  structure AtmSig (* : ATOMIC_CONDITIONS_SIGNATURE *) = struct
    type predicate_symbol = cheq
    (* datatype predicate_symbol = AtmEq of unit *)
    val eq = (op=)
    fun ar (ChanEq ()) = 2
  end
  structure CndSig : CONDITIONS_SIGNATURE = struct (* empty sig *)
    type condition_symbol = unit
    val eq = (op=)
    fun ar _ = ~1
  end
  structure PrePsi = PreFreeTermPsiInstance(struct
    structure Sort    = Sorts
    structure Name    = FinitelySortedCountedName
    structure AtmSig  = AtmSig
    structure CndSig  = CndSig
    structure TermSig = TermSig
    val isNameSort    = isNameSort
    val absSort       = absSort
    val canSubs       = canSubs
    val canSend       = canSend
    val canRecv       = canRecv
  end)
  open PrePsi

  fun right (Either.LEFT _) = Err.error "instance.ML: Should not occur"
    | right (Either.RIGHT r) = r

  fun chaneq (t,t') = Cnd.cnd $ right $ Atm.app (ChanEq (), [t,t'])

  fun entails (psi, phi) =
    case Cnd.des phi of
         RIGHT p => (case Atm.des p of
                         (_,[t,t']) => t </Term.eqData/> t'
                       | _ => false)
       | _ => false 


  fun brReceive _ = Err.undefined ()
  fun brTransmit _ = Err.undefined ()
end;


structure FreeTermPsi'FinSort'ChEq = Psi(FreeTermPsiReq'FinSort'ChEq);


structure FreeTermSymbPsi'FinSort'ChEq : SYMBOLIC_PSI =
struct
  structure Psi         = FreeTermPsi'FinSort'ChEq
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = Psi.Inst
  structure Constraint  = SymbolicOSConstraint(PsiInstance)
  val var               = FreeTermPsiReq'FinSort'ChEq.Term.var
  fun nameOfConstrSort () =
    FinitelySortedCountedName.someNameOfSort FiniteSorts.ConstraintNameSort
end;


val x = FiniteSorts.ConstraintNameSort;
val y = FiniteSorts.Sorts ([],[],[(x,false)]);
PolyML.print x;
PolyML.print_depth 1000;
PolyML.print y;

