(* uses pwb/free/cnames,
        pwb/free/signature
 *)

signature ATOMIC_CONDITIONS_SIGNATURE =
sig
  type predicate_symbol
  val eq : predicate_symbol * predicate_symbol -> bool
  val ar : predicate_symbol -> int
end;


signature NOM_ATOMIC_TERM_CONDITIONS =
sig
  structure Sig : ATOMIC_CONDITIONS_SIGNATURE
  structure Trm: NOM_TERM_ALGEBRA

  type predicate_term

  val app: Sig.predicate_symbol * Trm.carrier list -> (string, predicate_term) Either.either
  val des: predicate_term -> Sig.predicate_symbol * Trm.carrier list

  include NOMINAL
    where type data = predicate_term
    where type atom = Trm.atom
end;


functor NomAtomicTermConditions(A: sig
                                     structure Sig: ATOMIC_CONDITIONS_SIGNATURE
                                     structure Trm: NOM_TERM_ALGEBRA
                                   end): NOM_ATOMIC_TERM_CONDITIONS =
struct
  open A
  open Missing

  datatype predicate_term = PredTrm of Sig.predicate_symbol * Trm.carrier list

  fun app (p, trms) =
    if length trms = Sig.ar p
        then RIGHT $ PredTrm (p, trms)
        else LEFT $ "The arity of ___ does not match" (* TODO *)

  fun des (PredTrm ptrm) = ptrm

  structure Nom = Nominal(struct
    structure AtomSort = Trm.AtomSort
    structure DataSort = Unsorted
    type atom = Trm.atom
    type data = predicate_term

    val atomSort = Trm.atomSort
    fun dataSort _ = Unsorted.SORT
    val new = Trm.new
    fun support (PredTrm (_, trms)) = List.concat $ map Trm.support trms
    fun eq e (PredTrm (p, trms), PredTrm (p',trms')) =
      p </Sig.eq/> p' andalso Lst.eq Trm.eqData trms trms'
    fun swap ab (PredTrm (p,trms)) = PredTrm (p, map (Trm.swap ab) trms)
  end)
  open Nom
end;


signature CONDITIONS_SIGNATURE =
sig
  type condition_symbol

  val eq : condition_symbol * condition_symbol -> bool
  val ar : condition_symbol -> int
end;


signature NOM_TERM_CONDITIONS =
sig
  structure Sig: CONDITIONS_SIGNATURE
  structure Atm: NOM_ATOMIC_TERM_CONDITIONS

  type condition_term

  val cnd : Atm.predicate_term -> condition_term

  val app: Sig.condition_symbol * condition_term list ->
                (string, condition_term) Either.either
  val des: condition_term -> 
    (Sig.condition_symbol * condition_term list,
    Atm.predicate_term) Either.either

  include NOMINAL
    where type atom = Atm.atom
    where type data = condition_term
end;


functor NomTermConditions(A: sig
                               structure Sig: CONDITIONS_SIGNATURE
                               structure Atm: NOM_ATOMIC_TERM_CONDITIONS
                             end): NOM_TERM_CONDITIONS =
struct
  open A
  open Missing
  
  datatype condition_term
    = CndTrm of Sig.condition_symbol * condition_term list
    | AtmTrm of Atm.predicate_term

  val cnd = AtmTrm
  fun prd (AtmTrm p) = SOME p
    | prd _ = NONE

  fun app (l, atms) =
    if length atms = Sig.ar l
        then RIGHT $ CndTrm (l, atms)
        else LEFT $ "NomTermConditions: wrong arity" (*TODO*)

  fun des (CndTrm c) = LEFT c
    | des (AtmTrm p) = RIGHT p

  structure Nom = Nominal(struct
    structure AtomSort = Atm.AtomSort
    structure DataSort = Unsorted

    type atom = Atm.atom
    type data = condition_term

    val atomSort = Atm.atomSort
    fun dataSort _ = Unsorted.SORT
    val new = Atm.new
    fun support (CndTrm (_, cnds)) = List.concat $ map support cnds
      | support (AtmTrm p) = Atm.support p
    fun eq e (CndTrm (l, cnds), CndTrm (l', cnds')) =
      l </Sig.eq/> l' andalso Lst.eq (eq e) cnds cnds'
      | eq e (AtmTrm p, AtmTrm p') = p </Atm.eqData/> p'
      | eq _ _ = false
    fun swap ab (CndTrm (l,cnds)) = CndTrm (l, map (swap ab) cnds)
      | swap ab (AtmTrm p) = AtmTrm (Atm.swap ab p)
  end)
  open Nom
end;


