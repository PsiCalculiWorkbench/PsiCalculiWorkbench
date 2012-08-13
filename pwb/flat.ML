(* uses pwb/missing,
        pwb/sort,
        pwb/psi,
        pwb/simulator,
        pwb/bisim,
        pwb/command
*)


signature PSI_INSTANCE_NOM =
sig
  eqtype name
  type term
  type condition
  type assertion

  val chaneq   : term * term -> condition
  val compose  : assertion * assertion -> assertion
  val unit     : assertion
  val entails  : assertion * condition -> bool

  val substT   : (name * term) list -> term      -> term
  val substC   : (name * term) list -> condition -> condition
  val substA   : (name * term) list -> assertion -> assertion

  val new      : name -> name list -> name

  val eqT      : (((name * term) * (name * term)) -> bool) -> term * term -> bool
  val eqC      : (((name * condition) * (name * condition)) -> bool) -> condition * condition -> bool
  val eqA      : (((name * assertion) * (name * assertion)) -> bool) -> assertion * assertion -> bool

  val supportT : term -> name list
  val supportC : condition -> name list
  val supportA : assertion -> name list

  val swapT    : name * name -> term -> term
  val swapC    : name * name -> condition -> condition
  val swapA    : name * name -> assertion -> assertion
end;


(*
* Make the type 'sort' into a structure Sort. I think this should make it work.
*)

signature PSI_INSTANCE_NOM_SORTED =
sig
  eqtype name
  type term
  type condition
  type assertion
  eqtype sort

  val eqSort: sort * sort -> bool

  val chaneq   : term * term -> condition
  val compose  : assertion * assertion -> assertion
  val unit     : assertion
  val entails  : assertion * condition -> bool

  val substT   : (name * term) list -> term      -> term
  val substC   : (name * term) list -> condition -> condition
  val substA   : (name * term) list -> assertion -> assertion

  val new      : name -> name list -> name

  val eqT      : (((name * term) * (name * term)) -> bool) -> term * term -> bool
  val eqC      : (((name * condition) * (name * condition)) -> bool) -> condition * condition -> bool
  val eqA      : (((name * assertion) * (name * assertion)) -> bool) -> assertion * assertion -> bool

  val supportT : term -> name list
  val supportC : condition -> name list
  val supportA : assertion -> name list

  val swapT    : name * name -> term -> term
  val swapC    : name * name -> condition -> condition
  val swapA    : name * name -> assertion -> assertion

  val isNameSort : sort -> bool
  val canRecv    : sort -> sort -> bool
  val canSend    : sort -> sort -> bool
  val canSubs    : sort -> sort -> bool
  val nameSort   : name -> sort
  val sortT      : term -> sort
  (*
  val sortC      : condition -> sort
  val sortA      : assertion -> sort
  *)
end;


signature SYMBOLIC_PSI_FLAT =
sig
  include PSI_INSTANCE_NOM

  val var : name -> term
  val nameOfConstrSort : unit -> name


  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  val solve :
    Constraint.constraint ->
           ( condition list list
           , ((name * term) list * assertion) list (* solutions *)
           ) Either.either


  structure BisimConstraint : SYMBOLIC_BISIM_CONSTRAINT
  val solveBisim :
    ( (string -> BisimConstraint.constraint -> unit) ->
      BisimConstraint.constraint ->
          ( condition list list ,
          ((name * term) list * assertion) list)
      Either.either ) option


  sharing type Constraint.Inst.name      = name
  sharing type Constraint.Inst.term      = term
  sharing type Constraint.Inst.condition = condition
  sharing type Constraint.Inst.assertion = assertion
  sharing Constraint.Inst = BisimConstraint.Psi.Inst
  sharing Constraint.AtomSort = BisimConstraint.AtomSort
  sharing Constraint.DataSort = BisimConstraint.DataSort
end;


signature C_PSI =
sig
  include SYMBOLIC_PSI_FLAT

  val parseN : string -> (string, name) Either.either
  val parseT : string -> (string, term) Either.either
  val parseC : string -> (string, condition) Either.either
  val parseA : string -> (string, assertion) Either.either

  val printN  : name      -> string
  val printT  : term      -> string
  val printC  : condition -> string
  val printA  : assertion -> string

end;



signature SYMBOLIC_PSI_FLAT_SORTED =
sig
  include PSI_INSTANCE_NOM_SORTED

  val var : name -> term
  val nameOfConstrSort : unit -> name

  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  val solve :
    Constraint.constraint ->
           ( condition list list
           , ((name * term) list * assertion) list (* solutions *)
           ) Either.either


  structure BisimConstraint : SYMBOLIC_BISIM_CONSTRAINT
  val solveBisim :
    ( (string -> BisimConstraint.constraint -> unit) ->
      BisimConstraint.constraint ->
          ( condition list list ,
          ((name * term) list * assertion) list)
      Either.either ) option


  sharing type Constraint.Inst.name      = name
  sharing type Constraint.Inst.term      = term
  sharing type Constraint.Inst.condition = condition
  sharing type Constraint.Inst.assertion = assertion
  sharing Constraint.Inst = BisimConstraint.Psi.Inst

  sharing type Constraint.AtomSort.sort = sort
  sharing Constraint.AtomSort = BisimConstraint.AtomSort
  (* sharing Constraint.DataSort = BisimConstraint.DataSort *)
end;


signature C_PSI_SORTED =
sig
  include SYMBOLIC_PSI_FLAT_SORTED

  val parseN : string -> (string, name) Either.either
  val parseT : string -> (string, term) Either.either
  val parseC : string -> (string, condition) Either.either
  val parseA : string -> (string, assertion) Either.either

  val printN  : name      -> string
  val printT  : term      -> string
  val printC  : condition -> string
  val printA  : assertion -> string

end;



(*
signature UNSORTED_SORT =
sig
  datatype sort = U
  val u : sort
end;


structure UnsortedSort : UNSORTED_SORT =
struct
  datatype sort = U
  val u = U
end;


functor PsiInstanceNomUnsortedToSorted(I: PSI_INSTANCE_NOM)
    : PSI_INSTANCE_NOM_SORTED =
struct
  open I

  type sort = UnsortedSort.sort

  fun isNameSort _ = true
  fun canRecv _ _  = true
  fun canSend _ _  = true
  fun canSubs _ _  = true
  fun nameSort _   = UnsortedSort.u
  fun sortT _      = UnsortedSort.u
  fun sortC _      = UnsortedSort.u
  fun sortA _      = UnsortedSort.u

end;
*)

(*
functor PsiInstanceNomUnsortedToSorted(I: PSI_INSTANCE_NOM)
    : PSI_INSTANCE_NOM_SORTED =
struct
  open I

  datatype sort = U

  fun isNameSort _ = true
  fun canRecv _ _  = true
  fun canSend _ _  = true
  fun canSubs _ _  = true
  fun nameSort _   = U
  fun sortT _      = U
  fun sortC _      = U
  fun sortA _      = U

end;
*)


(*
functor PsiInstanceNomUnsortedToSorted(I: PSI_INSTANCE_NOM)
    : PSI_INSTANCE_NOM_SORTED =
struct
  open I

  datatype sort = U

  fun isNameSort _ = true
  fun canRecv _ _  = true
  fun canSend _ _  = true
  fun canSubs _ _  = true
  fun nameSort _   = U
  fun sortT _      = U
  fun sortC _      = U
  fun sortA _      = U

end;
*)



functor PsiInstanceSorted(I: PSI_INSTANCE_NOM_SORTED) : PSI_INSTANCE =
struct
  open I

  structure Sort : SORT = struct
    type sort = sort
    val eq = eqSort
  end (* I *) 
  structure AtomSort = Sort
  structure DataSort = Sort

  structure Term = Nominal(
  struct
    structure AtomSort = AtomSort
    structure DataSort = DataSort
    type atom   = name
    type data   = term
    val swap    = swapT
    val support = supportT
    val new     = new
    val eq      = eqT
    val atomSort = nameSort
    val dataSort = sortT
  end)

  structure Cond = Nominal(
  struct
    structure AtomSort = AtomSort
    (* structure DataSort = DataSort *)
    structure DataSort = Unsorted
    type atom   = name
    type data   = condition
    val swap    = swapC
    val support = supportC
    val new     = new
    val eq      = eqC
    val atomSort = nameSort
    (* val dataSort = sortC *)
    fun dataSort _ = Unsorted.SORT
  end)

  structure Assr = Nominal(
  struct
    structure AtomSort = AtomSort
    (* structure DataSort = DataSort *)
    structure DataSort = Unsorted
    type atom   = name
    type data   = assertion
    val swap    = swapA
    val support = supportA
    val new     = new
    val eq      = eqA
    val atomSort = nameSort
    (* val dataSort = sortA *)
    fun dataSort _ = Unsorted.SORT
  end)
end;

functor ConstraintSorted(S: PSI_INSTANCE_NOM_SORTED): SYMBOLIC_TRANSITION_CONSTRAINT =
struct
  structure PsiInst    = PsiInstanceSorted(S)
  structure Constraint = SymbolicOSConstraint(PsiInst)
  open Constraint
end;

(*
functor PsiInstance(I: PSI_INSTANCE_NOM) : PSI_INSTANCE =
   PsiInstanceSorted(PsiInstanceNomUnsortedToSorted(I))

functor Constraint(S: PSI_INSTANCE_NOM): SYMBOLIC_TRANSITION_CONSTRAINT =
   ConstraintSorted(PsiInstanceNomUnsortedToSorted(S))
   *)


functor BisimConstraintSorted(S: PSI_INSTANCE_NOM_SORTED): 
    SYMBOLIC_BISIM_CONSTRAINT =
struct
  structure PsiInst    = PsiInstanceSorted(S)
  structure Psi        = Psi(PsiInst)
  structure Constraint = SymBisimConstraint(Psi)
  open Constraint
end;

(*
functor BisimConstraint(S: PSI_INSTANCE_NOM): SYMBOLIC_BISIM_CONSTRAINT =
   BisimConstraintSorted(PsiInstanceNomUnsortedToSorted(S))
   *)


functor CommandSorted(C: C_PSI_SORTED) =
struct
  structure CP = CommandParser(struct

    structure Psi = C.BisimConstraint.Psi
    (* structure Psi = Psi(PsiInstanceSorted(C)) *)

    structure Inst = Psi.Inst
    structure SI = struct
      structure PsiInstance = Inst
      structure Constraint  = C.Constraint
      structure Psi         = Psi
      structure Clause      = PsiClause(Psi)
      structure ClEnv       = PsiClauseEnvironment(Clause)
      val var = C.var
      val nameOfConstrSort = C.nameOfConstrSort
    end;

    structure SCS = struct
      structure Inst       = Inst
      structure Constraint = C.Constraint
      val solve            = C.solve
    end
    structure SBCS = struct
      structure Psi        = Psi
      structure Constraint = C.BisimConstraint
      val solve =
        case C.solveBisim of
             NONE => (fn pp => fn c => Either.LEFT [])
           | SOME s => s
    end
    val useBisim = case C.solveBisim of NONE => false | _ => true

    structure PsiParserReq = struct
      structure Psi = Psi
      val parseName = C.parseN
      val parseTerm = C.parseT
      val parseCond = C.parseC
      val parseAssr = C.parseA
      val var       = SOME C.var
    end
    structure PPInst = struct
      structure Inst = Psi.Inst
      val printN    = C.printN
      val printT    = C.printT
      val printC    = C.printC
      val printA    = C.printA
      val var       = SOME C.var
    end
  end)

  val start = CP.start
end;


(*
functor Command(C: C_PSI) =
struct
  structure CS = CommandSorted(struct
    open C
    structure PsiSorted = PsiInstanceNomUnsortedToSorted(C)
    open PsiSorted
  end)
  open CS
end;
*)


