structure InstanceName___InstanceRequisites =
struct
  type name      = unit
  type term      = unit
  type condition = unit
  type assertion = unit

  type atom = name

  fun chaneq  (a,b)       = Err.undefined ()
  fun compose (psi1,psi2) = Err.undefined ()
  val unit                = ()
  fun entails (psi, phi)  = Err.undefined ()

  (* Could use the structure StringName.swap_name (a,b) n *)
  fun swap_name (a,b) n = Err.undefined ()

  (* StringName.generateDistinct xvec *)
  fun new xvec = Err.undefined ()
  fun newBasedOn name xvec = Err.undefined ()

  fun supportT m   = Err.undefined ()
  fun supportC phi = Err.undefined ()
  fun supportA psi = Err.undefined ()

  fun swapT pi m   = Err.undefined ()
  fun swapC pi phi = Err.undefined ()
  fun swapA pi psi = Err.undefined ()

  fun eqT _ (a,b) = Err.undefined ()
  fun eqC _ (a,b) = Err.undefined ()
  fun eqA _ (a,b) = Err.undefined ()

  fun substT sigma m   = Err.undefined ()
  fun substC sigma psi = Err.undefined ()
  fun substA sigma phi = Err.undefined ()

  (* Unsorted *)
  structure Sort = Unsorted

  fun isNameSort _ = true
  fun canRecv _ _  = true
  fun canSend _ _  = true
  fun canSubs _ _  = true
  fun canRstr _    = true
  fun nameSort _   = Unsorted.SORT
  fun sortT _      = Unsorted.SORT
  fun sortC _      = Unsorted.SORT
  fun sortA _      = Unsorted.SORT

  structure Term = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom      = name
    type data      = term
    val atomSort   = nameSort
    val dataSort   = sortT
    val swap       = swapT
    val support    = supportT
    val eq         = eqT
    val new        = new
    val newBasedOn = newBasedOn
  end)

  structure Cond = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = condition
    val atomSort = nameSort
    val dataSort = sortC
    val swap     = swapC
    val support  = supportC
    val eq       = eqC
    val new        = new
    val newBasedOn = newBasedOn
  end)

  structure Assr = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = assertion
    val atomSort = nameSort
    val dataSort = sortA
    val swap     = swapA
    val support  = supportA
    val eq       = eqA
    val new      = new
    val newBasedOn = newBasedOn
  end)

  fun isWellFormedOutSubj _ = Err.undefined ()
  fun isWellFormedInSubj  _ = Err.undefined ()
  fun isWellFormedInvArg  _ = Err.undefined ()
  fun isWellFormedOutObj  _ = Err.undefined ()
  fun isWellFormedCond    _ = Err.undefined ()
  fun isWellFormedAssr    _ = Err.undefined ()
end;


structure InstanceName___PsiInstance = Psi(InstanceName___InstanceRequisites)


structure InstanceName___SymbolicInstanceRequisites =
struct
  open InstanceName___InstanceRequisites

  structure Constraint      = SymbolicOSConstraint(InstanceName___PsiInstance.Inst)
  structure BisimConstraint = SymBisimConstraint(InstanceName___PsiInstance)

  fun var n               = Err.undefined ()
  fun solve cs            = Err.undefined ()
  fun solveBisim cs       = Err.undefined ()
end;


structure InstanceName___SymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = InstanceName___PsiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = InstanceName___PsiInstance.Inst
  structure Constraint  = InstanceName___SymbolicInstanceRequisites.Constraint
  val var               = InstanceName___SymbolicInstanceRequisites.var
end


structure InstanceName___SymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = InstanceName___PsiInstance.Inst
  structure Constraint = InstanceName___SymbolicInstanceRequisites.Constraint
  val solve            = InstanceName___SymbolicInstanceRequisites.solve
end;

structure InstanceName___SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = InstanceName___PsiInstance
  structure Constraint = InstanceName___SymbolicInstanceRequisites.BisimConstraint
  val solve = InstanceName___SymbolicInstanceRequisites.solveBisim
end;

structure InstanceName___ParserPrinterRequisites =
struct
  open InstanceName___InstanceRequisites

  structure Parser = Parser(StringStream)
  structure Lex    = PsiLexerParserComb(Parser)

  fun printN n   = Err.undefined ()
  fun printT m   = Err.undefined ()
  fun printC phi = Err.undefined ()
  fun printA psi = Err.undefined ()

  fun name () = Err.undefined ()
  fun term () = Err.undefined ()
  fun cond () = Err.undefined ()
  fun assr () = Err.undefined ()

  fun parseResult p s =
    case Parser.parse (p ()) (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult term s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s

end;

structure InstanceName___ParserRequisites : PSI_PARSER_REQ =
struct
  structure Psi = InstanceName___PsiInstance
  open InstanceName___ParserPrinterRequisites
  val var = SOME InstanceName___SymbolicInstanceRequisites.var
end;

structure InstanceName___PrinterRequisites : PSI_PP_REQ =
struct
  structure Inst = InstanceName___PsiInstance.Inst
  open InstanceName___ParserPrinterRequisites
  val var = SOME InstanceName___SymbolicInstanceRequisites.var
end;

structure InstanceName___Command = CommandParser(struct
  structure SI           = InstanceName___SymbolicInstance
  structure SCS          = InstanceName___SymbolicConstraintSolver
  structure SBCS         = InstanceName___SymbolicBisimConstraintSolver
  structure PsiParserReq = InstanceName___ParserRequisites
  structure PPInst       = InstanceName___PrinterRequisites
  val useBisim           = false (* true if bisimulation constraint solver is
                                    implemented *)
end);

structure InstanceName___ = InstanceName___Command;
structure PsiInstance = InstanceName___;
