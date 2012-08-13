structure StubInstanceRequisites =
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
  fun new n xvec = Err.undefined ()

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
  fun nameSort _   = Unsorted.SORT
  fun sortT _      = Unsorted.SORT
  fun sortC _      = Unsorted.SORT
  fun sortA _      = Unsorted.SORT

  structure Term = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = term
    val atomSort = nameSort
    val dataSort = sortT
    val swap     = swapT
    val support  = supportT
    val eq       = eqT
    val new      = new
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
    val new      = new
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
  end)

end;


structure StubPsiInstance = Psi(StubInstanceRequisites)


structure StubSymbolicInstanceRequisites =
struct
  open StubInstanceRequisites

  structure Constraint      = SymbolicOSConstraint(StubPsiInstance.Inst)
  structure BisimConstraint = SymBisimConstraint(StubPsiInstance)

  fun var n               = Err.undefined ()
  fun solve cs            = Err.undefined ()
  fun solveBisim cs       = Err.undefined ()
  fun nameOfConstrSort () = Err.undefined ()
end;


structure StubSymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = StubPsiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = StubPsiInstance.Inst
  structure Constraint  = StubSymbolicInstanceRequisites.Constraint
  val var               = StubSymbolicInstanceRequisites.var
  val nameOfConstrSort  = StubSymbolicInstanceRequisites.nameOfConstrSort
end


structure StubSymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = StubPsiInstance.Inst
  structure Constraint = StubSymbolicInstanceRequisites.Constraint
  val solve            = StubSymbolicInstanceRequisites.solve
end;

structure StubSymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = StubPsiInstance
  structure Constraint = StubSymbolicInstanceRequisites.BisimConstraint
  val solve = StubSymbolicInstanceRequisites.solveBisim
end;

structure StubParserPrinterRequisites =
struct
  open StubInstanceRequisites

  structure Parser = Parser(StringStream)
  structure Lex    = PsiParserBase(Parser)

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

structure StubParserRequisites : PSI_PARSER_REQ =
struct
  structure Psi = StubPsiInstance
  open StubParserPrinterRequisites
  val var = SOME StubSymbolicInstanceRequisites.var
end;

structure StubPrinterRequisites : PSI_INSTANCE_PRETTY_PRINTER =
struct
  structure Inst = StubPsiInstance.Inst
  open StubParserPrinterRequisites
  val var = SOME StubSymbolicInstanceRequisites.var
end;

structure StubCommand = CommandParser(struct
  structure SI           = StubSymbolicInstance
  structure SCS          = StubSymbolicConstraintSolver
  structure SBCS         = StubSymbolicBisimConstraintSolver
  structure PsiParserReq = StubParserRequisites
  structure PPInst       = StubPrinterRequisites
  val useBisim           = false (* true if bisimulation constraint solver is
                                    implemented *)
end);

structure Stub = StubCommand;
structure PsiInstance = Stub;
