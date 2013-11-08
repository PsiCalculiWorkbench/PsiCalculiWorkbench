(* uses pwb/workbench
*)
structure FHSSInstanceRequisites =
struct
  type     name      = string

  datatype term = Name     of name
                | NextFreq of term

  datatype condition = Eq of term * term | True
  datatype assertion = Unit

  val unit                     = Unit
  val chaneq                   = Eq
  fun compose _                = Unit

  fun entails (Unit,Eq (m, n)) = (m = n)
    | entails (Unit,True)      = true

  fun new xvec          = StringName.generateDistinct xvec
  fun newBasedOn _ xvec = new xvec
  fun swap_name (a,b) n = StringName.swap_name (a,b) n

  fun supportT (Name n)     = [n]
    | supportT (NextFreq m) = supportT m
  fun supportC (Eq (m, n))  = supportT m @ supportT n
    | supportC True         = []

  fun supportA _            = []

  fun swapT pi (Name n)      = Name (swap_name pi n)
    | swapT pi (NextFreq t)  = NextFreq (swapT pi t)
  fun swapC _  True          = True
    | swapC pi (Eq (t1, t2)) = Eq (swapT pi t1, swapT pi t2)

  fun swapA _ _ = Unit

  fun substT sigma (Name a)     =
        (case List.find (fn (b,_) => a = b) sigma of
             NONE       => Name a
           | SOME (_,t) => t)
    | substT sigma (NextFreq n) = NextFreq (substT sigma n)

  fun substC s True           = True
    | substC s (Eq (t1, t2)) = Eq (substT s t1, substT s t2)

  fun substA _ _ = Unit

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b


  fun brReceive (m,n) = Err.undefined
    "This intance is not meant to be used with broadcast semantics"

  fun brTransmit (m,n) = Err.undefined
    "This intance is not meant to be used with broadcast semantics"


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

  val ok = Either.RIGHT "OK"
  fun isWellFormedOutSubj _ = ok
  fun isWellFormedInSubj  _ = ok
  fun isWellFormedInvArg  _ = ok
  fun isWellFormedOutObj  _ = ok
  fun isWellFormedCond    _ = ok
  fun isWellFormedAssr    _ = ok
end;

structure FHSSPsiInstance = Psi(FHSSInstanceRequisites)


structure FHSSSymbolicInstanceRequisites =
struct
  open FHSSInstanceRequisites

  fun var a = Name a

  structure Constraint      = SymbolicOSConstraint(FHSSPsiInstance.Inst)
  structure BisimConstraint = SymBisimConstraint(FHSSPsiInstance)

  fun dom sigma = map (fn (n,t) => n) sigma
  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  structure L = NominalNameList(FHSSInstanceRequisites.Term)

  fun explode (avec,psi,phis) = map (fn phi => (avec, psi, [phi])) phis

  fun freshL avec bvec =
    List.all (fn b => L.fresh b avec) bvec

  fun mgu [] sigma = Either.RIGHT sigma
    | mgu ((avec, Unit,  [True] )::cs) sigma =
      mgu cs sigma
    | mgu ((avec, Unit, [Eq (NextFreq a, NextFreq b)])::cs)
          sigma =
        mgu ((avec, Unit, [Eq (a,b)])::cs) sigma
    | mgu ((avec, Unit, [Eq (NextFreq a, Name b)])::cs)
          sigma =
        mgu ((avec, Unit, [Eq (Name b, NextFreq a)])::cs)
            sigma
    | mgu ((avec, Unit, [Eq (Name a, n)])::cs) sigma =
       if Name a = n then mgu cs sigma
         else
           if L.fresh a avec andalso
              freshL avec (supportT n) andalso
              L.fresh a (supportT n)
             then
                (* compose the produced substitution
                 * sequence with the accumulated and
                 * apply it to the residual *)
               mgu (Constraint.subst [(a, n)] cs)
                   (composeSubst sigma (a, n))
             else
               Either.LEFT "One of the names is restricted"
    | mgu _ _ = Err.error "explode failed in fhss.ML"

  fun solve cs =
    case mgu (Lst.flatmapmix explode cs) [] of
         Either.RIGHT sigma => Either.RIGHT (sigma, Unit)
       | Either.LEFT msg    => Either.LEFT  msg

end;

structure FHSSSymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = FHSSPsiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = FHSSPsiInstance.Inst
  structure Constraint  = FHSSSymbolicInstanceRequisites.Constraint
  val var               = FHSSSymbolicInstanceRequisites.var
end


structure FHSSSymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = FHSSPsiInstance.Inst
  structure Constraint = FHSSSymbolicInstanceRequisites.Constraint
  type solution = (string , (Inst.name * Inst.term) list * Inst.assertion) Either.either
  val solve            = FHSSSymbolicInstanceRequisites.solve
end;

structure FHSSSymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = FHSSPsiInstance
  structure Constraint = FHSSSymbolicInstanceRequisites.BisimConstraint
  fun solve _ = Err.undefined "bisim"
end;



structure FHSSParserPrinterRequisites =
struct
  open FHSSInstanceRequisites

  structure Parser = Parser(StringStream)
  structure Lex    = PsiLexerParserComb(Parser)

  fun printN n = n

  fun printT (Name n) = n
    | printT (NextFreq t) = "nextFreq(" ^ printT t ^ ")"

  fun printC True = "T"
    | printC (Eq (t1, t2)) =
        (printT t1) ^ " = " ^ (printT t2)
  fun printA _ = "1"


  local
    open Parser
    open Lex
    open Missing
  in

  fun parseResult p s =
    case parse p (StringStream.make s) of
         RIGHT (r,s) => RIGHT r
       | LEFT  _ => LEFT "Error parsing"

  fun term () =
        (stok "nextFreq" >> stok "(" >>
        (delayed term) >>=
        (fn t => stok ")" >> return (NextFreq t)))
    </choice/>
        (Lex.identifier >>= return o Name)



  fun parseName s = parseResult (Lex.identifier) s
  fun parseTerm s = parseResult (term ()) s
  fun parseCond s = parseResult (stok "T" >> return True) s
  fun parseAssr s = parseResult (stok "1" >> return Unit) s
  end

end;

structure FHSSParserRequisites : PSI_PARSER_REQ =
struct
  structure Psi = FHSSPsiInstance
  open FHSSParserPrinterRequisites
  val var = SOME FHSSSymbolicInstanceRequisites.var
end;

structure FHSSPrinterRequisites : PSI_PP_REQ =
struct
  structure Inst = FHSSPsiInstance.Inst
  open FHSSParserPrinterRequisites
  val var = SOME FHSSSymbolicInstanceRequisites.var
end;

structure FHSSCommand = CommandParser(struct
  structure SI           = FHSSSymbolicInstance
  structure SCS          = FHSSSymbolicConstraintSolver
  structure SBCS         = FHSSSymbolicBisimConstraintSolver
  structure PsiParserReq = FHSSParserRequisites
  structure PPInst       = FHSSPrinterRequisites
  val useBisim           = false (* true if bisimulation constraint solver is
                                    implemented *)
end);

structure FHSS = FHSSCommand;
structure PsiInstance = FHSS;

