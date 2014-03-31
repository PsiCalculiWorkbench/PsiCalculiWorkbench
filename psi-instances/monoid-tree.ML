(*
    uses pwb/workbench
*)

structure PiInstanceRequirements =
struct

  open Missing

  type name      = string
  type nodeid    = int


  datatype term = Init of term
                | Data of term
                | Name of name
                | Int of int

  datatype condition = OutputConn of term * term
                     | InputConn of term * term
                     | ChEq of term * term

  datatype assertion = Top of (term * term) list

  fun preTopology (Top top) = 
    flatmap (fn (Int x, Int y) => [(x,y)] | _ => []) top

  type atom = name

  fun chaneq (m, n) = ChEq (m,n)

  fun compose (Top psi1, Top psi2) = Top $ psi1 @ psi2
  val unit = Top []

  fun entails (psi, OutputConn (m, n)) = m = n
    | entails (psi, InputConn (Int m, Int n)) =
        let val top = preTopology psi
        in  Lst.member (m,n) top orelse Lst.member (n,m) top
        end
    | entails (psi, InputConn (_, _)) = false
    | entails (_  , ChEq (Name a, Name b)) = a = b
    | entails (_  , ChEq (_,_)) = false

  fun brReceive (m,n) = InputConn (m,n)

  fun brTransmit (m,n) = OutputConn (m,n)

  fun swap_name (a,b) n = StringName.swap_name (a,b) n

  fun newBasedOn _ xvec = StringName.generateDistinct xvec
  fun new xvec = newBasedOn "a" xvec

  fun supportT (Name n) = [n]
    | supportT (Init m) = supportT m
    | supportT (Data m) = supportT m
    | supportT (Int _) = []

  fun supportC (ChEq (t1,t2)) = supportT t1 @ supportT t2
    | supportC (OutputConn (t1,t2)) =  supportT t1 @ supportT t2
    | supportC (InputConn (t1,t2)) =  supportT t1 @ supportT t2

  fun supportA psi = []

  fun swapT pi n = swap_name pi n

  fun swapT pi (Name n)    = Name (swap_name pi n)
    | swapT pi (Int i) = Int i
    | swapT pi (Init m) = Init (swapT pi m)
    | swapT pi (Data m) = Data (swapT pi m)

  fun swapC pi (ChEq (t1,t2)) = ChEq (swapT pi t1, swapT pi t2)
    | swapC pi (OutputConn (t1,t2)) = OutputConn (swapT pi t1, swapT pi t2)
    | swapC pi (InputConn (t1,t2)) = InputConn (swapT pi t1, swapT pi t2)

  fun swapA pi psi  = psi

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b

  fun substT sigma (Name n) =
    (case List.find (fn (x,_) => x = n) sigma of
           NONE       => Name n
         | SOME (_,t) => t)
    | substT sigma (Init m) = Init (substT sigma m)
    | substT sigma (Data m) = Data (substT sigma m)
    | substT sigma (Int i) = Int i

  fun substC sigma (ChEq (a,b)) = ChEq (substT sigma a, substT sigma b)
     | substC sigma (InputConn (a,b)) = InputConn (substT sigma a, substT sigma b)
     | substC sigma (OutputConn (a,b)) = OutputConn (substT sigma a, substT sigma b)

  fun substA sigma psi = psi

  (* the pi-calculus is unsorted *)
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
    type atom    = name
    type data    = term
    val atomSort = nameSort
    val dataSort = sortT
    val swap     = swapT
    val support  = supportT
    val eq       = eqT
    val new      = new
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
    val new      = new
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

  fun isWellFormedOutSubj _ = Err.undefined "Pi.isWellFormedOutSubj"
  fun isWellFormedInSubj  _ = Err.undefined "Pi.isWellFormedInSubj "
  fun isWellFormedInvArg  _ = Err.undefined "Pi.isWellFormedInvArg "
  fun isWellFormedOutObj  _ = Err.undefined "Pi.isWellFormedOutObj "
  fun isWellFormedCond    _ = Err.undefined "Pi.isWellFormedCond   "
  fun isWellFormedAssr    _ = Err.undefined "Pi.isWellFormedAssr   "
end;

structure PsiPiInstance = Psi(PiInstanceRequirements)


structure PiSymbolicInstanceRequirements =
struct
  open Missing
  open PiInstanceRequirements

  fun var x = Name x

  structure Constraint = SymbolicOSConstraint(PsiPiInstance.Inst)

  fun dom sigma = map (fn (n,t) => n) sigma

  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  structure L = NominalNameList(PsiPiInstance.Inst.Term)


  fun flattenConstraints c =
    Lst.flatmap (fn (avec, psi, phis) => map (fn phi => (avec,psi,[phi])) phis) c


  fun undef msg = Err.error msg
  fun substCstr s cs = Constraint.subst [s] cs


  fun subset x y = x |> all (fn xm => Lst.member xm y)

  fun unifyOutputs ((avec, psi, [OutputConn (Init (Int n), Name x)])::cs) rcs sigma  =
    let val subst = (x, Init $ Int $ n)
    in unifyOutputs (substCstr subst cs) (substCstr subst rcs) (subst::sigma)
    end
    | unifyOutputs (_::cs) rcs sigma =
    unifyOutputs cs rcs sigma
    | unifyOutputs [] rcs sigma = (rcs, sigma)


  fun unify [] psiS sigma   = RIGHT (sigma,psiS)
    | unify ((avec, psi, [OutputConn (Init (Int n), Name x)])::cs) psiS sigma   =
        undef "Not all outputs were pre unified"

    | unify ((avec, psi, [InputConn (Name x, Init (Int m))])::cs) (Top psiS) sigma   =
        let 
          val id = Int 0
          val node = Init id
        in
          if (psi </compose/> (Top psiS)) </entails/> InputConn (node, Init (Int m))
            then unify (substCstr (x, node) cs) (Top psiS) ((x, node)::sigma)
            else unify (substCstr (x, node) cs) (Top ((Int 0, Int m)::psiS)) ((x, node)::sigma)
        end

    | unify ((avec, psi, [InputConn (Init (Int x), Init (Int y))])::cs) (Top psiS) sigma   =
          if (psi </compose/> (Top psiS)) </entails/> InputConn (Init (Int x), Init (Int y))
            then unify cs (Top psiS) sigma
            else unify cs (Top ((Int x, Int y)::psiS)) sigma
        

    | unify ((avec, psi, [OutputConn (Init (Int x), Init (Int y))])::cs) psiS sigma   =
        if x = y then unify cs psiS sigma else LEFT "Can only broadcast on itself"

    | unify ((avec, psi, [OutputConn (Name _, Init (Int _))])::cs) psiS sigma   =
        undef "Undefined: x < init"
    | unify ((avec, psi, [OutputConn (Name _, Name _)])::cs) psiS sigma   =
        undef "Undefined: x < y"
    | unify ((avec, psi, [InputConn (Init (Int _), Name _)])::cs) psiS sigma   =
        undef "Undefined: init > x"
    | unify ((avec, psi, [InputConn (Name _ , Name _)])::cs) psiS sigma   =
        undef "Undefined: x > y"

    | unify ((avec, psi, [cond as ChEq (Data (Name x) , Data (Name y))])::cs) psiS sigma   =
        (* all names are distinct (this gives a channel equivalence of identity
         * on names (diagonal = reflexive relation) *)
        if x = y then unify cs psiS sigma  
        else Either.LEFT "Found names which are not the same"

    | unify ((avec, psi, [c])::cs) psiS sigma   = Either.LEFT ""
    | unify _ _ _ = Err.error "This shoud not happen"

  fun solve cs =
  let
    val c = flattenConstraints cs
    val (c',sigma) = unifyOutputs c c []
    val _ = PolyML.print c
    val () = print "\n\n\n"
    val _ = PolyML.print c'
  in
    unify c' (Top []) sigma
  end


  structure BisimConstraint = SymBisimConstraint(PsiPiInstance)

  val solveBisim = NONE

end;



structure SymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = PsiPiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = PsiPiInstance.Inst
  structure Constraint  = PiSymbolicInstanceRequirements.Constraint
  val var               = PiSymbolicInstanceRequirements.var
end


structure SymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = PsiPiInstance.Inst
  structure Constraint = PiSymbolicInstanceRequirements.Constraint
  type solution = (string , (Inst.name * Inst.term) list * Inst.assertion) Either.either
  val solve            = PiSymbolicInstanceRequirements.solve
end;

structure SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = PsiPiInstance
  structure Constraint = PiSymbolicInstanceRequirements.BisimConstraint
  val solve =
    case PiSymbolicInstanceRequirements.solveBisim of
         NONE => (fn c => Either.LEFT "")
       | SOME s => s
end;



structure PiParserPrinterRequirements =
struct

  open PiInstanceRequirements

  fun printN a = a

  fun printT (Name a) = a
    | printT (Int n) = Int.toString n
    | printT (Data t) = "data(" ^ printT t ^ ")"
    | printT (Init t) = "init(" ^ printT t ^ ")"

  fun printC (OutputConn (t1,t2)) = printT t1 ^ "<" ^ printT t2
    | printC (InputConn (t1,t2)) = printT t1 ^ ">" ^ printT t2
    | printC (ChEq (t1,t2)) = printT t1 ^ "==" ^ printT t2

  fun printLink (a,b) = "(" ^ printT a ^ "," ^ printT b ^ ")"
  fun printA (Top psi) =
    psi |>
    map printLink |>
    intersperse "," |>
    String.concat

  structure Parser = Parser(StringStream)
  open Parser
  open Missing

  structure Lex = PsiLexerParserComb(Parser)

  fun p >>= q = Parser.>>= (p,q)
  fun p >>  q = Parser.>>  (p,q)

  fun name () = Lex.identifier

  val intP = many1 (sat Char.isDigit) >>=
    return o always id o Int.fromString o String.concat o map Char.toString

  fun term () =
            (Lex.stok "init" >> Lex.stok "(" >> delayed term >>=
            (fn t => Lex.stok ")" >> return (Init t) ) )
    </choice/>
            (Lex.stok "data" >> Lex.stok "(" >> delayed term >>=
            (fn t => Lex.stok ")" >> return (Data t) ) )
    </choice/>
            (Lex.ws >> intP >>= (fn n => return (Int n) ) )
    </choice/>
            (name () >>= (fn a => return (Name a)))


  fun cond () =
            (term () >>=
            (fn t1 => Lex.stok "==" >> term () >>=
            (fn t2 => return (ChEq (t1, t2)) ) ) )
    </choice/>
            (term () >>=
            (fn t1 => Lex.stok ">" >> term () >>=
            (fn t2 => return (InputConn (t1, t2)) ) ) )
    </choice/>
            (term () >>=
            (fn t1 => Lex.stok "<" >> term () >>=
            (fn t2 => return (OutputConn (t1, t2)) ) ) )


  fun link () =     Lex.stok "(" >>
                    term () >>=
    (fn t1 =>       Lex.stok "," >>
                    term () >>=
    (fn t2 =>       return (t1, t2)))

  fun assr () = (link () </sepby/> Lex.stok ",") >>= return o Top

  fun parseResult p s =
    case Parser.parse (delayed p) (StringStream.make s) of
         Either.RIGHT (r,s) => Either.RIGHT r
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult term s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s

end;

structure PiParserRequirements : PSI_PARSER_REQ =
struct
  structure Psi = PsiPiInstance
  open PiParserPrinterRequirements
  val var = SOME PiSymbolicInstanceRequirements.var
end;

structure PiPrinterRequirements : PSI_PP_REQ =
struct
  structure Inst = PsiPiInstance.Inst
  open PiParserPrinterRequirements
  val var = SOME PiSymbolicInstanceRequirements.var
end;

structure PiCommand = CommandParser(struct
  structure SI           = SymbolicInstance
  structure SCS          = SymbolicConstraintSolver
  structure SBCS         = SymbolicBisimConstraintSolver
  structure PsiParserReq = PiParserRequirements
  structure PPInst       = PiPrinterRequirements
  val useBisim           = true
end);


structure Pi = PiCommand;
structure PsiInstance = Pi;

val start = Pi.start;

