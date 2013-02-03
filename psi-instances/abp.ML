(*
    uses pwb/workbench,
         pwb/constraint-solvers/pwb-smt
*)

structure PiInstanceRequirements =
struct
  open Missing

  type name = string * int

  type atom = name


  datatype term = Data of term * term
                | Bit of term
                | Datum of term
                | Neg of term
                | Name of name
                | Error | Zero | One

  datatype condition = ChEq of term * term
                     | Equal of term * term
                     | IsError of term
                     | TrueC

  datatype assertion = UnitAssr

  fun chaneq (m, n) = ChEq (m,n)

  fun compose (psi1,psi2)      = UnitAssr
  val unit                     = UnitAssr


  fun brReceive (m,n) = Err.undefined 
    "This intance is not meant to be used with broadcast semantics"

  fun brTransmit (m,n) = Err.undefined
    "This intance is not meant to be used with broadcast semantics"

  fun swap_name (a,b) n = 
    if a = n then b
    else if b = n then a
    else n

  fun max ints = List.foldr Int.max 0 ints
  fun newBasedOn (s,i) xvec = (s, (max (map Tpl.snd xvec)) + 1)

  val genName = ("gen",0)
  (*fun newBasedOn a xvec = StringName.generateDistinctBasedOn a xvec*)
  fun new xvec = newBasedOn genName xvec

  fun supportT (Name n) = [n]
    | supportT (Bit t) = supportT t
    | supportT (Datum t) = supportT t
    | supportT (Neg t) = supportT t
    | supportT (Data (t1,t2)) = supportT t1 @ supportT t2
    | supportT Error = []
    | supportT Zero = []
    | supportT One = []

  fun supportC (ChEq (t1,t2)) = supportT t1 @ supportT t2
    | supportC (Equal (t1,t2)) =  supportT t1 @ supportT t2
    | supportC (IsError t) = supportT t
    | supportC TrueC = []

  fun supportA psi = []

  fun swapT pi (Name n) = Name (swap_name pi n)
    | swapT pi (Bit b) = Bit (swapT pi b)
    | swapT pi (Datum b) = Datum (swapT pi b)
    | swapT pi (Neg b) = Neg (swapT pi b)
    | swapT pi (Data (t1,t2)) = Data (swapT pi t1, swapT pi t2)
    | swapT pi Error = Error
    | swapT pi Zero = Zero
    | swapT pi One = One

  fun swapC pi (ChEq (t1,t2)) = ChEq (swapT pi t1, swapT pi t2)
    | swapC pi (Equal (t1,t2)) = Equal (swapT pi t1, swapT pi t2)
    | swapC pi (IsError t) = IsError (swapT pi t)
    | swapC pi TrueC = TrueC

  fun swapA pi psi  = psi

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b

  fun reduceT' (Bit (Data (x, y))) = y
    | reduceT' (Datum (Data (x, y))) = x
    | reduceT' (Bit (Error)) = Error
    | reduceT' (Neg (Error)) = Error
    | reduceT' (Datum (Error)) = Error
    | reduceT' (Neg (Neg b)) = b
    | reduceT' (Neg (Zero)) = One
    | reduceT' (Neg (One)) = Zero
    | reduceT' (Data (x,y)) = Data (reduceT' x, reduceT' y)
    | reduceT' (Bit x) = Bit (reduceT' x)
    | reduceT' (Neg x) = Neg (reduceT' x)
    | reduceT' x = x

  fun fixReduceT t =
  let val newT = reduceT' t in
    if t = newT then t else fixReduceT newT
  end

  val reduceT = fixReduceT

  fun reduceC (ChEq (a,b)) = ChEq (a, b)
    | reduceC (Equal (a,b)) = Equal (reduceT a, reduceT b)
    | reduceC (IsError t) = IsError (reduceT t)
    | reduceC TrueC = TrueC

  fun entails (psi,c) = entails' (psi, reduceC c)
  and entails' (_, ChEq (Name a, Name b)) = a = b
    | entails' (_, Equal (a, b)) = a = b
    | entails' (_, TrueC) = true
    | entails' (_, IsError(Error)) = true
    | entails' _ = false

  fun reduceA psi = psi


  fun substT' sigma (Name n) =
    (case List.find (fn (x,_) => x = n) sigma of
           NONE       => Name n
         | SOME (_,t) => t)
    | substT' sigma (Bit m) = Bit (substT' sigma m)
    | substT' sigma (Datum m) = Datum (substT' sigma m)
    | substT' sigma (Data (m,n)) = Data (substT' sigma m, substT' sigma n)
    | substT' sigma (Neg m) = Neg (substT' sigma m)
    | substT' sigma Zero = Zero
    | substT' sigma One = One
    | substT' sigma Error = Error

  fun substT sigma t = substT' sigma t |> reduceT

  fun substC sigma (ChEq (a,b)) = ChEq (substT sigma a, substT sigma b)
    | substC sigma (Equal (a,b)) = Equal (substT sigma a, substT sigma b)
    | substC sigma (IsError t) = IsError (substT sigma t)
    | substC sigma TrueC = TrueC

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

  fun supportCS cs = cs |> flatmap
    (fn (avec,_,[cond]) => Lst.minus (supportC cond) avec
      | _ => Err.undefined "undefined case when calling supportCS" )

  fun termFresh t names = all ((flip L.fresh) names) $ supportT t


  fun unify _ [] sigma = Either.RIGHT (sigma,UnitAssr)

    | unify namesAvoid ((avec,psi,[TrueC])::cs) sigma =
        unify namesAvoid cs sigma

    | unify namesAvoid ((avec,psi,[ChEq (Name a, Name b)])::cs) sigma =
    if a = b then unify namesAvoid cs sigma
    else if L.fresh a avec andalso L.fresh b avec
    then let val sub = (b, Name a) in
      unify namesAvoid (substCstr sub cs) (composeSubst sigma sub) end
    else Either.LEFT TrueC


    | unify namesAvoid ((avec,psi,[c as Equal (Zero, Zero)])::cs) sigma =
        unify namesAvoid cs sigma
    | unify namesAvoid ((avec,psi,[c as Equal (Zero, One)])::cs) sigma =
        Either.LEFT TrueC
    | unify namesAvoid ((avec,psi,[c as Equal (One, Zero)])::cs) sigma =
        Either.LEFT TrueC
    | unify namesAvoid ((avec,psi,[c as Equal (One, One)])::cs) sigma =
        unify namesAvoid cs sigma

    | unify namesAvoid ((avec,psi,[c as Equal (Name a, Name b)])::cs) sigma =
    if a = b 
        then unify namesAvoid cs sigma
        else if L.fresh a avec andalso L.fresh b avec
            then let val sub = (b, Name a) in
              unify namesAvoid (substCstr sub cs) (composeSubst sigma sub) end
            else Either.LEFT TrueC

    | unify namesAvoid ((avec,psi,[c as Equal (Error,Error)])::cs) sigma =
        unify namesAvoid cs sigma
    | unify namesAvoid ((avec,psi,[c as Equal (Error, x)])::cs) sigma =
        Either.LEFT TrueC
    | unify namesAvoid ((avec,psi,[c as Equal (x, Error)])::cs) sigma =
        Either.LEFT TrueC

    (* VAR ELIM *)
    | unify namesAvoid ((avec,psi,[c as Equal (Name x, t)])::cs) sigma =
        if L.fresh x avec andalso all ((flip L.fresh) avec) (supportT t)
        then let val sub = (x,t) in
          unify namesAvoid (substCstr sub cs) (composeSubst sigma sub) end
        else Either.LEFT c

    | unify namesAvoid ((avec,psi,[c as IsError (x)])::cs) sigma =
        (case x of
             Error => unify namesAvoid cs sigma
           | Name y => unify namesAvoid ((avec,psi,[Equal(x,Error)])::cs) sigma
           | _ => Either.LEFT c)

    (* SWAP *)
    | unify namesAvoid ((avec,psi,[Equal (t1,Name x)])::cs) sigma =
        unify namesAvoid ((avec,psi,[Equal (Name x, t1)])::cs) sigma


    | unify namesAvoid ((avec,psi,[c as Equal (Data (x,y), Data (x',y'))])::cs) sigma =
        unify namesAvoid ((avec,psi,[Equal (x,x')])::(avec,psi,[Equal(y,y')])::cs) sigma


    | unify namesAvoid ((avec,psi,[c as Equal (Neg x, Neg y)])::cs) sigma =
        unify namesAvoid ((avec,psi,[Equal(x,y)])::cs) sigma


    | unify namesAvoid ((avec,psi,[c as Equal (Neg x, Bit y)])::cs) sigma =
        unify namesAvoid ((avec,psi,[Equal (Bit y, Neg x)])::cs) sigma


    | unify namesAvoid ((avec,psi,[c as Equal (Bit y, Neg x)])::cs) sigma =
        if termFresh y avec andalso termFresh x avec then 
          let
            val unifName = ("unif",0)
            val n1 = newBasedOn unifName (avec@namesAvoid)
            val n2 = newBasedOn unifName (avec@(n1::namesAvoid))
            val eq1 = Equal (y, Data (Name n1, Name n2))
            val eq2 = Equal (Name n2, Neg x)
          in
            unify (n1::n2::namesAvoid) ((avec,psi,[eq1])::(avec,psi,[eq2])::cs) sigma
          end
        else Either.LEFT c


    | unify _ _ _ = Either.LEFT TrueC


  fun unif cs =
  let
    val r = unify (supportCS cs) (flattenConstraints cs) []
  in
    r
  end


  fun solve cs =
    case unif cs of
         Either.RIGHT (sigma,psi) => Either.RIGHT [(sigma, psi)]
       | Either.LEFT phi    => Either.LEFT  [[phi]]


  structure BisimConstraint = SymBisimConstraint(PsiPiInstance)
  structure BC = BisimConstraint
  local open BisimConstraint in


  val forallEliminationRules =
    (fn (Forall (x, Imp(c,c'))) =>
        (let
          fun findE (Atomic (avec, psi, ChEq (a,b))) =
                if not (Lst.member x avec) then
                    (if Name x = a then [(x,b)] else
                     if Name x = b then [(x,a)] else [])
                else []
            | findE (TermEq (a,b)) = []
            | findE (Conj (c,c')) = findE c @ findE c'
            | findE (Disj (c,c')) = findE c @ findE c'
            | findE (Imp  (c,c')) = findE c @ findE c'
            | findE _ = []
        in
          SOME (subst (Imp (c,c')) (findE c))
        end)
       | _ => NONE) ::
    []

  val trivialConditionRules =
    (fn (StImp _) => SOME True | _ => NONE) ::
    (fn (Atomic (_, _, TrueC)) => SOME True | _ => NONE) ::
    (fn (Atomic (_, _, ChEq (a, b))) =>
        if a = b then SOME True else NONE | _ => NONE) ::
    (fn (Atomic (avec, _, ChEq (Name a, Name b))) =>
        if a <> b andalso
          (Lst.member a avec orelse Lst.member b avec)
            then SOME False else NONE
      | _ => NONE) ::
    (fn (TermEq (a, b)) =>
        if a = b then SOME True else NONE | _ => NONE) ::
    (fn (TermEq (m,n)) => SOME (Atomic ([], unit, Equal (m,n))) | _ => NONE) ::

    []


  structure ABPTheory = struct
    type literal = BC.constraint
    type model = unit

    fun neg l = Err.undefined "neg"
    fun eqL l l' = Err.undefined "eqL"
    val empty = ()
    fun extend m l = Err.undefined "extend"
    fun isConsistent m str = true
    fun models m l = true
  end

  structure ABPSolver = PwbSmtTheoryWithForget(ABPTheory)


  fun solveB c =
  let
    val cnf = 
      c |> rewrite (trivialConditionRules @ forallEliminationRules @
                   BC.simplificationRules)
        |> BC.cnfList

    val _ = PolyML.print cnf
  in
    Err.undefined "solveB"
  end

  val solveBisim = SOME solveB

  end
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
  type solution = (Inst.condition list list , ((Inst.name * Inst.term) list * Inst.assertion) list) Either.either
  val solve            = PiSymbolicInstanceRequirements.solve
end;

structure SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = PsiPiInstance
  structure Constraint = PiSymbolicInstanceRequirements.BisimConstraint
  val solve =
    case PiSymbolicInstanceRequirements.solveBisim of
         NONE => (fn c => Either.LEFT [])
       | SOME s => s
end;



structure PiParserPrinterRequirements =
struct

  open PiInstanceRequirements

  fun printN (s,i) = s ^ (if i = 0 then "" else Int.toString i)

  fun printT (Name a) = printN a
    | printT (Data (t1,t2)) = "data(" ^ printT t1 ^","^ printT t2 ^ ")"
    | printT (Neg t) = "~" ^ printT t
    | printT (Bit b) = "bit("^ printT b ^")"
    | printT (Datum b) = "datum("^ printT b ^")"
    | printT (Error) = "ERR"
    | printT (Zero) = "0"
    | printT (One) = "1"

  fun printC (ChEq (t1,t2)) = printT t1 ^ " <-> " ^ printT t2
    | printC (Equal (t1,t2)) = printT t1 ^ " = " ^ printT t2
    | printC (IsError t) = "isErr("^printT t ^")"
    | printC (TrueC) = "T"

  fun printA psi = "1"

  structure Parser = Parser(StringStream)
  open Parser
  open Missing

  structure Lex = PsiLexerParserComb(Parser)

  fun p >>= q = Parser.>>= (p,q)
  fun p >>  q = Parser.>>  (p,q)

  val toS = String.implode

  fun name () =
    many1 (sat Char.isAlpha) >>=
    (fn s => many (sat Char.isDigit) >>=
    (fn i => return (toS s, if null i then 0 else always id (Int.fromString (toS
    i)))))

  (*fun name () = Lex.identifier*)

  fun term' () =
            (Lex.stok "0" >> return Zero)
    </choice/> 
            (Lex.stok "1" >> return One)
    </choice/>
            (Lex.stok "ERR" >> return PiInstanceRequirements.Error)
    </choice/> 
            (Lex.stok "bit" >> Lex.stok "(" >> delayed term' >>=
            (fn t => Lex.stok ")" >> return (Bit t) ) )
    </choice/> 
            (Lex.stok "datum" >> Lex.stok "(" >> delayed term' >>=
            (fn t => Lex.stok ")" >> return (Datum t) ) )
    </choice/> 
            (Lex.stok "data" >> Lex.stok "(" >> delayed term' >>=
            (fn t1 => Lex.stok "," >> delayed term' >>=
            (fn t2 => Lex.stok ")" >> return (Data (t1,t2) ) )))
    </choice/>
            (Lex.stok "~" >> delayed term' >>=
            (fn t => return (Neg t) ) ) 
    </choice/>
            (Lex.ws >> name () >>= (fn a => return (Name a)))

  fun term () = delayed term'


  fun cond () =
            (Lex.stok "isErr" >> Lex.stok "(" >> delayed term >>=
            (fn t => Lex.stok ")" >> return (IsError t)))
    </choice/>
            (delayed term >>=
            (fn t1 => Lex.stok "=" >> delayed term >>=
            (fn t2 => return (Equal (t1,t2)))))
    </choice/>
            (Lex.stok "T" >> return TrueC)

  fun assr () = Lex.stok "1" >> return UnitAssr


  fun allP p = p >>= (fn r => Lex.ws >> eof r)

  fun parseResult p s =
    case Parser.parse (allP (delayed p)) (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined "Pi.parseResult RIGHT x::y::zs"
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
  val useBisim           = false
end);


structure Pi = PiCommand;
structure PsiInstance = Pi;

val start = Pi.start;
