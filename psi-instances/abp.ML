(*
    uses pwb/workbench,
         pwb/constraint-solvers/pwb-smt
*)

structure PiInstanceRequirements =
struct
  open Missing

  type name = string * int

  type atom = name

  datatype term 
    = Neg of term
    | Name of name
    | Bottom | Error | Zero | One

  datatype condition
    = ChEq of term * term
    | Equal of term * term
    | CTrue | CBottom

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
    | supportT (Neg t) = supportT t
    | supportT Error = []
    | supportT Zero = []
    | supportT One = []
    | supportT Bottom = []

  fun supportC (ChEq (t1,t2)) = supportT t1 @ supportT t2
    | supportC (Equal (t1,t2)) = supportT t1 @ supportT t2
    | supportC CTrue = []
    | supportC CBottom = []

  fun supportA psi = []

  fun swapT pi (Name n) = Name (swap_name pi n)
    | swapT pi (Neg b) = Neg (swapT pi b)
    | swapT pi Error = Error
    | swapT pi Zero = Zero
    | swapT pi One = One
    | swapT pi Bottom = Bottom

  fun swapC pi (ChEq (t1,t2)) = ChEq (swapT pi t1, swapT pi t2)
    | swapC pi (Equal (t1,t2)) = Equal (swapT pi t1, swapT pi t2)
    | swapC pi CTrue = CTrue
    | swapC pi CBottom = CBottom

  fun swapA pi psi  = psi

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b

  fun reduceT' (Neg (Error)) = Bottom
    | reduceT' (Neg (Neg (Name b))) = Name b
    | reduceT' (Neg (Zero)) = One
    | reduceT' (Neg (One)) = Zero
    | reduceT' (Neg (Bottom)) = Bottom
    | reduceT' (Neg x) = Neg (reduceT' x)
    | reduceT' x = x

  fun fixReduceT t =
  let val newT = reduceT' t in
    if t = newT then t else fixReduceT newT
  end

  val reduceT = fixReduceT

  fun reduceC' (Equal (Neg x, Neg y)) = Equal (x,y)
    | reduceC' (Equal (Error, Neg x)) = CBottom
    | reduceC' (Equal (Neg x, Error)) = CBottom
    | reduceC' (Equal (Neg x, y)) =
        if x = y then CBottom else Equal (Neg x, y)
    | reduceC' (Equal (x, Neg y)) = 
        if x = y then CBottom else Equal (x, Neg y)
    | reduceC' (Equal (Bottom, _)) = CBottom
    | reduceC' (Equal (_, Bottom)) = CBottom
    | reduceC' (Equal (Error, Zero)) = CBottom
    | reduceC' (Equal (Error, One)) = CBottom
    | reduceC' (Equal (One, Error)) = CBottom
    | reduceC' (Equal (Zero, Error)) = CBottom
    | reduceC' (Equal (Zero, One)) = CBottom
    | reduceC' (Equal (One, Zero)) = CBottom
    | reduceC' (Equal (x, y)) = if x = y then CTrue else Equal (x,y)
    | reduceC' phi = phi

  fun reduceC phi = reduceC' phi

  fun entails _ = Err.error "undefined entails"
    (*
  fun entails (psi,c) = entails' (psi, reduceC c)
  and entails' (_, ChEq (Name a, Name b)) = a = b
    | entails' (_, Equal (a, b)) = a = b
    | entails' (_, CTrue) = true
    | entails' _ = false
    *)

  fun reduceA psi = psi

  fun substT' sigma (Name n) =
    (case List.find (fn (x,_) => x = n) sigma of
           NONE       => Name n
         | SOME (_,t) => t)
    | substT' sigma (Neg m) = Neg (substT' sigma m)
    | substT' sigma Zero = Zero
    | substT' sigma One = One
    | substT' sigma Error = Error
    | substT' sigma Bttom = Bottom

  fun substT sigma t = substT' sigma t |> reduceT

  fun substC' sigma (ChEq (a,b)) = ChEq (substT sigma a, substT sigma b)
    | substC' sigma (Equal (a,b)) = Equal (substT sigma a, substT sigma b)
    | substC' sigma CTrue = CTrue
    | substC' sigma CBottom = CBottom

  fun substC sigma phi = substC' sigma phi |> reduceC


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

  fun termFresh t names = all ((flip L.fresh) names) $ supportT t


  fun unify  [] sigma = Either.RIGHT (sigma, UnitAssr)

    | unify  ((avec,psi,[CTrue])::cs) sigma = unify cs sigma

    | unify  ((avec,psi,[CBottom])::cs) sigma = Either.LEFT "_|_ encountered"

    | unify  ((avec,psi,[ChEq (Name a, Name b)])::cs) sigma =
        if a = b 
            then unify cs sigma
            else if L.fresh a avec andalso L.fresh b avec
                 then let val sub = (b, Name a) in
                    unify (substCstr sub cs) (composeSubst sigma sub) end
                 else Either.LEFT "Failed unification at equating names"

    | unify  ((avec,psi,[c as Equal (Name a, y)])::cs) sigma =
        let val sub = (a, y) in
          unify (substCstr sub cs) (composeSubst sigma sub) end

    | unify  ((avec,psi,[c as Equal (y, Name a)])::cs) sigma =
        let val sub = (a, y) in
          unify (substCstr sub cs) (composeSubst sigma sub) end

    | unify c _ = Err.error "Undefined case in the unify algorithm"


  fun unif cs =
  let
    fun red (avec,psi,[c]) = (avec,psi,[reduceC c])
      | red _ = Err.error "Undefined case for unif.red"
    fun reds cs = map red cs
    val r = unify (reds (flattenConstraints cs)) []
  in
    r
  end

  fun solve cs = unif cs


  structure BisimConstraint = SymBisimConstraint(PsiPiInstance)

  fun solveB c = LEFT "Bisimulation solver unimplemented"

  val solveBisim = SOME solveB

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

  fun printN (s,i) = s ^ (if i = 0 then "" else Int.toString i)

  fun printT (Name a) = printN a
    | printT (Neg t) = "~" ^ printT t
    | printT (Error) = "ERR"
    | printT (Zero) = "0"
    | printT (One) = "1"
    | printT (Bottom) = "_|_"

  fun printC (ChEq (t1,t2)) = printT t1 ^ " <-> " ^ printT t2
    | printC (Equal (t1,t2)) = printT t1 ^ " = " ^ printT t2
    | printC (CTrue) = "True"
    | printC (CBottom) = "False"

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
            (Lex.stok "_|_" >> return Bottom)
    </choice/>
            (Lex.stok "~" >> delayed term' >>=
            (fn t => return (Neg t) ) ) 
    </choice/>
            (Lex.ws >> name () >>= (fn a => return (Name a)))

  fun term () = delayed term'


  fun cond () =
            (delayed term >>=
            (fn t1 => Lex.stok "=" >> delayed term >>=
            (fn t2 => return (Equal (t1,t2)))))
    </choice/>
            (Lex.stok "True" >> return CTrue)
    </choice/>
            (Lex.stok "False" >> return CBottom)

  fun assr () = Lex.stok "1" >> return UnitAssr


  fun allP p = p >>= (fn r => Lex.ws >> eof r)

  fun parseResult p s =
    case Parser.parse (allP (delayed p)) (StringStream.make s) of
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
  val useBisim           = false
end);


structure Pi = PiCommand;
structure PsiInstance = Pi;

val start = Pi.start;

