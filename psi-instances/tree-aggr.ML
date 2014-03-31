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
                | Add of term * term
                | Sub of term * term
                | Agg of term * term
                | MaxT

  datatype condition = OutputConn of term * term
                     | InputConn of term * term
                     | ChEq of term * term
                     | CollectC of term * term
                     | TrueC

  (* Assertion is the one element set 'topology' below *)
  datatype phase = BuildA
                 | CollectA of term
  type assertion = phase list

  fun numberOfCollects psi x =
    psi |> filter (fn (CollectA (Name a)) => a = x
                    | _ => false)
        |> length

  fun listOfSize 0 el = []
    | listOfSize n el = el::(listOfSize (n-1) el)


  val maxLevel = 5

  val topology = [
    (0,1),
    (1,2),
    (2,3)
  ]
  val top = map (fn (x,y) => (Int x, Int y)) topology



  type atom = name


  fun chaneq (m, n) = ChEq (m,n)

  fun compose (psi1,psi2)      = psi1 @ psi2
  val unit                     = []

  fun entails (psi, OutputConn (m, n)) = m = n
    | entails (psi, InputConn (m, n)) =
        Lst.member (m,n) top orelse Lst.member (n,m) top
    | entails (_, ChEq (Name a, Name b)) = a = b
    | entails (_, ChEq (_,_)) = false
    | entails (_, TrueC) = true
    | entails (psi, CollectC (Name n, Int x)) = (numberOfCollects psi n) = x
    | entails _ = false

  fun brReceive (m,n) = InputConn (m,n)

  fun brTransmit (m,n) = OutputConn (m,n)

  fun swap_name (a,b) n = StringName.swap_name (a,b) n

  fun newBasedOn a xvec = StringName.generateDistinctBasedOn a xvec
  fun new xvec = newBasedOn "a" xvec

  fun supportT (Name n) = [n]
    | supportT (Init m) = supportT m
    | supportT (Data m) = supportT m
    | supportT (Int _) = []
    | supportT (Add (m,n)) = supportT m @ supportT n
    | supportT (Sub (m,n)) = supportT m @ supportT n
    | supportT (Agg (m,n)) = supportT m @ supportT n
    | supportT (MaxT) = []

  fun supportC (ChEq (t1,t2)) = supportT t1 @ supportT t2
    | supportC (OutputConn (t1,t2)) =  supportT t1 @ supportT t2
    | supportC (InputConn (t1,t2)) =  supportT t1 @ supportT t2
    | supportC (CollectC (t1,t2)) = supportT t1 @ supportT t2
    | supportC (TrueC) = []

  fun supportA psi = []

  fun swapT pi n = swap_name pi n

  fun swapT pi (Name n)    = Name (swap_name pi n)
    | swapT pi (Int i) = Int i
    | swapT pi (Init m) = Init (swapT pi m)
    | swapT pi (Data m) = Data (swapT pi m)
    | swapT pi (Add (m,n)) = Add (swapT pi m, swapT pi n)
    | swapT pi (Sub (m,n)) = Sub (swapT pi m, swapT pi n)
    | swapT pi (Agg (m,n)) = Agg (swapT pi m, swapT pi n)
    | swapT pi (MaxT) = MaxT

  fun swapC pi (ChEq (t1,t2)) = ChEq (swapT pi t1, swapT pi t2)
    | swapC pi (OutputConn (t1,t2)) = OutputConn (swapT pi t1, swapT pi t2)
    | swapC pi (InputConn (t1,t2)) = InputConn (swapT pi t1, swapT pi t2)
    | swapC pi (CollectC (t1,t2)) = CollectC (swapT pi t1, swapT pi t2)
    | swapC pi TrueC = TrueC

  fun swapA pi psi  = psi

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b


  fun reduceT' (Add (Int x, Int y)) = Int (x + y)
    | reduceT' (Sub (Int x, Int y)) = if x >= y then Int (x - y) else Int 0
    | reduceT' (Add (t1, t2)) = Add (reduceT' t1, reduceT' t2)
    | reduceT' (Sub (t1, t2)) = Sub (reduceT' t1, reduceT' t2)
    | reduceT' (MaxT) = Int maxLevel
    | reduceT' x = x

  fun fixReduceT t =
  let val newT = reduceT' t in
    if t = newT then t else fixReduceT newT
  end

  val reduceT = fixReduceT


  fun reduceC (CollectC (t1,t2)) = CollectC (reduceT t1, reduceT t2)
    | reduceC c = c

  fun reduceA psi = psi |> map (fn (CollectA t) => CollectA (reduceT t)
                                 | x => x)


  fun substT' sigma (Name n) =
    (case List.find (fn (x,_) => x = n) sigma of
           NONE       => Name n
         | SOME (_,t) => t)
    | substT' sigma (Init m) = Init (substT' sigma m)
    | substT' sigma (Data m) = Data (substT' sigma m)
    | substT' sigma (Int i) = Int i
    | substT' sigma (Add (m,n)) = Add (substT' sigma m, substT' sigma n)
    | substT' sigma (Sub (m,n)) = Sub (substT' sigma m, substT' sigma n)
    | substT' sigma (Agg (m,n)) = Agg (substT' sigma m, substT' sigma n)
    | substT' sigma (MaxT) = MaxT

  fun substT sigma t = substT' sigma t |> reduceT

  fun substC sigma (ChEq (a,b)) = ChEq (substT sigma a, substT sigma b)
    | substC sigma (InputConn (a,b)) = InputConn (substT sigma a, substT sigma b)
    | substC sigma (OutputConn (a,b)) = OutputConn (substT sigma a, substT sigma b)
    | substC sigma (CollectC (a,b)) = CollectC (substT sigma a, substT sigma b)
    | substC sigma (TrueC) = TrueC

  fun substA sigma psi = psi |> map (fn (CollectA t) => CollectA (substT sigma t)
                                      | x => x)

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

  fun preUnify [] psiS sigma omega kapa = Either.RIGHT (sigma,psiS,omega,kapa)
    | preUnify ((avec, psi, [TrueC])::cs) psiS sigma omega kapa =
        preUnify cs psiS sigma omega kapa
    | preUnify ((avec, psi, [CollectC cl])::cs) psiS sigma omega kapa =
        if psi </entails/> (CollectC cl)
            then preUnify cs psiS sigma omega kapa
            else (case cl of
                      (Name a, Int y) =>
                        if a <//member//> avec then Either.LEFT "Restricted name"
                        else 
                          let val n = y - (numberOfCollects psi a)
                          in preUnify cs ((listOfSize n (CollectA (Name a))) </compose/> psiS) sigma omega kapa
                          end
                     | _ => Either.LEFT "Malformed condition")
              (* preUnify cs ([(CollectA cl)] </compose/> psiS) sigma omega kapa *)
              (* Either.LEFT "collect is not entailed" *)
    | preUnify ((avec, psi, [OutputConn (Init (Int n), Name x)])::cs) psiS sigma omega kapa =
        preUnify  cs psiS sigma ((n, x)::omega) kapa
    | preUnify ((avec, psi, [OutputConn (Init (Int _), Init (Int _))])::cs) psiS sigma omega kapa =
        undef "Undefined: init < init"
    | preUnify ((avec, psi, [OutputConn (Name _, Init (Int _))])::cs) psiS sigma omega kapa =
        undef "Undefined: x < init"
    | preUnify ((avec, psi, [OutputConn (Name _, Name _)])::cs) psiS sigma omega kapa =
        undef "Undefined: x < y"
    | preUnify ((avec, psi, [InputConn (Name x, Init (Int m))])::cs) psiS sigma omega kapa =
        preUnify cs psiS sigma omega ((x, m)::kapa)
    | preUnify ((avec, psi, [InputConn (Init (Int _), Init (Int _))])::cs) psiS sigma omega kapa =
        undef "Undefined: init > init"
    | preUnify ((avec, psi, [InputConn (Init (Int _), Name _)])::cs) psiS sigma omega kapa =
        undef "Undefined: init > x"
    | preUnify ((avec, psi, [InputConn (Name _ , Name _)])::cs) psiS sigma omega kapa =
        undef "Undefined: x > y"

    | preUnify ((avec, psi, [cond as ChEq (Data (Name x) , Data (Name y))])::cs) psiS sigma omega kapa =
        (* all names are distinct (this gives a channel equivalence of identity
         * on names (diagonal = reflexive relation) *)
        if x = y then preUnify cs psiS sigma omega kapa
        else Either.LEFT "Names are not the same"

    | preUnify ((avec, psi, [c])::cs) psiS sigma omega kapa = Either.LEFT ""
    | preUnify _ _ _ _ _ = Err.error "This shoud not happen"


  val symtop = topology @ map Tpl.swap topology

  fun subset x y = x |> all (fn xm => Lst.member xm y)

  fun solve' cs =
  let
    val m = preUnify (flattenConstraints cs) [] [] [] []
    (* omega - output conn (init(n) < x)
     * kapa - input conn (x > init(n) ) *)
    fun getO omega =
      (case omega of
            [(n,x)] => (n,x)
          | _ => Err.undefined "More than one output conn in solve'")
  in
    m <//bindE//> (fn (sigma,psi,omega,kapa) =>
        case (null omega, null kapa) of
             (false, true) => let val (n,x) = getO omega in
               RIGHT ((x,Init (Int n))::sigma,psi) end
           | (true, false) =>
               let
                 val cand = kapa |>
                    map (fn (_,i) => List.filter (fn (x,y) => y = i) topology) |>
                    map (map fst)
                 val x = kapa |> map fst |> hd
               in
                 if null cand then LEFT "null cand"
                 else RIGHT ((x, Init (Int (hd $ hd cand)))::sigma, psi)
               end
           | (false,false) =>
               let
                 val (n,x) = getO omega
                 val t = topology |> List.filter (fn (x,_) => n = x) |> map snd
                 val k = map snd kapa
               in
                 if k <//subset//> t then RIGHT ((x, Init(Int n))::sigma,psi)
                 else LEFT ""
               end
           | (true, true) => RIGHT (sigma, psi)
    )
  end

  fun solve cs = solve' cs

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
    | printT (Add (t1,t2)) = printT t1 ^" + "^ printT t2
    | printT (Sub (t1,t2)) = printT t1 ^" - "^ printT t2
    | printT (Agg (t1,t2)) = printT t1 ^" @ "^ printT t2
    | printT (MaxT) = "MAX"

  fun printC (OutputConn (t1,t2)) = printT t1 ^ "<" ^ printT t2
    | printC (InputConn (t1,t2)) = printT t1 ^ ">" ^ printT t2
    | printC (ChEq (t1,t2)) = printT t1 ^ "==" ^ printT t2
    | printC (TrueC) = "T"
    | printC (CollectC (t1,t2)) = "collect("^ printT t1 ^ ", " ^ printT t2 ^")"

  fun printA psi = 
    psi |> map (fn BuildA => "build"
                 | CollectA i => "collect("^printT i^")")
        |> intersperse ","
        |> String.concat

  structure Parser = Parser(StringStream)
  open Parser
  open Missing

  structure Lex = PsiLexerParserComb(Parser)

  fun p >>= q = Parser.>>= (p,q)
  fun p >>  q = Parser.>>  (p,q)

  fun name () = Lex.identifier

  val intP = many1 (sat Char.isDigit) >>=
    return o always id o Int.fromString o String.concat o map Char.toString

  fun term' () =
            (Lex.stok "MAX" >> return MaxT)
    </choice/> 
            (Lex.stok "init" >> Lex.stok "(" >> delayed term' >>=
            (fn t => Lex.stok ")" >> return (Init t) ) )
    </choice/>
            (Lex.stok "data" >> Lex.stok "(" >> delayed term' >>=
            (fn t => Lex.stok ")" >> return (Data t) ) )
    </choice/>
            (Lex.ws >> intP >>= (fn n => return (Int n) ) )
    </choice/>
            (name () >>= (fn a => return (Name a)))

  (* A better solution is to factor this grammer to be left recursion free *)
  fun term () =
            (delayed term' </leftAssocOp1/> 
                    ((Lex.stok "+" >> return Add) </choice/>
                     (Lex.stok "-" >> return Sub) </choice/>
                     (Lex.stok "@" >> return Agg)))


  fun cond () =
            (           Lex.stok "collect" >> 
                        Lex.stok "(" >> 
                        term () >>=
            (fn t1 =>   Lex.stok "," >>
                        term () >>=
            (fn t2 =>   Lex.stok ")" >> return (CollectC (t1, t2)))))
    </choice/>
            (Lex.stok "T" >> return TrueC)

(*
    </choice/>
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
            *)

  fun assr () =
    ((Lex.stok "build" >> return BuildA) </choice/>
     (Lex.stok "collect" >> Lex.stok "(" >> delayed term >>=
        (fn p => Lex.stok ")" >> return (CollectA p))))
    </sepby/> (Lex.stok ",")


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
  val useBisim           = true
end);


structure Pi = PiCommand;
structure PsiInstance = Pi;

val start = Pi.start;

