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
                     | CollectC of term
                     | TrueC

  (* Assertion is the one element set 'topology' below *)
  datatype phase = Build
                 | CollectP of term
  type assertion = phase list

  (*
  val topology = [
    (0,1),
    (0,2),
    (2,3)
  ]
  *)

  val topology = [
    (0,1),
    (1,2),
    (2,3)
  ]

  val maxLevel = 5

  (*
  val topology = [
    (0,1),
    (0,2),
    (1,2),
    (1,3),
    (2,3),
    (2,4),
    (3,4)
  ]
  *)


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
    | entails (psi, CollectC (Int x)) =
        psi |> flatmap (fn (CollectP (Int p)) => [p] | _ => [])
            |> member x
    | entails _ = false

  fun brReceive (m,n) = InputConn (m,n)

  fun brTransmit (m,n) = OutputConn (m,n)

  fun swap_name (a,b) n = StringName.swap_name (a,b) n

  fun newBasedOn _ xvec = StringName.generateDistinct xvec
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
    | supportC (CollectC t) = supportT t
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
    | swapC pi (CollectC t1) = CollectC (swapT pi t1)
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


  fun reduceC (CollectC t) = CollectC (reduceT t)
    | reduceC c = c

  fun reduceA psi = psi |> map (fn (CollectP t) => CollectP (reduceT t)
                                 | x => x)


  (* TODO: need some termrwriting *)
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
    | substC sigma (CollectC a) = CollectC (substT sigma a)
    | substC sigma (TrueC) = TrueC

  fun substA sigma psi = psi |> map (fn (CollectP t) => CollectP (substT sigma t)
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
            else Either.LEFT (CollectC cl)
    | preUnify ((avec, psi, [OutputConn (Init (Int n), Name x)])::cs) psiS sigma omega kapa =
        preUnify  cs psiS sigma ((n, x)::omega) kapa
        (*let val subst = (x, Init (Int n)) in*)
            (*preUnify (substCstr subst cs) psiS (composeSubst sigma subst) kapa*)
        (*end*)
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
        else Either.LEFT cond

        (*
        if x = y
            then preUnify cs psiS sigma kapa
            else
                if L.fresh x avec andalso L.fresh y avec
                    then preUnify (substCstr (x,Name y) cs) psiS (composeSubst sigma (x,Name y)) kapa
                    else Either.LEFT cond
                    *)

    | preUnify ((avec, psi, [c])::cs) psiS sigma omega kapa = Either.LEFT c
    | preUnify _ _ _ _ _ = Err.error "This shoud not happen"


  fun solve' cs =
  let
    val m = preUnify (flattenConstraints cs) [] [] [] []
  in
    m |> either LEFT (fn (sigma,psi,omega,kapa) =>
        let
          val symtop = topology @ map Tpl.swap topology
          val cand = kapa |>
            map (fn (_,i) => List.filter (fn (x,y) => y = i) topology) |>
            map (map fst)
          val is =
            if null cand then [] else
                tl cand |> List.foldr
                (fn (a, b) => List.filter (fn x => Lst.member x a) b)
                (hd cand)
          val _ = print "\n\n"
          val _ = PolyML.print omega
          val _ = PolyML.print kapa
          val _ = PolyML.print is
        in
          if null kapa then RIGHT (sigma, psi)
          else if null is then LEFT (ChEq (Int 0, Int 0))
          else if null omega then RIGHT ((fst (hd kapa), Init (Int (hd is)))::sigma, psi)
          else let val x = fst (hd omega) val n = snd (hd omega)
               in if Lst.member x is
                    then RIGHT ((n, Init (Int x))::(fst (hd kapa), Init (Int x))::sigma, psi)
                    else LEFT (ChEq (Int 0, Int 0))
               end
        end
    )
  end


  fun solve cs =
    case solve' cs of
         Either.RIGHT (sigma,psi) => Either.RIGHT [(sigma, psi)]
       | Either.LEFT phi    => Either.LEFT  [[phi]]

  (*fun solve cs = Either.RIGHT [([], Top)]*)

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
  val solve            = PiSymbolicInstanceRequirements.solve
end;

structure SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = PsiPiInstance
  structure Constraint = PiSymbolicInstanceRequirements.BisimConstraint
  val solve =
    case PiSymbolicInstanceRequirements.solveBisim of
         NONE => (fn pp => fn c => Either.LEFT [])
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
    | printC (CollectC t1) = "collect("^ printT t1 ^")"

  fun printA psi = 
    psi |> map (fn Build => "build"
                 | CollectP i => "collect("^printT i^")")
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
            (Lex.stok "collect" >> Lex.stok "(" >> term () >>=
            (fn t => Lex.stok ")" >> return (CollectC t)))
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
    ((Lex.stok "build" >> return Build) </choice/>
     (Lex.stok "collect" >> Lex.stok "(" >> delayed term >>=
        (fn p => Lex.stok ")" >> return (CollectP p))))
    </sepby/> (Lex.stok ",")


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
  val useBisim           = true
end);


structure Pi = PiCommand;
structure PsiInstance = Pi;

val start = Pi.start;

