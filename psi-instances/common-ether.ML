(*
    uses pwb/workbench
*)
structure CommonEtherInstanceRequisites =
struct
  structure Sort = Unsorted

  type name          = string
  type term          = name
  datatype condition = Eq of name * name

  type assertion = name list


  fun chaneq  (a,b)            = Eq (a,b)
  fun compose (psi1,psi2)      = psi1 @ psi2

  val unit = []
  fun entails (psi,Eq (a, b))  =
    Lst.member a psi andalso Lst.member b psi


  fun swap_name (a,b) n = StringName.swap_name (a,b) n
  fun new xvec = StringName.generateDistinct xvec
  fun newBasedOn _ xvec = new xvec

  fun supportT n           = [n]
  fun supportC (Eq (a, b)) = [a, b]

  fun supportA psi = psi

  fun eqT _ (a,b) = a = b

  fun swapT pi n           = swap_name pi n
  fun swapC pi (Eq (a, b)) = Eq (swapT pi a, swapT pi b)

  fun brReceive (m,n) = Err.undefined 
    "This intance is not meant to be used with broadcast semantics"

  fun brTransmit (m,n) = Err.undefined
    "This intance is not meant to be used with broadcast semantics"

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

  structure L = NominalNameList(Term)

  fun swapA pi psi = L.swap pi psi

  fun substT sigma n =
    case List.find (fn (x,_) => x = n) sigma of
           NONE       => n
         | SOME (_,t) => t
  fun substC sigma (Eq (a, b)) = Eq (substT sigma a, substT sigma b)

  fun substA sigma psi =
    map (fn n =>
        case List.find (fn (a,b) => a = n) sigma of
             SOME (_,x) => x
           | NONE => n) psi

  fun eqC _ (a,b) = a = b
  fun eqA _ (psi,psi') =
    Lst.all (fn a => Lst.member a psi') psi andalso
    Lst.all (fn a => Lst.member a psi ) psi'

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



structure CommonEtherPsiInstance = Psi(CommonEtherInstanceRequisites)


structure CommonEtherSymbolicInstanceRequisites =
struct
  open CommonEtherInstanceRequisites

  structure Constraint      = SymbolicOSConstraint(CommonEtherPsiInstance.Inst)
  structure BisimConstraint = SymBisimConstraint(CommonEtherPsiInstance)

  fun var x = x

  fun x |> f = f x

  structure L = NominalNameList(Term)

  fun dom sigma = map (fn (n,t) => n) sigma
  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  fun tr ((sigma, psi'), []) = node ((sigma,psi'),[])
    | tr ((sigma, psi'),((c as (avec, psi, [(Eq (a,b))]))::cs)) =
    (case Constraint.subst sigma [c] of
      [(_, psi'', [Eq (a',b')])] =>
        let
          val psi'' = compose (psi'', psi')
          (* menmonic af = a is fresh in avec *)
          val af    = L.fresh a avec
          val bf    = L.fresh b avec
          val af'   = L.fresh a' psi''
          val bf'   = L.fresh b' psi''
          (* mnemonic am = a is member of avec *)
          val am    = not af
          val bm    = not bf
          val am'   = not af'
          val bm'   = not bf'
          val rules = [
          (* CE1 *)
          ((af andalso af' andalso bf andalso bm'),
            (fn () => (composeSubst sigma (a',b'), psi'))),

          (* CE2 *)
          ((af andalso af' andalso bm'),
            (fn () => (sigma, compose(psi', [a'])))),

          (* CE3 *)
          ((af andalso am' andalso bf andalso bf'),
            (fn () => (composeSubst sigma (b',a'), psi'))),

          (* CE4 *)
          ((am' andalso bf andalso bf'),
            (fn () => (sigma, compose(psi', [b'])))),

          (* CE5 *)
          ((af andalso af' andalso bf andalso bf'),
            (fn () => (sigma, compose(psi', [a',b'])))),

          (* CE6 *)
          ((af andalso af' andalso bf andalso bf'),
            (fn () => (composeSubst sigma (a',b'),
                       compose(psi', [b'])))),

          (* CE7 *)
          ((af andalso af' andalso bf andalso bf'),
            (fn () => (composeSubst sigma (b',a'),
                       compose(psi', [a'])))),

          (* CE8 *)
          ((entails (psi'', Eq (a',b'))),
            (fn () => (sigma, psi')))
          ]

          val valid = map (fn (_,c) => c ())
            (List.filter (fn (cond, sol) => cond) rules)
        in
          case valid of
               [] => fail ()
             | _  => node ((sigma,psi'),
                           map (fn sol => tr (sol, cs)) valid)
        end
      | _ => Err.error "explode failed in common-ether.ML")
      | tr _ = Err.undefined "tr"

  and fail () = []
  and node (n,[]) = [n]
    | node (n,l)  = List.concat l

  fun explode (avec,psi,phis) = map (fn phi => (avec, psi, [phi])) phis

  fun solve cs =
  let
    val sols = tr (([], []), Lst.flatmapmix explode cs)
  in
    case sols of
         [] => Either.LEFT "No solutions"
       | s::_  => Either.RIGHT s
  end

  fun solveBisim _ = Err.undefined "bisim unimplemented"
end;


structure CommonEtherSymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = CommonEtherPsiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = CommonEtherPsiInstance.Inst
  structure Constraint  = CommonEtherSymbolicInstanceRequisites.Constraint
  val var               = CommonEtherSymbolicInstanceRequisites.var
end


structure CommonEtherSymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = CommonEtherPsiInstance.Inst
  structure Constraint = CommonEtherSymbolicInstanceRequisites.Constraint
  type solution = (string , (Inst.name * Inst.term) list * Inst.assertion) Either.either
  val solve            = CommonEtherSymbolicInstanceRequisites.solve
end;

structure CommonEtherSymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = CommonEtherPsiInstance
  structure Constraint = CommonEtherSymbolicInstanceRequisites.BisimConstraint
  val solve = CommonEtherSymbolicInstanceRequisites.solveBisim
end;


structure CommonEtherParserPrinterRequisites =
struct
  open CommonEtherInstanceRequisites

  structure Parser = Parser(StringStream)
  structure Lex    = PsiLexerParserComb(Parser)

  fun printN a = a
  fun printT a = a
  fun printC (Eq (a, b)) = a ^ " = " ^ b
  fun printA psi = String.concat (Lst.intersperse ", " psi)

  local
    open Parser
    open Missing
  in

  fun parseResult p s =
    case Parser.parse p (StringStream.make s) of
         Either.RIGHT (r,s) => Either.RIGHT r
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  val name = Lex.identifier

  val cond =  name >>=
    (fn a =>    Lex.stok "=" >>
                name >>=
    (fn b =>    Parser.return (Eq (a,b))
    ))
  val assr = name </sepby/> (Lex.stok ",")

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult name s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s

  end
end;


structure CommonEtherParserRequisites : PSI_PARSER_REQ =
struct
  structure Psi = CommonEtherPsiInstance
  open CommonEtherParserPrinterRequisites
  val var = SOME CommonEtherSymbolicInstanceRequisites.var
end;


structure CommonEtherPrinterRequisites : PSI_PP_REQ =
struct
  structure Inst = CommonEtherPsiInstance.Inst
  open CommonEtherParserPrinterRequisites
  val var = SOME CommonEtherSymbolicInstanceRequisites.var
end;


structure CommonEtherCommand = CommandParser(struct
  structure SI           = CommonEtherSymbolicInstance
  structure SCS          = CommonEtherSymbolicConstraintSolver
  structure SBCS         = CommonEtherSymbolicBisimConstraintSolver
  structure PsiParserReq = CommonEtherParserRequisites
  structure PPInst       = CommonEtherPrinterRequisites
  val useBisim           = false (* true if bisimulation constraint solver is
                                    implemented *)
end);


structure CommonEther = CommonEtherCommand;
structure PsiInstance = CommonEther;

