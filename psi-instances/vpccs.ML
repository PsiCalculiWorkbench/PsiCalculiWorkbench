(* uses pwb/workbench, pwb/constraint-solvers/ilp
 *)

structure VPCCSInstanceRequisites =
struct
  open Missing

  datatype sort = Chan | Val | Exp

  datatype nameS = Channel | Variable
  type name = nameS * string

  datatype value = Int of int | Bool of bool
  datatype bool_exp = BoolEq of exp * exp
  and      exp = ExpBool of bool_exp
               | ExpAdd of exp * exp
               | ExpVar of name
               | ExpVal of value

  datatype term  = TExp of exp | TVal of value | TName of name
  datatype condition =
    CBool of bool_exp | CVal of bool |
    ChEq of term * term
  type assertion = unit

  type atom = name

  fun nameSort (Channel, _) = Chan | nameSort (Variable, _) = Exp

  fun bexpSupp (BoolEq (a,b)) = expSupp a @ expSupp b

  and expSupp (ExpBool bexp) = bexpSupp bexp
    | expSupp (ExpAdd (a,b)) = expSupp a @ expSupp b
    | expSupp (ExpVar v) = [v]
    | expSupp (ExpVal vl) = []

  fun isClosed exp = null (expSupp exp)
  fun isClosedB exp = null (bexpSupp exp)

  fun eval exp =
    if isClosed exp
      then evalExp exp
      else LEFT exp

  and evalB exp =
    if isClosedB exp
      then evalBExp exp
      else LEFT exp

  and evalExp (e as (ExpAdd (a,b))) =
    (case (evalExp a, evalExp b) of
         (RIGHT (Int x), RIGHT (Int y)) => RIGHT (Int (x + y))
       | _ => LEFT e)
    | evalExp (e as (ExpBool bexp)) =
        evalBExp bexp |> either (LEFT o const e) RIGHT
    | evalExp (ExpVal v) = RIGHT v
    | evalExp _ = Err.undefined ""

  and evalBExp (e as (BoolEq (a,b))) =
    (case (evalExp a, evalExp b) of
          (RIGHT (Bool a), RIGHT (Bool b)) => RIGHT (Bool (a = b))
        | (RIGHT (Int a),  RIGHT (Int b)) => RIGHT (Bool (a = b))
        | _ => LEFT e)

  fun chaneq  (a,b) = ChEq (a,b)
  fun compose (psi1,psi2) = ()
  val unit                = ()
  fun entails (_, (CVal v)) = v
    | entails _ = false

  fun swap_name ((sa, a), (sb, b)) (sn, n) =
    if sa = sb andalso sb = sn
        then (sa, StringName.swap_name (a,b) n)
        else (sn, n)

  fun newBasedOn (sn, _) xvec =
    (sn, StringName.generateDistinct (map (fn (_,x) => x) xvec))
  fun new xvec = newBasedOn (Channel, "a") xvec


  fun supportT (TExp exp)   = expSupp exp
    | supportT (TVal _ ) = []
    | supportT (TName n) = [n]
  fun supportC (CVal _) = []
    | supportC (CBool exp) = bexpSupp exp
    | supportC (ChEq (a,b)) = supportT a @ supportT b
  fun supportA psi = []

  fun swapExp pi (ExpAdd (e,e')) = ExpAdd (swapExp pi e, swapExp pi e')
    | swapExp pi (ExpVar n) = ExpVar $ swap_name pi n
    | swapExp pi (v as (ExpVal _)) = v
    | swapExp pi (ExpBool bexp) = ExpBool $ swapBExp pi bexp
  and swapBExp pi (BoolEq (a, b)) = BoolEq (swapExp pi a, swapExp pi b)

  fun swapT pi (TExp exp) = TExp (swapExp pi exp)
    | swapT pi (v as (TVal _)) = v
    | swapT pi (TName n) = TName (swap_name pi n)

  fun swapC pi (CBool bexp) = CBool $ swapBExp pi bexp
    | swapC pi (v as (CVal _)) = v
    | swapC pi (ChEq (a,b)) = ChEq (swapT pi a, swapT pi b)

  fun swapA pi psi = ()

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = true


  fun substExp s (ExpAdd (e,e')) = ExpAdd (substExp s e, substExp s e')
    | substExp s (v as (ExpVal _)) = v
    | substExp s (var as (ExpVar n)) =
        (case List.find (fn (x,e) => x = n) s of
             SOME (_,e) => e
           | NONE => var)
    | substExp s (ExpBool bexp) = ExpBool $ substBExp s bexp
  and substBExp s (BoolEq (e,e')) = BoolEq (substExp s e, substExp s e')

  fun substEvalExp s exp = eval (substExp s exp)
  fun substEvalBExp s bexp = evalB (substBExp s bexp)


  fun termSigmaToExp s =
    s |>
    filter (fn ((Variable, _), _) => true | _ => false) |>
    map (fn (x, TVal v) => (x, ExpVal v)
          | (x, TName n) => (x, ExpVar n)
          | (x, TExp (ExpVar n)) => (x, ExpVar n)
          | _ =>
              Err.error "Variables can be substituted only for values")


  fun substT s (TExp m) = substEvalExp (termSigmaToExp s) m |> either TExp TVal
    | substT s (v as (TVal _)) = v
    (*| substT s (TName _) = Err.error "Channels are not values"*)
    | substT s x = x


  fun substC s (v as (CVal _)) = v
    | substC s (CBool bexp) =
        substEvalBExp (termSigmaToExp s) bexp |>
            either CBool (fn (Bool b) => CVal b
                           | _ => Err.error "Condition reduced to non boolean value")
    | substC s (ChEq (a,b)) = ChEq (substT s a, substT s b)

  fun substA s phi = ()

  fun brTransmit (m,n) = Err.undefined ""
  fun brReceive (m,n) = Err.undefined ""


  structure Sort = struct
    type sort = sort
    val eq = (op=)
  end


  fun isNameSort Chan = true | isNameSort Val = false | isNameSort Exp = true
  fun canRecv Chan Exp = true | canRecv Chan Val = true | canRecv _ _ = false
  fun canSend Chan Exp = true | canSend Chan Val = true | canSend _ _ = false
  fun canSubs Exp Value = true | canSubs _ _ = false
  fun canRstr Chan   = true | canRstr _ = false

  fun sortT (TExp _) = Exp
    | sortT (TVal _) = Val
    | sortT (TName n) = nameSort n

  fun sortC _ = Unsorted.SORT
  fun sortA _ = Unsorted.SORT


  structure CondSort = Unsorted
  structure AssrSort = Unsorted

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
    val newBasedOn=newBasedOn
  end)

  structure Cond = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = CondSort
    type atom    = name
    type data    = condition
    val atomSort = nameSort
    val dataSort = sortC
    val swap     = swapC
    val support  = supportC
    val eq       = eqC
    val new      = new
    val newBasedOn=newBasedOn
  end)

  structure Assr = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = AssrSort
    type atom    = name
    type data    = assertion
    val atomSort = nameSort
    val dataSort = sortA
    val swap     = swapA
    val support  = supportA
    val eq       = eqA
    val new      = new
    val newBasedOn=newBasedOn
  end)

  fun isWellFormedOutSubj _ = Err.undefined "Pi.isWellFormedOutSubj"
  fun isWellFormedInSubj  _ = Err.undefined "Pi.isWellFormedInSubj "
  fun isWellFormedInvArg  _ = Err.undefined "Pi.isWellFormedInvArg "
  fun isWellFormedOutObj  _ = Err.undefined "Pi.isWellFormedOutObj "
  fun isWellFormedCond    _ = Err.undefined "Pi.isWellFormedCond   "
  fun isWellFormedAssr    _ = Err.undefined "Pi.isWellFormedAssr   "
end;


structure VPCCSPsiInstance = Psi(VPCCSInstanceRequisites)


structure VPCCSSymbolicInstanceRequisites =
struct
  open VPCCSInstanceRequisites
  open Missing

  structure Constraint      = SymbolicOSConstraint(VPCCSPsiInstance.Inst)
  structure BisimConstraint = SymBisimConstraint(VPCCSPsiInstance)

  fun var n               = TName n

  open Constraint

  (*fun lineariseConstraint (Atomic (_,c)) = [([], c)]*)
    (*| lineariseConstraint (Restriction (bs, c)) =*)
        (*map (fn (ns, cnd) => (bs @ ns, cnd)) (lineariseConstraint c)*)
    (*| lineariseConstraint (Conjunction cs) = flatmap lineariseConstraint cs*)
    (*| lineariseConstraint (Exists _) = Err.error "Exists constraint encountered"*)

  fun explode (avec,phis) = map (fn phi => (avec,phi)) phis
  fun lineariseConstraint cs =
    Lst.flatmapmix (fn (avec,psi,c) => explode (avec,c)) cs


  fun expToEq (ExpAdd (a,b)) = expToEq a @ expToEq b
    | expToEq (ExpVal (Int v)) = [(v, "")]
    | expToEq (ExpVar (Variables, n)) = [(1, n)]
    | expToEq _ = Err.error "Boolean expression is malformed"

  fun bexpToILP (BoolEq (a,b)) =
    (expToEq a, LPSolveSolver.Eq, expToEq b)

  fun makeSubst sol =
    map (fn (x,v) => ((Variable, x), TVal (Int v))) sol

  structure L = NominalNameList(VPCCSInstanceRequisites.Term)

  fun unify cs =
  let
    fun isSolv ((bs, ChEq (TName (Channel, a), TName (Channel, b)))::cs) =
      (case (member (Channel, a) bs, member (Channel, b) bs) of
           (false, true) => false
         | (true, false) => false
         | _ => isSolv cs)
      | isSolv [] = true
      | isSolv _ = Err.error "isSolv failed"

    fun composeSubst s (a,b) =
      (map (fn (n, TName (Channel, x)) =>
                    (n, TName (Channel, if a = x then b else x))
             | _ => Err.error "composeSubst failed") s)
      |>
      (fn subst =>
            if (member a (map (fn ((_, x), _) => x) subst))
                then subst
                else ((Channel, a), TName (Channel, b))::subst)

    fun substCs (x,y) ((c as (bs, ChEq (TName (Channel, a),
                           TName (Channel, b))))::cs) =
      (case (member (Channel, a) bs, member (Channel, b) bs) of
            (true, true) => c :: (substCs (x,y) cs)
          | (false, false) =>
              if member (Channel, x) bs
                then c :: (substCs (x, y) cs)
                else
                  let
                    val yy = (Channel, y)
                    val yyy = TName yy
                    val xx = (Channel, x)
                    val n = L.newBasedOn yy bs
                    val nbs = L.swap (yy, n) bs
                    val cnd = ChEq (TName (Channel, a), TName (Channel, b))
                    val cnd' = swapC (n,yy) cnd
                  in
                    if member yy bs
                        then (nbs, substC [(xx,yyy)] cnd') ::
                            (substCs (x,y) cs)
                        else (bs, substC [(xx,yyy)] cnd) ::
                            (substCs (x,y) cs)
                 end
          | _ => Err.error "substCs failed")
      | substCs _ [] = []
      | substCs _ _ = Err.error "subtCs failed 2"

    fun unif s ((bs, ChEq (TName (Channel, a),
                           TName (Channel, b)))::cs) =
      if a = b then unif s cs else
      (case (member (Channel, a) bs, member (Channel, b) bs) of
            (true, true) => LEFT "Different names under restriction"
          | (false, false) => unif (composeSubst s (a, b))
                                   (substCs (a,b) cs)
          | _ => Err.error "unif failed 1")
      | unif s [] = RIGHT s
      | unif _ _ = Err.error "unif failed 2"
  in
    if isSolv cs
        then unif [] cs
        else LEFT "Unsolvable constraint"
  end

  fun lpSolve [] = RIGHT []
    | lpSolve bexps = LPSolveSolver.solve (map bexpToILP bexps)

  fun solver ((bs, CVal false)::cs) e u = LEFT "Encountered false"
    | solver ((bs, CVal true)::cs) e u = solver cs e u
    | solver ((bs, CBool bexp)::cs) e u =
    if exists ((flip member) bs) (bexpSupp bexp)
        then LEFT "One of the Boolean expression is restricted"
        else solver cs (bexp::e) u
    | solver ((eq as (bs, ChEq _))::cs) e u =
        solver cs e (eq::u)
    | solver [] e u =
    (lpSolve e) |>
    (either LEFT
            (RIGHT o makeSubst)) |>
    (either LEFT
            (fn subst => unify u |> (either
                (LEFT)
                (fn us => (RIGHT (subst @ us))) ) ))


  fun solve cs =
  let
    val sol = solver (lineariseConstraint cs) [] []
  in
    case sol of
         LEFT msg => LEFT msg
       | RIGHT sl => RIGHT (sl, ())
  end




  fun solveBisim cs       = Err.undefined ""
end;




structure VPCCSSymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = VPCCSPsiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = VPCCSPsiInstance.Inst
  structure Constraint  = VPCCSSymbolicInstanceRequisites.Constraint
  val var               = VPCCSSymbolicInstanceRequisites.var
end
structure VPCCSSymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = VPCCSPsiInstance.Inst
  structure Constraint = VPCCSSymbolicInstanceRequisites.Constraint
  type solution = (string , (Inst.name * Inst.term) list * Inst.assertion) Either.either
  val solve            = VPCCSSymbolicInstanceRequisites.solve
end;
structure VPCCSSymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = VPCCSPsiInstance
  structure Constraint = VPCCSSymbolicInstanceRequisites.BisimConstraint
  val solve = VPCCSSymbolicInstanceRequisites.solveBisim
end;




structure VPCCSParserPrinterRequisites =
struct
  open VPCCSInstanceRequisites

  structure Parser = Parser(StringStream)
  structure Lex    = PsiLexerParserComb(Parser)
  structure PPA = PrettyPrinterAux(WPrettyPrinter)
  open WPrettyPrinter
  open PPA
  open Parser

  fun printN (Channel, n) = if String.size n = 1 then n else "@" ^ n
    | printN (Variable, n) = n

  fun ppVal (Int i) = text (Int.toString i)
    | ppVal (Bool true) = text "true"
    | ppVal (Bool false) = text "false"

  fun ppBExp (BoolEq (a,b)) =
    ppExp a </sp/> text "=" </sp/> ppExp b

  and ppExp (ExpBool bexp) = ppBExp bexp
    | ppExp (ExpAdd (a,b)) = ppExp a </sp/> text "+" </sp/> ppExp b
    | ppExp (ExpVar n) = text (printN n)
    | ppExp (ExpVal v) = ppVal v


  fun ppT (TExp exp) = ppExp exp
    | ppT (TVal v) = ppVal v
    | ppT (TName n) = text (printN n)

  fun printT m = pretty 80 (ppT m)

  fun printC (CBool bexp) = pretty 80 (ppBExp bexp)
    | printC (CVal v) = pretty 80 (ppVal (Bool v))
    | printC (ChEq (a, b)) =
        pretty 80 (ppT a </sp/> text "<->" </sp/> ppT b)

  fun printA _ = "1"

  val charP = sat Char.isAlpha

  val idP = many1 charP >>=
    return o String.concat o map Char.toString
  val intP = many1 (sat Char.isDigit) >>=
    return o always id o Int.fromString o
        String.concat o map Char.toString

  val ws = many (sat Char.isSpace) >> return ()

  fun singleLowerCharP b1 b2 dataConstr =
    ws >> sat (fn c => b1 <= c andalso c <= b2) >>=
    return o tuple dataConstr o Char.toString

  val charChanP = singleLowerCharP #"a" #"b" Channel
  val charVarP = singleLowerCharP #"o" #"z" Variable

  val boolP =  (str "true" >> return true)
    </choice/> (str "false" >> return false)

  val valP = (intP >>= return o Int)
    </choice/> (boolP >>= return o Bool)

  val varP = charVarP
    </choice/> (charP >>=
        (fn c => idP >>= (fn i => return (Variable, ((Char.toString c) ^ i)))))

  val expP' =
    ((varP >>= return o ExpVar)
        </choice/>
     (valP >>= return o ExpVal))
     </sepby1/> (ws >> str "+" >> ws)

  val expP = expP' >>= (fn (exp::[]) => return exp
                         | (exp::exps) => return
                            (List.foldr ExpAdd exp exps)
                         | _ => Err.error "expP")

  val bExpP =   expP >>=
    (fn a =>    ws >> str "=" >> ws >>
                expP >>=
    (fn b =>    return (BoolEq (a,b))))


  val chP =
    charChanP </choice/>
    (str "@" >> idP >>= return o tuple Channel)

  fun name () =
    chP </choice/> varP

  fun term () =
    (chP >>= return o TName)
    </choice/>
    (valP >>= return o TVal)
    </choice/>
    (expP >>= (fn exp => if null (expSupp exp) 
        then error "Closed expression encountered"
        else return (TExp (exp))))

  fun cond () = (boolP >>= return o CVal)
    </choice/>  (bExpP >>= (fn bexp =>
        if null (bexpSupp bexp)
            then error "Closed condition encountered"
            else  return (CBool bexp)))

  fun assr () = ws >> str "1" >> return ()

  fun parseResult p s =
    case Parser.parse (p ()) (StringStream.make s) of
         Either.RIGHT (r,s) => Either.RIGHT r
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult term s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s

end;


structure VPCCSParserRequisites : PSI_PARSER_REQ =
struct
  structure Psi = VPCCSPsiInstance
  open VPCCSParserPrinterRequisites
  val var = SOME VPCCSSymbolicInstanceRequisites.var
end;
structure VPCCSPrinterRequisites : PSI_PP_REQ =
struct
  structure Inst = VPCCSPsiInstance.Inst
  open VPCCSParserPrinterRequisites
  val var = SOME VPCCSSymbolicInstanceRequisites.var
end;
structure VPCCSCommand = CommandParser(struct
  structure SI           = VPCCSSymbolicInstance
  structure SCS          = VPCCSSymbolicConstraintSolver
  structure SBCS         = VPCCSSymbolicBisimConstraintSolver
  structure PsiParserReq = VPCCSParserRequisites
  structure PPInst       = VPCCSPrinterRequisites
  val useBisim           = false
end);



structure VPCCS = VPCCSCommand;
structure PsiInstance = VPCCS;
