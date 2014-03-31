(* uses pwb/missing,
        pwb/parser,
        pwb/pp,
        pwb/psi,
        pwb/psi-parser,
        pwb/pp-nom,
        pwb/pp-psi,
        pwb/pp-sim,
        pwb/simulator,
        pwb/bisim,
        pwb/graph-viz,
        pwb/pwb-logger
*)


signature PSI_COMMAND_INTERPRETER =
sig
  val start : unit -> unit
end;


functor CommandParser(A: sig
  structure SI           : SYMBOLIC_PSI
  structure SCS          : SYMBOLIC_CONSTRAINT_SOLVER
  structure SBCS         : SYMBOLIC_BISIM_CONSTRAINT_SOLVER
  structure PsiParserReq : PSI_PARSER_REQ
  structure PPInst       : PSI_PP_REQ
  val useBisim : bool

  sharing PsiParserReq.Psi = SI.Psi = SBCS.Psi
  sharing SI.Psi.Inst = SCS.Inst = SBCS.Psi.Inst = PPInst.Inst
  sharing SCS.Constraint.Inst = SBCS.Constraint.Psi.Inst
  sharing SCS.Constraint.AtomSort = SBCS.Constraint.AtomSort = SI.Psi.Inst.Sort

end) : PSI_COMMAND_INTERPRETER  =
struct
  open Missing
  open A

  structure Psi = SI.Psi
  structure Cl = SI.ClEnv.Cl
  structure Guarded = PsiGuarded(SI)
  structure PP = WPrettyPrinter
  structure PsiPP = PrettyPrintPsi(struct
    structure PP     = PP
    structure Psi    = Psi
    structure PPInst = PPInst
  end)
  structure PPNomPsi = PPNominal(struct
    structure PP = PP
    structure Nom = Psi
    val ppAtom = PsiPP.n
  end)
  structure PPClause = PPClause(struct
    structure PP    = PP
    structure Cl    = Cl
    structure PPPsi = PsiPP
  end)
  structure PsiParser = PsiParser(struct
    structure Parser = Parser(ParserStreamIO)
    structure Req    = PsiParserReq
  end)
  structure PsiB = PsiLexerParserComb(PsiParser.Parser)
  structure Env  = SI.ClEnv
  structure Sim  = SymbolicPsiSimulator(SI)
  structure Red  = SymbolicPsiReducer(struct
    structure Sim = Sim
    structure Slv = SCS
  end)
  structure WSim = WeakSymbolicPsiSimulator(SI)
  structure WRed = WeakSymbolicPsiReducer(struct
    structure Red = Red
    structure Tr = WSim.Tr
  end)

  structure Bisim = WeakStrongBisim(struct
    structure Psi  = Psi
    structure Slv  = SCS
    structure SPsi = SI
    structure C    = SBCS.Constraint
  end)

  structure PPSAct = PPStrongAction(struct
    structure PP     = PP
    structure Act    = Sim.Tr.Act
    structure PPInst = PPInst
  end)

  open PsiParser
  open PsiParser.Parser
  open PsiB

  fun getWidth _ = 60

  val simplBisim = ref true;

  datatype command_state = CommandState of
     { env         : Env.env
     , eof         : bool
     }

  fun updateEnv (CommandState {env,eof}) f =
    CommandState
    { env         = f env
    , eof         = eof
    }
  fun getEnv (CommandState {env, ...}) = env
  fun setEof (CommandState {env,eof}) =
    CommandState
    { env         = env
    , eof         = true
    }
  fun unsetEof (CommandState {env,eof}) =
    CommandState
    { env         = env
    , eof         = false
    }
  fun setStatement (CommandState {env,eof}) st =
    CommandState
    { env         = env
    , eof         = false
    }
  fun isEof (CommandState {eof,...}) = eof

  fun freshState () =
    CommandState
    { env = Env.empty
    , eof = false
    }


  fun forall action [] = ()
    | forall action (x::xs) = (action x; forall action xs)


  fun output ctx str =
    (print str;
    print "\n")

  fun nl ctx = print "\n"

  fun pretty ctx doc =
    WPrettyPrinter.pretty (getWidth ctx) doc

  fun outputPP ctx doc =
    print $ pretty ctx doc

  fun outputPPPlain ctx doc =
    print $ PP.plain doc


  fun warning ctx msg =
    (output ctx msg; ctx)

  fun warningPP ctx doc =
  let
    val d = PP.nest 2 $ PP.line
            </PP.join/> PP.text "-- Warning: "
            </PP.join/> doc
  in
    warning ctx $ pretty ctx d
  end


  fun discard (s,p) =
  let
    val c = TextIO.StreamIO.canInput (s,1000000)
  in
    case c of
         NONE => (s,p)
       | SOME k => (snd (TextIO.StreamIO.inputN (s, k)),p)
  end

  (* fun seof (s,p) = TextIO.StreamIO.endOfStream s *)

  fun streamPosStr s =
  let
    val (ln,cn,_) = ParserStreamIO.pos s
  in
    Int.toString ln ^ ":" ^ Int.toString cn
  end
  fun parserFailMsg (Fail m) s = streamPosStr s ^ ": " ^ m
    | parserFailMsg (Error m) s = streamPosStr s ^ ": " ^ m

  fun interactiveStatements ctx prompt statement stEnd stream =
  let
    fun interact ctx stream =
      interactiveStatements ctx prompt statement stEnd stream
    val st = statement ctx
    val _  = (print prompt; print " ")
    val stream = ParserStreamIO.resetPos stream
    val (c,s) =
      (case parse st stream of
         RIGHT (ctx,s) =>
            if stEnd ctx
                then (ctx,s)
                else (interact ctx s)
       | LEFT (msg,s) => (
            print "Syntax Error: "; print (parserFailMsg msg s); print "\n";
            interact ctx (discard s) )
       )
        handle
        (Err.Error msg) => (output ctx ("Error: " ^ msg); interact ctx (discard stream))
          | _ => (output ctx "Error occured"; interact ctx (discard stream))
  in
    (c,s)
  end;



  fun tr () = chr #";"

  fun ran env =
    List.concat (map (Env.find env) (Env.dom env))


  structure PPAux = PrettyPrinterAux(WPrettyPrinter)
  local open WPrettyPrinter open PPAux in

  fun ppAgentSupport ctx agent = PPNomPsi.ppSupp agent
  fun ppClause _ cl            = PPClause.ppClause cl
  fun ppClauseFormals _ cl     = PPClause.ppClauseFormals cl
  fun ppAlpha _ act            = PPSAct.ppAction act

    fun ppAgent ctx a = PsiPP.ppAgent a

  fun ppAgentC ctx a =
    text "  " </join/> (nest 2 (ppAgent ctx a)) </join/> line


  fun ppAlphaSim ctx alpha =
    text "--|" </join/> (ppAlpha ctx alpha) </join/> text "|-->"

  fun ppWAlphaSim ctx alpha =
    case alpha of
         WSim.Tr.Silent => text "======>"
       | _ => text "==|"
            </join/>
                (ppAlpha ctx (case alpha of
                                   WSim.Tr.Tau          => Sim.Tr.Act.Tau
                                 | WSim.Tr.Input    inp => Sim.Tr.Act.Input    inp
                                 | WSim.Tr.Output   out => Sim.Tr.Act.Output   out
                                 | WSim.Tr.BrInput  inp => Sim.Tr.Act.BrInput  inp
                                 | WSim.Tr.BrOutput out => Sim.Tr.Act.BrOutput out
                                 | _ => Err.undefined "Command.ppWAlphasim default" ) )
            </join/> text "|==>"

  fun ppPsi ctx psi = PsiPP.a psi

  fun ppCbrackets ctx doc = text "{|" </sp/> doc </sp/> text "|}"

  fun ppConds [phi] = PsiPP.c phi
    | ppConds phis  =
      text "(" </join/>
	   (sep (text " /\\ ") $ map PsiPP.c phis)
	   </join/> text ")"

  fun ppAtomicConstraint ctx (avec, psi, phis) =
    (if null avec
        then empty
        else text "(new" </sp/>
             commaSep (map PsiPP.n avec) </join/> text ")") </join/>
             (ppCbrackets ctx $
                (if Psi.Inst.Assr.eqData (psi, Psi.Inst.unit)
                    then empty
                    else PsiPP.a psi </sp/> text "|-" </join/> text " ")
                    </join/> ppConds phis)

  fun ppConstraint ctx c =
    group $ sep (text " /\\ " </join/> line) $ map (ppAtomicConstraint ctx) c

  fun ppParens ctx d = text "(" </join/> d </join/> text ")"

  fun breakableSp ctx (a,b) = a </join/> nest 2 (line </join/> b)

  local open Bisim.C in
  fun ppFrame ctx (SBCS.Constraint.Frame.Frame (avec, psi)) =
    (if null avec
        then empty
        else text "(new " </join/> (commaSep (map PsiPP.n avec)) </join/> text ")")
        </join/>
        text "(|" </sp/> PsiPP.a psi </sp/> text "|)"

  fun toSConstr (avec,psi,phi) = (avec,psi,[phi])

  fun ppBisimConstraint ctx True = text "true"
    | ppBisimConstraint ctx False = text "false"
    | ppBisimConstraint ctx (Atomic a) = ppAtomicConstraint ctx (toSConstr a)
    | ppBisimConstraint ctx (Conj (c,c')) =
        group (ppParens ctx $
            ppBisimConstraint ctx c </sp/> text "/\\" </breakableSp ctx/>
            ppBisimConstraint ctx c')
    | ppBisimConstraint ctx (Disj (c,c')) =
        group (ppParens ctx $
            ppBisimConstraint ctx c </sp/> text "\\/" </breakableSp ctx/>
            ppBisimConstraint ctx c')
    | ppBisimConstraint ctx (Imp (c,c')) =
        ppParens ctx $
        ppBisimConstraint ctx c </sp/> text "==>" </breakableSp ctx/>
        ppBisimConstraint ctx c'
    | ppBisimConstraint ctx (TermEq (n,m)) =
        ppCbrackets ctx $ PsiPP.t n </sp/> text "=" </sp/> PsiPP.t m
    | ppBisimConstraint ctx (FreshP (a,p)) =
        ppCbrackets ctx $ PsiPP.n a </sp/> text "#" </sp/> ppAgent ctx p
    | ppBisimConstraint ctx (StImp (f,g)) =
        ppCbrackets ctx $ ppFrame ctx f </sp/> text "<=" </sp/> ppFrame ctx g
    | ppBisimConstraint ctx (Forall (x,c)) =
        text "forall " </sp/> PsiPP.n x </join/> text "." </breakableSp ctx/>
            ppBisimConstraint ctx c
    | ppBisimConstraint ctx (Var x) = PsiPP.n x
  end

  fun ppBisimDisjList ctx l =
    text "<" </join/>
        group (
        sep (text "," </join/> line)
        (map (group o ppBisimConstraint ctx) l) )
            </join/>
    text ">"

  fun ppBisimCNFList ctx l =
    text "[" </join/> nest 2 (
    group (
        line </join/>
        sep (text "," </join/> line)
        (map (ppBisimDisjList ctx) l) ) )
            </join/>
    text "]" </join/> line

  fun ppBisim ctx (c,t) =
    text "Constraint Table:" </breakableSp ctx/>
    ((text "{" </nl/>
       (List.foldr (fn ((i, ((p,q), c) ), d) =>
           text (Int.toString i) </join/> text "." </sp/>
           text "((" </join/> ppAgent ctx p </join/> text ", "
                     </join/> ppAgent ctx q </join/> text "), "
                     </nl/> ppBisimConstraint ctx c
                     </join/> text ")," </join/> line </nl/> d)
           empty (Lst.zip (Lst.enum 1 (length t)) t)))
            </join/> text "}" </join/> line ) </nl/>
    (text "Constraint:" </breakableSp ctx/>
    (ppBisimConstraint ctx c))


  fun ppSol ctx sol =
  let
    fun s sigma = text "[" </join/> commaSep (map (fn (n,t) =>
      PsiPP.n n </sp/> text ":=" </sp/> PsiPP.t t) sigma)
      </join/> text "]"
    fun sl (sigma, psi) = text "(" </join/> commaSep [s sigma, PsiPP.a psi]
      </join/> text ")"
  in
    sl sol
  end

  fun ppSols ctx sols = 
    case sols of
         RIGHT sol => ppSol ctx sol
       | LEFT msg => text "No solution found: " </join/> text msg

  fun ppDescr msg doc =
    text msg </join/> (nest 2 (line </join/> doc))

  fun ppTrans ctx ppAlpha (psi,sourceAgent,alpha,c,sol,agent) =
    ppPsi ctx psi </sp/> text "|>" </join/>
        nest 2 (line </join/>
            ppAlpha ctx alpha </join/>
                nest 2 ( line </nl/>
                ppDescr "Source:" (ppAgent ctx sourceAgent) </nl/>
                ppDescr "Constraint:" (ppConstraint ctx c) </nl/>
                ppDescr "Solution:" (ppSols ctx (RIGHT sol)) </nl/>
                ppDescr "Derivative:" (ppAgent ctx agent)
            ))

  fun ppTransSim ctx ppAlpha number agent =
    (text (Int.toString number)) </join/> text " ---" </join/>
    (nest 2 (line </join/> ppTrans ctx ppAlpha agent))

  fun dumpEnv ctx =
  let
    val e = getEnv ctx
    val clsn = nubBy (op=) (Env.dom e)
    fun pp cl =
      PP.nest 2 (PP.line </PP.join/>
      (ppClause ctx cl) </PP.join/> PP.line)
    val () = forall (fn a =>
        (* TODO: print lets *)
        outputPP ctx (sep line $ map pp (Env.find e a))
    ) clsn
    val () = output ctx "\n"
  in
    ()
  end


  fun drop ctx a =
    updateEnv ctx ((flip Env.remove) a)



  end (* local open WPrettyPrinter open PPAux *)


  fun outputClause ctx clause =
    outputPP ctx ((PP.nest 2 (PP.line </PP.join/> ppClause ctx clause))
                                      </PP.join/> PP.line)




  fun freeVariablesInClause cl = SI.ClEnv.Cl.support cl

  fun clauseArgs () =
                (t "(" >>
                name </sepby/> (t ",") >>=
    (fn xvec => t ")" >>
                return xvec)) </choice/> (return [])


  fun parseClause ctx =
                processConstant () >>=
    (fn a =>    clauseArgs () >>=
    (fn xvec => t "<=" >>
                agent () >>=
    (fn p =>    return (Cl.Clause (a,xvec,p)) )))


  fun parseLetClauses ctx =
                t "def" >> t "{" >>
                ((parseClause ctx) </sepby/> (t ";")) >>=
    (fn cls =>  (t ";" </choice/> return "") >>
                t "}" >> tr () >>
                return cls )


  fun clauseId (a,_,_) = a

  fun checkClauseClosed ctx cl =
  let
    val n = Cl.support cl
  in
    case n of
         [] => RIGHT ()
       | _  => LEFT $
        ppClauseFormals ctx cl
            </PPAux.sp/> PP.text "is not closed, the support is"
            </PPAux.sp/> PP.text "{" </PP.join/>
                            PPAux.commaSep (map PsiPP.n n) </PP.join/>
                         PP.text "}"
  end

  fun invocations (Psi.Nil) = []
    | invocations (Psi.Output _) = []
    | invocations (Psi.Input _) = []
    | invocations (Psi.Tau _) = []
    | invocations (Psi.BrOutput _) = []
    | invocations (Psi.BrInput _) = []
    | invocations (Psi.Case cs) = List.concat $ map (invocations o snd) cs
    | invocations (Psi.Restriction (_,p)) = invocations p
    | invocations (Psi.Parallel (p,q)) = (invocations p) @ (invocations q)
    | invocations (Psi.Replication p) = invocations p
    | invocations (Psi.Assertion _) = []
    | invocations (Psi.Invocation inv) = [inv]


  fun checkInvocation env (a : string,mvec) =
  let
    val clauses = Env.find env a
    val cl = List.find (fn (Cl.Clause (a',xvec,p)) =>
                (a = a') andalso (length xvec = length mvec)) clauses
  in
    maybe
        (LEFT $
            PP.text "There is no clause defined "
                </PPAux.sp/> PsiPP.ppConstant a </PPAux.sp/> PP.text "with arity"
                </PPAux.sp/> PP.text (Int.toString $ length mvec))
        (const (RIGHT ()))
        cl
  end

  fun checkInvocations env (Cl.Clause (a,xvec,p)) =
    lefts $ map (checkInvocation env) (invocations p)

  (*
  * Check if every call is defined in the environment and in the let {..}
  * Warn if some things will be redefined
  * Check if all clauses are closed
  *)

  fun checkDrop env a =
    case Env.find env a of
         [] => RIGHT ()
       | _  => LEFT $ (PP.text "redefined clause" </PPAux.sp/> (PsiPP.ppConstant a))


  fun checkDroped env cls =
    map (checkDrop env)
        (nubBy (op=) $ map (fn (Cl.Clause (a,_,_)) => a) cls)


  fun ppInvocation (a,mvec) =
    (PsiPP.ppConstant a)
              </PP.join/> PP.text "<"
              </PP.join/> PPAux.commaSep (map PsiPP.t mvec)
              </PP.join/> PP.text ">"

  fun checkGuarded ctx env (inv as (a,mvec)) =
    case Guarded.guarded env (Psi.Invocation inv) of
         true  => RIGHT ()
       | false => LEFT $
        PP.text "Invocation" </PPAux.sp/> ppInvocation inv
                             </PPAux.sp/> PP.text "is not guarded."

  fun checkGuardedInvocations ctx env (Cl.Clause (a,xvec,p)) =
    lefts $ map (checkGuarded ctx env) (invocations p)


  fun letClauses ctx cls =
  let
    val env  = getEnv ctx
    (* drop all the read clauses from the environment *)
    val dropedEnv = List.foldr (fn (Cl.Clause (a,_,_),e) => Env.remove e a) env cls
    (* extend the environment with read clauses *)
    val env' = List.foldr (fn ((cl as Cl.Clause (a,_,_)),e) => Env.extend e a cl)
                    dropedEnv cls
    val inv = List.concat $ map (checkInvocations env') cls
    val closed = lefts $ map (checkClauseClosed ctx) cls
    val droped = lefts $ checkDroped env cls
    val guarded = List.concat $ map (checkGuardedInvocations ctx env') cls
    fun warnings docs =
        forall (warningPP ctx) docs
               (* (map (PP.join/>PP.line) docs) *)
    val newCtx = updateEnv ctx (const env')
    val _ = if length cls > 1 then output newCtx "\ndef {" else ()
    val _ = forall (fn c => (outputClause newCtx c; output ctx ";")) cls
    val _ = if length cls > 1 then output newCtx "};" else ()
    val _ = warnings (droped @ closed @ inv @ guarded)
  in
    return newCtx
  end

  fun clauseC ctx = parseClause ctx >>= letClauses ctx o sngl
  fun letClausesC ctx = parseLetClauses ctx >>= letClauses ctx



  (* TODO: nicer printout of an environment *)
  fun envC ctx =
                t "env" >> tr () >>=
    (fn _ =>    (dumpEnv ctx; return ctx))



  fun agentSupport ctx =
                t "n" >>
                t "(" >>
                agent () >>=
    (fn a =>    t ")" >> tr () >>
                (outputPP ctx (PP.text "  " </PP.join/>
                              (ppAgentSupport ctx a
                              </PP.join/> PP.line));
                return ctx)
    )


  fun boolResponse ctx =
    (fn t =>    (outputPP ctx (PP.text (if t then "true" else "false")
                               </PP.join/> PP.line);
                return ctx ))

  fun agentGuarded ctx =
                t "guarded" >> t "(" >> agent () >>=
    (fn a =>    t ")" >> tr () >>
                return (Guarded.guarded (getEnv ctx) a) >>=
                boolResponse ctx)


  fun parseAssignment ctx =
                name >>=
    (fn x =>    t ":=" >>
                term >>=
    (fn t =>    return (x,t)
    ))


  fun parseSubst ctx =
                t "[" >> parseAssignment ctx </sepby1/> t "," >>=
    (fn xts =>  t "]" >>
                return xts)

  fun agentSubst' ctx =
                agent () >>=
    (fn a =>    many1 (parseSubst ctx) >>=
    (fn sigmas => tr () >>
                return $ Lst.foldl (flip Psi.subst) a sigmas))

  fun agentSubst ctx =
                agentSubst' ctx >>=
    (fn a =>    (outputPP ctx (ppAgentC ctx a); return ctx))

  fun agentAgent ctx =
                agent () >>=
    (fn a =>    tr () >>=
    (fn _ =>    (outputPP ctx (ppAgentC ctx a); return ctx)))


  fun agentAlphaEq ctx =
                agent () >>=
    (fn a =>    t "=" >>
                agent () >>=
    (fn b =>    tr () >>=
    (fn _ =>    return (Psi.eqData (a,b) ) >>=
                boolResponse ctx)))

  fun opAgent ctx =
                agentSupport ctx
    </choice/>  agentSubst ctx
    </choice/>  agentGuarded ctx
    </choice/>  agentAlphaEq ctx
    </choice/>  agentAgent ctx

  fun agentC ctx =
                (t "agent" </choice/> return "") >> opAgent ctx



  fun inputEnd ctx = ws >> eof ctx >>= return

  fun redundantDelim ctx = ws >> tr () >> return ctx

  fun dropC ctx =
                t "drop" >> processConstant () >>=
    (fn n =>    ws >> tr () >>
                return (drop ctx n))



  fun number () =
                sat (fn c => c <> #"0" andalso Char.isDigit c) >>=
    (fn a =>    many (sat Char.isDigit) >>=
    (fn r =>    maybe
                    (error "Could not parse integer")
                    return
                    (Int.fromString (String.implode (a :: r)))
    ))


  val  enum = Lst.enum

  fun trS () = singleWS

  fun numCommand ctx =
                ws >> number () >>=
    (fn n =>    trS () >> return n)


  fun onlySolv trs =
    List.filter (fn (tr as (_,_,_,s,_)) =>
        s |> either (const false) (const true)) trs

  fun stepAgentC
        reduce
        ppAlpha
        (wctx as (ctx,((initPsi,agent)::agents))) =
  let
    fun addAssertion psi agent = (Psi.Parallel(Psi.Assertion psi,agent))
    fun stripAssertion (Psi.Parallel (Psi.Assertion _, agent)) = agent
      | stripAssertion agent = agent

    val tr = reduce (getEnv ctx) (addAssertion initPsi agent) Sim.Constraint.unit
    val transitions = onlySolv tr

    val transitions = transitions |> map
        (fn (p, alpha, c, RIGHT (subst, psi), p') =>
                (Psi.Inst.compose (initPsi, psi), stripAssertion agent, alpha, c, (subst,psi), Psi.subst (stripAssertion p') subst)
          | _ => Err.undefined "Command.stepAgentC.transitions LEFT")

    val n        = List.length transitions
    val nTrans   = zip (enum 1 n) transitions

    fun stransAgent (psi,agent',alpha,c,sol,agent) = (psi,agent)
    fun select x = stransAgent $ List.nth (transitions, x - 1)

    val _ = output ctx ((Int.toString n) ^ " possible derivative(s)")
    val _ =
      forall
        (fn (n, trans) =>
            (()
            ; outputPP ctx (ppTransSim ctx ppAlpha n trans)
            ; nl ctx; nl ctx
            )
        ) nTrans
  in
    (           numCommand ctx >>=
    (fn x =>    nofail (if x - 1 < n
                    then return (ctx,((select x)::(initPsi,agent)::agents))
                    else error "No such agent") ) )
    </choice/>
                (ws >> str "b" >> nofail (trS () >>
                delayed (fn () =>
                (case agents of
                      [] => Parser.error "There are no more agents to backtrack to"
                    | _ => return (ctx,agents)))))
    </choice/>
                (  ((ws >> str "q" >> trS ()) </choice/> (ws >> eof ())) >>
                return (setEof ctx,[])
                )
  end
    | stepAgentC _ _ _ =
        Err.error "sstepAgentC called without giving an agent"


  fun sstepAgentC wctx =
    stepAgentC Red.reduce ppAlphaSim wctx

  fun wsstepAgentC wctx =
    stepAgentC WRed.reduce ppWAlphaSim wctx


  fun symbolicStepC ctx name stepF =
                t name >> agent () >>=
    (fn a =>    ws >> tr () >>
                direct (fn stream =>
                    let
                      val () = output ctx "Type <num> for selecting derivative, b - for backtracking, q - quit"
                      val (_,s) = interactiveStatements
                                        (ctx, [(Psi.Inst.unit,a)])
                                        (name ^ ">")
                                        stepF
                                        (isEof o fst)
                                        stream
                    in
                      RIGHT (ctx,s) (* unmodified ctx *)
                    end
                )
    )

  fun sstepC ctx =
    symbolicStepC ctx "sstep" sstepAgentC

  fun wsstepC ctx =
    symbolicStepC ctx "wsstep" wsstepAgentC


  fun disjToList (Bisim.C.Disj (c,c')) = disjToList c @ disjToList c'
    | disjToList c = [c]

  fun cnfToList (Bisim.C.Conj (c,c')) = cnfToList c @ cnfToList c'
    | cnfToList c = [disjToList c]


  fun checkSymbolicBisim ctx bisim (p,q) =
  let
    val b = bisim (getEnv ctx) p q
    val res = SBCS.solve (Tpl.fst b)
  in
     (output ctx "\n\n";
     outputPP ctx $ ppSols ctx res;
     output ctx "\n"; ()
     )
  end


  fun bisimC opString bisim ctx =
                agent () >>=
    (fn p =>    t opString >>
                agent () >>=
    (fn q =>    tr () >>
                (if useBisim
                   then checkSymbolicBisim ctx bisim (p,q)
                   else output ctx "NOTE: (Bi)simulation checking is not available.";
                   return ctx) ))


  structure Viz = PsiTransitionGraphViz(struct
    structure Sim = Sim
    structure Slv = SCS

    fun showP proc = PP.pretty 40 (PsiPP.ppAgent proc)
    fun showC constr = PP.pretty 40 (ppConstraint (freshState ()) constr)
    fun showA act = PP.pretty 40 (PPSAct.ppAction act)
    fun showS sol = PP.pretty 40 (ppSol (freshState ()) sol)
  end)


  val intP = many1 (sat Char.isDigit) >>=
    return o always id o Int.fromString o String.concat o map Char.toString

  fun transGraphC ctx =
    (t "transgraph" >> ws >> intP >>=
    (fn lvl => agent () >>=
    (fn p => tr () >>
        (Viz.viz (getEnv ctx) p lvl "graph-viz.dot" ;
        return ctx))))

  fun toggleSimpC ctx =
    ((t "toggleSimp" >> tr ()) >>= (fn _ => ((simplBisim := not (!simplBisim)); return ctx)))


  fun exitC ctx =
    ((t "exit" >> tr () >> return ctx)
    </choice/>
    (ws >> eof ctx)) >>=
    (fn _ => (return (setEof ctx)))


  val helpString =
    "help                      - prints this help message\n" ^
    "env                       - prints the current process environment\n" ^
    "drop <procname>           - removes clauses from the environment with <procname>\n" ^
    "input \"filename\"          - reads commands from a file filename\n" ^
    "sstep <proc>              - enters the symbolic simulator for the process <proc>;\n" ^
    "                            enter a number to select an agent to follow, b to backtrack, and q to exit\n" ^
    "wsstep <proc>             - enters the weak symbolic simulator; accepts the same commands as sstep\n" ^
    "<proc> ~ <proc>           - computes the weak bisimulation\n" ^
    "<proc> ~w <proc>          - computes the weak bisimulation (alias for the above)\n" ^
    "<proc> ~s <proc>          - computes the strong bisimulation\n" ^
    "<proc> <w <proc>          - computes the weak simulation\n" ^
    "<proc> <s <proc>          - computes the strong simulation\n" ^
    "transgraph <depth> <proc> - computes the transition graph for <proc>, follows at most <depth> transitions\n" ^
    "                            writes this graph to graphviz.dot in the current directory\n" ^
    "agent <proc>              - pretty prints the process <agent>\n" ^
    "def { <procname>(<formals>) <= <proc>; ... } - adds to the environment the clauses specified\n" ^
    "<procname>(<formals>) <= <proc> - the same as above, but only for one clause"

  fun simpleWS () = many (sat Char.isSpace)
  fun simpleWSNoNL () = 
    many (sat (fn #"\n" => false | c => Char.isSpace c))

  fun helpC ctx =
    ((simpleWS () >> str "help" >> 
     simpleWSNoNL () >> chr #"\n" >>= (fn _ =>
        (output ctx helpString ; return ctx))))

  fun commands () =
    helpC                          :: 
    exitC                          :: 
    clauseC                        :: 
    letClausesC                    :: 
    redundantDelim                 :: 
    envC                           :: 
    dropC                          :: 
    inputC                         :: 
    sstepC                         :: 
    wsstepC                        :: 
    agentC                         :: 
    bisimC "~s" Bisim.Strong.bisim :: 
    bisimC "~w" Bisim.Weak.bisim   :: 
    bisimC "<s" Bisim.Strong.sim   :: 
    bisimC "<w" Bisim.Weak.sim     :: 
    bisimC "~" Bisim.Weak.bisim    :: 
    toggleSimpC                    :: 
    transGraphC                    :: 
    []

  and statement (ctx : command_state) =
    List.foldr choice zero (map (fn c => c ctx) (commands ()))

  and inputFile ctx n =
  let
    val f = TextIO.openIn n
    val s = ParserStreamIO.make f

    fun eof ctx =
      if isEof ctx
        then return (unsetEof ctx)
        else error "-- End of input unexpected"

    fun script ctx =    (eof ctx)
        </choice/>      (statement ctx >>= (fn c => nofail $ script c))
  in
    parse (script ctx) s
  end

  and inputC ctx =
                t "input" >> PsiB.literal >>=
    (fn n =>    ws >> tr () >>=
    (fn _ =>    case (inputFile ctx n) of
                       RIGHT (ctx,s) => return ctx
                     | LEFT (err,s)  => error (parserFailMsg err s)
    ))


  fun repl ctx stream =
    interactiveStatements
        ctx
        "psi>"
        statement
        isEof
        stream


  fun captureStdIn () = ParserStreamIO.make TextIO.stdIn

  fun start' () =
  let
    val state = freshState ()
    val stream = captureStdIn ()
  in
    repl state stream
  end

  fun start () =
  let
    val _ = PwbLog.pushLoggerStdOut "Bisim"
    val _ = start' ()
  in
    ()
  end

end;

