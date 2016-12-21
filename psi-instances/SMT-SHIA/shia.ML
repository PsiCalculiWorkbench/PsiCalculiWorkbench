(*
    uses pwb/workbench,
         pwb/missing-io,
         pwb/constraint-solvers/pwb-smt
*)

structure MissingExtra =
struct
  open Missing

  fun fmt' ([], _) = []
    | fmt' (fmts, []) = fmts
    | fmt' (f::fmts, v::vals) =
    if f = "$"
    then v::(fmt' (fmts, vals))
    else f::(fmt' (fmts, v::vals))

  fun fmt fm vals =
    String.concat $
        fmt' (map String.str (String.explode fm), vals)
end;

structure ExternalSmt :
sig
  datatype sat = SAT | UNSAT | UNKNOWN | TIMEOUT
  val sat : string -> sat
end =
struct
  open Missing
  open MissingExtra
  open MissingIO
  open Thread
  datatype sat = SAT | UNSAT | UNKNOWN | TIMEOUT

  val verb = 3 (* debug printout verbosity level *)

  fun debug n =
      if n <= verb then
          curry TextIO.output $ TextIO.stdErr
      else
          const ()

  val timeout = 10 (* seconds *)
  val hardtimeout = 11 (* seconds *)

  (* Try the following solvers concurrently *)
  type solver = {name:string, bin:string,opts:string list,preamble:string}
  val solvers =
      [{name="Z3",
        bin="/usr/bin/z3",
	opts=["-smt2", "-in", fmt "-T:$" [Int.toString timeout]],
	preamble=""
       },
(*       {name="CVC4",
        bin="/usr/bin/cvc4",
	opts=["--lang=smt2", fmt "--tlimit=$" [Int.toString $ timeout*1000]],
	preamble="(set-logic ALL_SUPPORTED)"
       },*)
       {name="CVC4 (finite-model-find)",
        bin="/usr/bin/cvc4",
	opts=["--lang=smt2", "--finite-model-find", fmt "--tlimit=$" [Int.toString $ timeout*1000]],
	preamble="(set-logic ALL_SUPPORTED)"
       }(*,

       {name="PCVC4",
        bin="/usr/bin/pcvc4",
	opts=["--lang=smt2",
	      "--threads=2",
	      fmt "--tlimit=$" [Int.toString $ timeout*1000],
	      "--thread0=--finite-model-find"
	     ],
	preamble="(set-logic ALL_SUPPORTED)"
       }       *)
]
       
  val cache = HashArray.hash 400 : sat HashArray.hash
  val maxfailhash = ref 100;
  val maxhash = ref 300;


  fun afterSublist l [] =
      SOME l
    | afterSublist (f::r) (f'::r') =
      if f = f' then
	  afterSublist r r'
      else NONE
    | afterSublist [] _ = NONE

  fun splitAroundSublist [] [] =
      SOME ([],[])
    | splitAroundSublist [] _ =
      NONE
    | splitAroundSublist (l as f::r) l' =
      (case afterSublist l l' of
	   SOME l'' => SOME ([],l'')
	 | NONE =>
	   (case splitAroundSublist r l' of
		SOME (r,l') => SOME (f::r,l')
	      | NONE => NONE))

  fun replaceFirst l s t =
      case splitAroundSublist l s of
	  NONE => NONE
	| SOME (l,l') => SOME(l @ t @ l')
				     
  fun replaceAll l s t =
      case replaceFirst l s t of
	  NONE => l
	| SOME l' => replaceAll l' s t
				
  fun deBruijnifyArgs (#"("::r) n =
      (case splitAroundSublist r (explode " ") of
	   SOME (l,l') =>
	   (case splitAroundSublist l' (explode ")") of
		SOME (l',l'') =>
		let
		    val new = explode("deBruijnVar" ^ Int.toString n)
		    val rl = deBruijnifyArgs (replaceAll l'' l new) (n+1)
		in
		    List.concat [[#"("],new,[#" "],l',[#")"],rl]
		end
	      | NONE => raise Domain)
	 | NONE => raise Domain)
    | deBruijnifyArgs (#")"::r) n = #")"::deBruijnify r n
    | deBruijnifyArgs (f::r) n = f::deBruijnifyArgs r n
    | deBruijnifyArgs _ _ = raise Domain
				      
  and deBruijnify l n = 
      case splitAroundSublist l (explode "forall (") of
	  NONE => l
	| SOME (l,l') =>
	  l @ (explode "forall (") @ deBruijnifyArgs l' n
						     
  fun deBruijn s =
      String.tokens (fn x => x = #"\n") s |> map (fn x => implode(deBruijnify (explode x) 0)) |> join "\n"

  fun runSolver smtLib (solver:solver) proc =
      let
          val () = Thread.setAttributes [Thread.InterruptState Thread.InterruptDefer];
	  val () = proc := SOME(Unix.execute (#bin solver, #opts solver))
          val p = valOf $ ! proc
	  val (inp,outp) = Unix.streamsOf p
          val () = Thread.setAttributes [Thread.InterruptState Thread.InterruptAsynchOnce];
      in
          let
	      val () = TextIO.output (outp, #preamble solver)
	      val () = TextIO.output (outp, "\n")
	      val () = TextIO.output (outp, smtLib)
	      val () = TextIO.output (outp, "(check-sat)\n")
	      val () = TextIO.closeOut outp
	      val r = getOpt(TextIO.inputLine inp,"")
              val _ = TextIO.closeIn inp;
	      val _ = Unix.kill (p,Posix.Signal.term)
                  handle (exn as (OS.SysErr _)) => debug 1 $ PolyML.makestring exn^"\n"
	      val _ = Unix.reap p
	  in
	      case r of
		  "sat\n" => SAT
		| "unsat\n" => UNSAT
		| "unknown\n" => UNKNOWN
		| "timeout\n" => TIMEOUT
		| _ => error (fmt "$ gave something unexpected: $" [#name solver,r])
	  end handle Thread.Interrupt => (
                     Thread.setAttributes [Thread.InterruptState Thread.InterruptDefer];
                     TextIO.closeOut outp;
                     TextIO.closeIn inp;
		     Unix.kill (p,Posix.Signal.kill) handle exn => debug 1 $ PolyML.makestring exn^"\n";
		     Unix.reap p;
                     Thread.setAttributes [Thread.InterruptState Thread.InterruptSynch];
		     raise Thread.Interrupt
	             )
      end 

  fun runSolverThread cv lock res proc smtLib (solver:solver) =
      (case runSolver smtLib solver proc of
	   result => (
	   Thread.setAttributes [Thread.InterruptState Thread.InterruptSynch];
	   Mutex.lock lock;
	   res := SOME result;
	   Mutex.unlock lock;
	   Thread.testInterrupt();
	   ConditionVar.signal cv           
      )) handle Thread.Interrupt => ()
	      | exn => debug 1 $ PolyML.makestring exn^"\n";

  fun through f a =
      (f a; a)

  fun runTimer lock cv timeout () =
      (OS.Process.sleep(Time.fromSeconds hardtimeout);
       Thread.setAttributes [Thread.InterruptState Thread.InterruptSynch];
       Mutex.lock lock;
       timeout := true;
       Mutex.unlock lock;
       Thread.testInterrupt();
       ConditionVar.signal cv)

  fun maybeInterrupt thread =
      if Thread.isActive thread then
          Thread.interrupt thread
      else
          ()

  fun runSolvers smtLib =
      let
          val atts = Thread.getAttributes()
          val _ = Thread.setAttributes [Thread.InterruptState Thread.InterruptSynch];
	  val n = ref(length solvers)
	  val cv = ConditionVar.conditionVar ()
	  val timeout = ref false
	  val lock = Mutex.mutex ()
	  val refs = List.map (fn _ => ref NONE) solvers
          val procs =  List.map (fn _ => ref NONE) solvers
	  val result = ref UNKNOWN
	  val timer = Thread.fork(runTimer lock cv timeout,
                                  [Thread.InterruptState Thread.InterruptAsynch])
	  val workers = ListPair.map
                            (fn ((r,p),s) =>
                                Thread.fork ((fn _ => runSolverThread cv lock r p smtLib s),
                                             [Thread.InterruptState Thread.InterruptAsynchOnce]))
                            (Lst.zip refs procs,solvers)
          val overtimebadness = ref 0
      in
	  while !n > 0 do (
	      ConditionVar.wait(cv,lock);
	      if not(!timeout) then (
		  debug 2 $ PolyML.makestring refs;
		  case List.find (fn x => !x = SOME SAT orelse !x = SOME UNSAT) refs of
		      SOME res =>
		      (
			List.app (fn t => maybeInterrupt t handle (Thread _) => ()) workers;
			n := 0;
			result := (valOf o !) res)
		    | NONE =>
		      (
			n := (List.filter (not o isSome o !) refs |> length))
	      ) else (
		  debug 1 ("\n== HARD TIMEOUT== \n");
		  n := 0;
		  List.app (fn t => maybeInterrupt t handle (Thread _) => ()) workers;
		  result := TIMEOUT)
	  );
	  (maybeInterrupt timer handle (Thread _) => ());
	  (case !result of
	       UNKNOWN =>
	      if List.exists (fn x => !x = SOME TIMEOUT) refs then
		  TIMEOUT
	      else
		  UNKNOWN
	    | result => result)
	  before
	  (if null solvers then
	       ()
	   else
	      Mutex.unlock lock;
           Thread.setAttributes atts;
           (* Join with worker threads to prevent multiple instances of the same
              external solver from running concurrently.

              (CVC4 in particular gives unexpected results when this happens.)

              Worker threads that persist in not terminating are interrupted,
              then killed if they persist further.
            *)
           while (not o null o List.filter Thread.isActive) workers do
               (if !overtimebadness >= 100 then
                    List.app (fn t => Thread.kill t handle (Thread _) => ()) workers
                else
                    if !overtimebadness >= 10 then
                        (List.app (fn t => maybeInterrupt t handle (Thread _) => ()) workers;
                         overtimebadness := !overtimebadness +1)                        
                    else
                        overtimebadness := !overtimebadness +1;
                OS.Process.sleep $ Time.fromMilliseconds 10);
           List.app (Option.app (ignore o Unix.reap) o !) procs
          )
      (* List.app (fn t => Thread.kill t handle _ => ()) (timer::workers);*)
      end
	  
  fun sat smtLib =
  let
      val db = deBruijn smtLib
      fun toCache result =
          if result = TIMEOUT orelse result = UNKNOWN then
	      if !maxfailhash <= 0 then
	          ()
	      else
	          (HashArray.update(cache, db, result);
	           debug 1 "\n== CACHED FAILURE ==\n";
	           debug 1 db;
	           maxfailhash := !maxfailhash - 1)
          else
	      if !maxhash <= 0 then
	          ()
	      else
	          (HashArray.update(cache, db, result);
	           debug 1 "\n== CACHED SUCCESS ==\n";
	           debug 1 db;
	           maxhash := !maxhash - 1)

  in
      case HashArray.sub (cache,db) of
	  NONE =>
	  through (fn x => if x = UNKNOWN then
                               (debug 1 "\n\n== UNKNOWN ==\n\n"; debug 1 smtLib)
			   else
                               toCache x)
		  $ runSolvers smtLib
	| SOME result => (debug 2 "\n\n== CACHE HIT ==\n\n";result)
  end before debug 3 "\n== NEXT ==\n"
end

(* PolyML.print_depth 2; *)
(* PolyML.print (ExternalSmt.sat "(assert true) "); *)




structure NominalAlgebra =
struct
  open Missing
  open MissingExtra

  (*
  Sorts
    a, b, c, d

  Symbols

    f : (a,...,z) => x
    ...
    g : () => x

  *)

  type name = string * string

  (* Signature *)
  datatype spec
    = S of string list * string list * (string * string list * string) list * (string * string list * string) list * tm list
  and tm = Tm of string * tm list
         | Va of name

  val emptySpec = S ([],[],[],[],[])
  fun joinSpecs (S (sorts,csorts,syms,consts,ax)) (S (sorts',csorts',syms',consts',ax')) = S (sorts @ sorts', csorts @ csorts',syms @ syms', consts @ consts', ax @ ax')
  fun specSorts (S (sorts,csorts,_,_,_)) = sorts@csorts
  fun specVSorts (S (sorts,_,_,_,_)) = sorts
  fun specCSorts (S (_,csorts,_,_,_)) = csorts
  fun specSyms (S (_,_,syms,consts,_))   = syms@consts
  fun specUSyms (S (_,_,syms,_,_))   = syms
  fun specConsts (S (_,_,_,consts,_))   = consts
  fun specAx (S (_,_,_,_,ax))   = ax

  fun addSort s (S (sorts,csorts,syms,consts,ax))  = S (s::sorts,csorts,syms,consts,ax)
  fun addCSort s (S (sorts,csorts,syms,consts,ax))  = S (sorts,s::csorts,syms,consts,ax)
  fun addSym sym (S (sorts,csorts,syms,consts,ax)) = S (sorts,csorts,sym::syms,consts,ax)
  fun addConst const (S (sorts,csorts,syms,consts,ax)) = S (sorts,csorts,syms,const::consts,ax)
  fun addAx a (S (sorts,csorts,syms,consts,ax)) = S (sorts,csorts,syms,consts,a::ax)


  fun populateSpecWithPredef spec =
    spec                                        |>
    addSort "bool"                              |>
    addSym ("and", ["bool","bool"], "bool")     |>
    addSym ("implies", ["bool","bool"], "bool") |>
    addSym ("or", ["bool","bool"], "bool")      |>
    addSym ("not", ["bool"], "bool")            |>
    addSort "i"                                 |>
    addSym ("S", ["i"], "i")                    |>
    addSym ("Z", [], "i")                       |>
    addSym ("true", [], "bool")                 |>
    addSym ("false", [], "bool")                |>
    addSym ("Add", ["i","i"], "i")              |>
    addSym ("Sub", ["i","i"], "i")              |>
    addSym ("Dec", ["i"], "i")                  |>
    addSym ("LT", ["i", "i"], "bool")


  (* Specially treated sorts *)
  val intSort = "i"
  val equalitySymbols = ["iEq", "dEq", "cEq"]
  val channelSort = "tch"


  fun swap_name (a,b) n =
    if a = n then b
    else if b = n then a
    else n


  datatype pr = Pr of string * tm list

  fun fv_tm (Va x) = [x]
    | fv_tm (Tm (_,tms)) = Lst.flatmap fv_tm tms

  fun fv_pr (Pr (_,tms)) = Lst.flatmap fv_tm tms

  fun swap_tm pi (Va x) = Va (swap_name pi x)
    | swap_tm pi (Tm (name,tms)) = Tm (name, map (swap_tm pi) tms)

  fun swap_pr pi (Pr (name, tms)) = Pr (name, map (swap_tm pi) tms)

  fun subst_tm sigma (Va x) =
    (case List.find (fn (x', tm) => x = x') sigma of
         SOME (_,tm) => tm
       | NONE => Va x)
    | subst_tm sigma (Tm (name, tms)) = Tm (name, map (subst_tm sigma) tms)

  fun subst_pr sigma (Pr (name, tms)) = Pr (name, map (subst_tm sigma) tms)

  fun isNone NONE = true
    | isNone _    = false


  fun nameSort (_,s) = s

  fun sortOfSym name spec =
    case List.find (fn (s,_,_) => s = name) (specSyms spec) of
         SOME (_,args,ret) => (args,ret)
       | NONE => Err.error ("Unknown function symbol: " ^ name)


  exception SortCheckFail of string

  fun inferSort sgn (Va (name,sort)) = sort
    | inferSort sgn (Tm ("=", (t1::t2::_))) = (* = is polymorphic *)
        let
          val s1 = inferSort sgn t1
          val s2 = inferSort sgn t2
        in
          if s1 = s2
            then "bool"
            else raise SortCheckFail ("Eq sorts don't match")
        end
    | inferSort sgn (Tm (name, tms)) =
    let
      val (args, ret) = sortOfSym name sgn
      val argSorts = map (inferSort sgn) tms
    in
      if length args = length argSorts andalso
        Lst.all (op=) (zip argSorts args)
      then
        ret
      else
        raise SortCheckFail (fmt "The argument sort of '$' is '$' but inferred '$'"
                                 [name, join "," args, join "," argSorts])
    end


  structure Parser = AbstractParser
  structure Lex = PsiLexerParserComb(Parser)
  open Parser
  open Lex

  fun parseName spec =
    List.foldr choice zero
      (map (fn s => Lex.ws >> str s >> Lex.identifier >>= (fn n => return (n,s)))
           (specSorts spec))

           (*
  val intP = many1 (sat Char.isDigit) >>=
    return o always id o Int.fromString o String.concat o map Char.toString
    *)

  fun toPA 0 = Tm ("Z", [])
    | toPA n = Tm ("S", [toPA (n-1)])

  fun intFromString str =
    case Int.fromString str of
         NONE => error (fmt "Can't parse an integer from this '$'" [str])
       | SOME i => i

  fun parseInt () =
    many1 (sat Char.isDigit) >>= (fn is =>
    return (toPA (intFromString (String.implode is))) )


  fun maybeP p =
    (p >>= return o SOME) </choice/> (return NONE)

  fun notNl c = c <> #"\n"
  fun cmnt () =
    str "#" >>
    many ((sat notNl) </choice/> (eof () >> zero) ) >>
    (eof () </choice/> (item >> return ()))

  fun parseSym spec =
        (List.foldr choice zero
          (map (fn (name,args,_) =>
                Lex.stok name >>= (fn _ => nofail
                (if length args = 0
                    then return (Tm (name, []))
                    else
                        Lex.stok "(" >>
                        (delayed (fn () => parseTm spec)) </sepby/> Lex.stok "," >>=
                        (fn args =>
                        Lex.stok ")" >>
                        return (Tm (name, args))
                        )) )
             )
            (specSyms spec)))

  and parseTm' spec =
        (Lex.ws >> parseInt ())
    </choice/>
        parseSym spec
    </choice/>
        (parseName spec >>= return o Va)
    </choice/>
        (item >>= (fn e => Parser.fail ("Unknown term " ^ Char.toString e)))

  and parseTmGroup spec = 
      (Lex.ws >> str "(" >>= (fn _ =>  parseTm spec >>= 
                             (fn t => Lex.ws >> str ")" >>
                             return t)))
    </choice/>
      parseTm' spec

  and parseTm spec =
      (parseTmGroup spec >>= (fn tm1 =>
      maybeP (Lex.ws >> str "=" >> parseTm spec) >>=
      (fn NONE => return tm1
        | SOME tm2 => return (Tm ("=", [tm1,tm2])))))

  fun ws' () =
    ((sat Char.isSpace) >> return ()) </choice/> (cmnt ())
  fun ws () = many (ws' ())
  fun ws1 () = many1 (ws' ())

  fun parseTermSpec () =
    ws () >> identifier >>= (fn name =>
    nofail (
    stok ":" >>
    nofail (
    stok "(" >>
    (identifier </sepby/> stok ",") >>= (fn argSorts =>
    nofail (
    stok ")" >> stok "=>" >>
    identifier >>= (fn resultSort =>
    return (name, argSorts, resultSort)
    ))))))

  fun parseSort () =
    ws () >> identifier >>= (fn s =>
        if s = "Symbols"
            then fail ("Symbols is a reserved word")
            else return s
    )

    (*
  fun parseSpec () =
    ws () >> stok "Sorts" >> ws () >> nofail (
    many (delayed parseSort) >>= (fn sorts =>
    ws () >> stok "Symbols" >> ws () >> nofail (
    many (parseTermSpec ()) >>= (fn termSpecs => nofail (
    ws () >> eof "" >>
    return (S (sorts,termSpecs))
    )))))
    *)

  fun parseAxioms spec =
    ws () >> parseTm spec


  fun parseSpec () =
    ws () >> stok "@Sorts" >> ws () >> nofail (
    many (delayed parseSort) >>= (fn sorts =>
    ws () >> stok "@CSorts" >> ws () >> nofail (
    many (delayed parseSort) >>= (fn csorts =>
    ws () >> stok "@Symbols" >> ws () >> nofail (
    many (parseTermSpec ()) >>= (fn termSpecs => nofail (
    ws () >> stok "@Constructors" >> ws () >> nofail (
    many (parseTermSpec ()) >>= (fn termConsts => nofail (
    ws () >> stok "@Axioms" >> ws () >> nofail (
    let
      val spec = joinSpecs (populateSpecWithPredef emptySpec) (S (sorts, csorts, termSpecs, termConsts, []))
    in
        many (parseAxioms spec) >>= (fn axioms => nofail (
        ws () >> eof "" >>
        return (S (sorts,csorts,termSpecs,termConsts,axioms))
    ))
    end)))))))))))

  fun checkSpec spec  =
  let
    val _ =
      (* TODO: accept any bool term *)
        map (fn (t as (Tm ("=", [t1,t2]))) => inferSort spec t
	      | (t as (Tm ("not", [Tm("=",[t1,t2])]))) => inferSort spec t
              | _ => raise SortCheckFail ("Only axioms on equality and inequality are allowed")) (specAx spec)
  in
    spec
  end

  fun parseSpecFromFile file =
    MissingIO.withOpenFile file (fn (ins) =>
    let
      val ps = AbstractParserStream.ioToStream ins
    in
      case parse (parseSpec ()) ps of
           RIGHT (r,s) =>
            checkSpec (joinSpecs (populateSpecWithPredef emptySpec) r)
         | LEFT (msg,s) =>
            Err.error ("Error parsing the signature specification: " ^ (errormsg (msg,s)))
    end
    )


  fun printName (a,sort) = sort ^ a

  fun printTm (Tm (name, args)) =
    (case name of
          "=" => join " = " (map printTm args)
        | "S" => printPA (Tm (name, args)) 0
        | "Z" => printPA (Tm (name, args)) 0
        | _ =>
	  (case map printTm args of
	       [] => name
	     | tmArgs =>
	       name ^ "(" ^ (join ", " tmArgs) ^ ")")
       )
    | printTm (Va x) = printName x

  and printPA (Tm ("S", [tm])) x = printPA tm (x + 1)
    | printPA (Tm ("Z", [])) x = Int.toString x
    | printPA tm x =
        if x <> 0
            then printTm (Tm ("Add", [toPA x, tm]))
            else printTm tm


  fun toSmtSort "i" = "Int"
    | toSmtSort s = s

  fun toSmtSym "Sub" = "-"
    | toSmtSym "Add" = "+"
    | toSmtSym "LT" = "<="
    | toSmtSym "implies" = "=>"
    | toSmtSym s = s

  val builtInSpec = populateSpecWithPredef (emptySpec)

  fun isBuiltinSort s =
    member s (specSorts builtInSpec)

  fun isBuiltinSym s =
    member s (map (fn (x,_,_) => x) (specSyms builtInSpec))

  fun toSmtSortDecl sorts =
    sorts |>
    flatmap (fn s =>
        if isBuiltinSort s
            then []
            else [fmt "(declare-sort $ 0)" [s]] ) |>
            (* then fmt "(declare-fun distinguish-$ ($) Int)" [toSmtSort s, toSmtSort s] *)
            (* else fmt "(declare-sort $ 0) (declare-fun distinguish-$ ($) Int)" [s,s,s,s]) |> *)
    join "\n"

  fun genIntList' n m l =
    if n >= m
        then l
        else genIntList' n (m-1) ((m)::l)
  fun genIntList n m = genIntList' n m []

  fun toSmtAssertDis bsort sorts sym i =
  let
    val n = length sorts
    val vars = map (fn i => "x" ^ Int.toString i) (genIntList 0 n)
    val ssorts = map toSmtSort sorts
    val sbsort = toSmtSort bsort
    val si = Int.toString i
  in
    if n = 0
        then fmt "(assert (= (distinguish-$ $) $))" [sbsort, sym, si]
        else fmt "(assert (forall ($) (= (distinguish-$ ($ $)) $)))"
            [join " " (map (fn (v,s) => fmt "($ $)" [v, s]) (zip vars ssorts)),
            sbsort,
            sym,
            join " " vars,
            si]
  end

  fun toSmtVarList vars =
    join " " $
        map (fn v => fmt "($ $)" [printName v, toSmtSort (nameSort v)]) vars

  fun toSmtAnd [] = "true"
    | toSmtAnd [p] = p
    | toSmtAnd props = fmt "(and $)" [join " " props]

  fun toSmtImplies "true" q = q
    | toSmtImplies "false" q = "true"
    | toSmtImplies p "false" = "false"
    | toSmtImplies p "true" = "true"
    | toSmtImplies p q = fmt "(=> $ $)" [p,q]

  fun toSmtForall vars x =      
    if null vars
        then x
        else fmt "(forall ($) $)" [toSmtVarList vars, x]

  fun partitionByCSorts spec vars = 
      List.filter
	  (fn x => Lst.exists (curry (op =)
				     ((toSmtSort o nameSort) x))
			      (specCSorts spec)
	  )
	  vars
	  |> Lst.partitionBy nameSort

  fun toSmtForallDist spec vars x =
      let
	  fun toDistinct [] = NONE
	    | toDistinct [_] = NONE
	    | toDistinct l =
	      SOME(fmt "(distinct $)" [l |> map printName |> join " "])

	  val dcvars = partitionByCSorts spec vars
			  |> map toDistinct
			  |> Opt.filterSome
			  |> toSmtAnd
      in
	  if null vars
          then x
          else fmt "(forall ($) $)" [toSmtVarList vars, toSmtImplies dcvars x]
      end

  fun toSmtExists vars x =
    if null vars
        then x
        else fmt "(exists ($) $)" [toSmtVarList vars, x]

  fun toSmtAssert x =
    fmt "(assert $)" [x]

  fun genNamesForSorts baseName sorts =
  let
    val n = length sorts
    val ns = map (fn i => baseName ^ Int.toString i) (genIntList 0 n)
  in
    zip ns sorts
  end

  fun toSmtAssertSymInjective sym sorts bsort =
  let
    val n = length sorts
    val vars1 = genNamesForSorts "x" sorts
    val vars2 = genNamesForSorts "y" sorts
  in
    if null sorts
        then ""
        else
    toSmtAssert $
    toSmtForall (vars1@vars2) $
        fmt "(implies (= ($ $) ($ $)) (and $))" [
            sym,
            join " " $ map printName vars1,
            sym,
            join " " $ map printName vars2,
            join " " $ map (fn (x,y) => fmt "(= $ $)" [printName x, printName y])
                (zip vars1 vars2)
        ]
  end

  fun toSmtSymDecl syms =
    zip (genIntList 0 (length syms)) syms |>
    flatmap (fn (j, (sym,sorts,bsort)) =>
        if isBuiltinSym sym
            then []
            else [
              let
                val vars = map (fn i => "x" ^ Int.toString i) (genIntList 0 (length sorts))
              in
		case (map toSmtSort sorts) of
		    [] =>
                    fmt "(declare-const $ $)" (* "\n\t$\n\t$" *)
			[sym,
			 toSmtSort bsort
			(* , toSmtAssertDis bsort sorts sym j *)
			(* , toSmtAssertSymInjective sym sorts bsort *)
			]
		  | smtSorts => 
                    fmt "(declare-fun $ ($) $)" (* "\n\t$\n\t$" *)
			[sym,
			 join " " smtSorts,
			 toSmtSort bsort
			(* , toSmtAssertDis bsort sorts sym j *)
			(* , toSmtAssertSymInjective sym sorts bsort *)
			]
            end ]
    ) |>
    join "\n"

  fun toSmtConstDecl consts =
      let
	  fun toSmtConst (c,[],_) =
	      toSmtSort c
	    | toSmtConst (c,args,_) =
	      let
		  val vargs = Lst.zip args (Lst.enum 1 (length args))
	      in
		  fmt "($ $)"
		      [toSmtSort c,
		       map (fn (s,n) => fmt "(mk-$$ $)" [toSmtSort c,Int.toString n, toSmtSort s]) vargs |> join " " 
		      ]
	      end
		  
	  fun toSmtDataTypeDecl [] = raise Domain
	    | toSmtDataTypeDecl (l as ((_,_,rs)::_)) =
	      fmt "(declare-datatypes () (($ $)))"
		  [toSmtSort rs,
		   join " " $ map toSmtConst l
		  ]
      in
      Lst.partitionBy (fn (_,_,rs) => rs) consts |>
		      List.map toSmtDataTypeDecl |>
		      join "\n"
      end

  fun toSmtTm (Tm (f, terms)) =
    (case f of
         "S" => toSmtPA (Tm (f,terms)) 0
       | "Z" => "0"
       | _ =>
	 (case map toSmtTm terms of
	      [] => toSmtSym f
	    | smtTerms => fmt "($ $)" [toSmtSym f, (join " " smtTerms)]))
    | toSmtTm (Va name) = printName name

  and toSmtPA (Tm ("S", [tm])) x = toSmtPA tm (x + 1)
    | toSmtPA (Tm ("Z", [])) x = Int.toString x
    | toSmtPA tm x =
        if x <> 0
            then toSmtTm (Tm ("Add", [toPA x, tm]))
            else toSmtTm tm

  fun toSmtAxDecl ax =
    ax |>
    map (fn a =>
        fmt "(assert (forall ($) $))" [
        join " " $
            map (fn x => fmt "($ $)" [printName x, toSmtSort (nameSort x)]) (nub (fv_tm a)),
        toSmtTm a
        ]
    ) |>
    join "\n"

  fun toSmtSpec spec =
  let
    val s = toSmtSortDecl (specSorts spec)
    val m = toSmtSymDecl (specUSyms spec)
    val c = toSmtConstDecl (specConsts spec)
    val a = toSmtAxDecl (specAx spec)
  in
    join "\n" [s,m,c,a]
  end

  fun toSmtNameDecl names =
    join "\n" $
        map (fn n =>
            fmt "(declare-fun $ () $)"
            [printName n, toSmtSort $ nameSort n]) (nub names)


end;


structure PiInstanceRequirements =
struct

  open Missing
  open MissingExtra
  open NominalAlgebra

  val spec = parseSpecFromFile "shia-sig.txt"

  type atom = name
  type term = tm
  type condition = tm (* of sort bool *)
  datatype assertion = Unit

  fun chaneq  (a,b)       = Tm ("=", [a,b])
  fun brReceive  (m,n)    = Tm ("=", [m,n])
  fun brTransmit (m,n)    = Tm ("=", [m,n])
  fun compose (psi1,psi2) = Unit
  val unit                = Unit

  fun newBasedOn (a,sort) xvec =
    case unzip xvec of
         (names,_) => (StringName.generateDistinct names, sort)

  (* This function is used in the simulator and bisim algorithm for generating placeholder names for channels. *)
  fun new xvec = newBasedOn ("hole", channelSort) xvec



  structure Sort = struct
    type sort = string
    val eq = (op=)
  end

  fun supportT t = fv_tm t
  fun supportC p = fv_tm p
  fun supportA _ = []

  fun swapT pi t = swap_tm pi t
  fun swapC pi p = swap_tm pi p
  fun swapA _ _  = Unit

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b

  fun substT sigma tm = subst_tm sigma tm
  fun substC sigma p = subst_tm sigma p
  fun substA sigma Unit = Unit

  fun nameSort (a,sort) = sort
  fun sortT t = inferSort spec t
  fun sortC t =
    let
      val s = inferSort spec t
    in
      if s = "bool"
        then "bool"
        else Err.error ("Only terms with return type of bool are allowed as conditions, got: " ^ s)
    end
  fun sortA _      = Err.undefined "implement sortA"

  fun isNameSort _ = true
  fun canRecv s _  = s = "tch"
  fun canSend _ _  = true
  fun canSubs a b  = a = b
  fun canRstr _ = true


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

end;

structure PsiPiInstance = Psi(PiInstanceRequirements)


structure PiSymbolicInstanceRequirements =
struct

  open PiInstanceRequirements

  fun var x = Va x

  structure Constraint = SymbolicOSConstraint(PsiPiInstance.Inst)

  val sTrue = RIGHT ([],Unit)
  val sFalse = LEFT ()

  (* fun collectNames (c as (names,psi,conds)) =  *)

  fun collectAllNames [] = []
    | collectAllNames ((c as (names, psi, conds))::cs) =
    names @ (flatmap supportC conds) @ (collectAllNames cs)


  fun distributeNames [] = []
    | distributeNames ((c as (avec, psi, conds))::cs) =
    (map (fn c => (avec, c)) conds) @ (distributeNames cs)

  fun derestrictNames names genNames conds [] = (genNames, conds)
    | derestrictNames names genNames conds ((avec, cond)::cs) =
  let
    val supC = supportC cond
    val avec = filter (fn a => member a supC) avec
    val freshFor = supC @ names
    val ns = List.foldr (fn (a,bvec) => (newBasedOn a (bvec @ freshFor))::bvec) [] avec
    val cond' = List.foldr (fn (pi,c) => swapC pi c) cond (zip avec ns)
  in
    derestrictNames (ns @ names) (ns @ genNames) (cond'::conds) cs
  end

  fun derestrictConds cs =
    cs |>
    distributeNames |>
    derestrictNames (collectAllNames cs) [] []

  fun freeNames cs = Constraint.support cs

  fun smtAssert props = fmt "(assert $)" [toSmtAnd props]

  fun toSmtCond cond = toSmtTm cond

  fun toSmtC conds =
    conds |>
    map toSmtCond |>
    toSmtAnd


  fun partitionNamesBasedOnSort spec names =
  let
    val sorts = specSorts spec
    val sort = nameSort
  in
    map (fn s => filter (fn n => sort n = s) names) sorts |>
    filter (fn x => not (null x))
  end


  fun nameDistinctions freeNames boundNames =
    freeNames |>
    map (fn n => partitionNamesBasedOnSort spec (n::boundNames)) |>
    List.concat


  fun toSmtNameDistinctions dists =
    dists |>
    map (fn ds => fmt "(distinct $)"
                  [join " " (map printName ds)]) |>
    toSmtAnd

  fun toSmt cs =
  let
    val s = toSmtSpec spec
    val (boundN,conds) = derestrictConds cs
    val freeN = freeNames cs
    val nd = toSmtNameDecl (boundN @ freeN)
    val distinctions = nameDistinctions freeN boundN
    val d = smtAssert [toSmtNameDistinctions distinctions]
    val c = smtAssert [toSmtC conds]
    val smt = join "\n" [s, nd, d, c]
  in
    smt
  end


  fun nameName (n,_) = n

  fun toSmtCond2 (avec,c) =
  let
    val names = nub (fv_tm c)
    val avec = nub avec
    val fnames = Lst.minus names avec
    val bnames = Lst.intersection names avec

    fun distinct names =
      if null names
        then ""
        else fmt "(distinct $)" [join " " $ map printName names]

    val distinctions =
      fnames |> flatmap (fn (x as (n,s)) =>
        let
          val bns = filter (fn (_,s') => s = s') bnames
        in
          if null bns
            then []
            else [distinct (x::bns)]
        end
      )
    val distinctions = 
      if null bnames
        then []
        else ((distinct bnames) :: distinctions)

    fun forallBNames nms x =
      if null nms
        then x
        else fmt "(forall ($) $)"
            [join " " $ map (fn n =>
                fmt "($ $)" [printName n, toSmtSort (nameSort n)]) nms, x]
  in
    forallBNames bnames (
        if null distinctions
            then toSmtTm c
            else fmt "(implies $ $)" [toSmtAnd distinctions, toSmtTm c])
  end


  fun toSmtConds2 cs =
    cs |>
    distributeNames |>
    map toSmtCond2 |>
    smtAssert

  fun toSmt2 cs =
  let
    val s = toSmtSpec spec
    val freeN = freeNames cs
    val nd = toSmtNameDecl freeN
    val c = toSmtConds2 cs
    val smt = join "\n" [s, nd, c]
  in
    smt
  end


  fun constraintToFOL cs =
    toSmtAnd $ map (fn (avec,c) => 
        toSmtForall (intersection avec (Cond.support c)) (toSmtTm c)) cs


  fun toSmtNeg x = fmt "(not $)" [x]

  fun distinguishSpecSorts [] = ""
(*    | distinguishSpecSorts [x] =
      fmt "(declare-const $ $)" [printName x, (toSmtSort o nameSort) x]*)
    | distinguishSpecSorts f =
      let
	  fun freshvars n vars x =
	      Lst.foldr (fn x => fn vars => newBasedOn x vars :: vars) vars (List.tabulate(n,const x))

	  val f' = freshvars 2 f (hd f)
      in
      join "\n"
	   (map (fn x => fmt "(declare-const $ $)" [printName x, (toSmtSort o nameSort) x]) f' @
	    [fmt "(assert (distinct $))" [join " " $ map printName f']])
      end
	  

  fun toSmt3 cs =
  let
    val fnames = freeNames cs
    val distrAvec = distributeNames cs
    val s = toSmtSpec spec
    val formula = constraintToFOL distrAvec
    val f = toSmtAssert (toSmtForallDist spec (nub fnames) (toSmtNeg formula))
    val csortbags = partitionByCSorts spec (nub fnames)
    val d = map distinguishSpecSorts csortbags |> join "\n"
  in
    join "\n" [s,d,f]
  end

  fun solve cs =
  let
    val smt = toSmt3 cs
(*    val _ = print "\n\n;;; ----------------------------------------------------------------------------\n"
    val _ = print smt*)
    val isSat = ExternalSmt.sat smt
(*    val _ = PolyML.print isSat*)
  in
    (* RIGHT ([], Unit) *)
    case isSat of
         ExternalSmt.SAT => LEFT ("")
       | ExternalSmt.UNSAT => RIGHT ([],Unit) 
       | ExternalSmt.UNKNOWN =>
	 RIGHT ([],Unit)
       | ExternalSmt.TIMEOUT =>
	 RIGHT ([],Unit)
        (*  Err.error "SMT solver does not know whether the constraint is satisfiable"*)
  end

  (*
  fun solve cs =
  let
    val smt = toSmt2 cs
    val _ = print smt
    val isSat = ExternalSmt.sat smt
    val _ = PolyML.print isSat
  in
    case isSat of
         ExternalSmt.SAT => RIGHT ([],Unit)
       | ExternalSmt.UNSAT => LEFT ("")
       | ExternalSmt.UNKNOWN =>
          Err.error "SMT solver does not know whether the constraint is satisfyable"
  end
  *)


  (*
  fun solve cs =
  let
    val smt = toSmt cs
    val _ = print smt
    val isSat = ExternalSmt.sat smt
    val _ = PolyML.print isSat
  in
    case isSat of
         ExternalSmt.SAT => RIGHT ([],Unit)
       | ExternalSmt.UNSAT => LEFT ("")
       | ExternalSmt.UNKNOWN =>
          Err.error "SMT solver does not know whether the constraint is satisfyable"
  end
  *)


  structure BisimConstraint = SymBisimConstraint(PsiPiInstance)
  local open BisimConstraint in
    val solveBisim = SOME (fn _ => Err.undefined "")
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
  type solution = (string, (Inst.name * Inst.term) list * Inst.assertion) Either.either
  val solve            = PiSymbolicInstanceRequirements.solve
end;

structure SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = PsiPiInstance
  structure Constraint = PiSymbolicInstanceRequirements.BisimConstraint
  val solve =
    case PiSymbolicInstanceRequirements.solveBisim of
         NONE => (fn _ => Either.LEFT "")
       | SOME s => s
end;

structure PiParserPrinterRequirements =
struct
  open PiInstanceRequirements
  open Missing

  fun printN n = printName n
  fun printT tm = printTm tm
  fun printC c = printT c
  fun printA psi = "1"
  val assr = Lex.stok "1" >> return Unit

  fun closeP p =
    p
    (* p >>= (fn x => Lex.ws >> eof x) *)

  fun parseResult p s =
    case Parser.parse p (AbstractParserStream.stringToStream s) of
         Either.RIGHT (r,s) => Either.RIGHT r
       | Either.LEFT  m => Either.LEFT (errormsg m)

  fun parseName s = parseResult (NominalAlgebra.parseName spec) s
  fun parseTerm s = parseResult (closeP (parseTm spec)) s
  fun parseCond s = parseResult (closeP (parseTm spec)) s
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


(* vim:ts=4:
 *)
