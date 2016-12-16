(* uses pwb/psi,
        pwb/missing,
        pwb/simulator,
        pwb/missing-io,
        pwb/pwb-logger
 *)


functor PsiTransitionGraphViz(A:
    sig
      structure Sim : SYMBOLIC_PSI_SIMULATOR
      structure Slv : SYMBOLIC_CONSTRAINT_SOLVER
      sharing Sim.Psi.Inst = Slv.Inst
      (*sharing Sim.Constraint = Slv.Constraint*)

      val showP : Sim.Psi.psi -> string
      val showC : Sim.Tr.Constraint.constraint -> string
      val showA : Sim.Tr.Act.action -> string
      val showS : ((Slv.Inst.name * Slv.Inst.term) list * Slv.Inst.assertion)
        -> string
    end) :
sig
  structure Sim : SYMBOLIC_PSI_SIMULATOR
  val viz : Sim.ClEnv.env -> Sim.Psi.psi -> int -> string -> bool -> unit
end =
struct
  open Missing
  open A
  open Sim

  structure C = Slv.Constraint
  structure P = Sim.Psi

  fun freshPermutation c p newc =
      let
          val newnames = Lst.minus (C.support newc) (P.support p)
          val freshnames = C.newsBasedOn newnames (Lst.union (C.support c) (P.support p))
      in
          Lst.zip newnames freshnames
      end

  fun permConstr perm c =
      Lst.foldr C.swap c perm

  fun permAct perm a =
      Lst.foldr Tr.Act.swap a perm

(*  fun freshconstr c p newc = 
      let
	  val newnames = Lst.minus (C.support newc) (P.support p)
	  val freshnames = C.newsBasedOn newnames (Lst.union (C.support c) (P.support p))
      in
	  Lst.foldr Slv.Constraint.swap newc (Lst.zip newnames freshnames)
      end*)

  (* code duplication from simulator.ML :( *)
  val removeBrIn = 
      List.filter (fn ((_,Tr.Act.BrInput _,_,_),_) => false
                    | _ => true)

  (* code duplication from simulator.ML :( *)
  fun onlyMostListeners trs = 
      let
          val (brs,others) = List.partition (fn (_,tup) => isSome tup) trs
          val brs' = map (fn (a,b) => (a,valOf b)) brs
      in
          map fst others @
          (
           Lst.partitionBy (fn (_,(path,_)) => path) brs' |>
                           map
                           (fn (f::r) =>
                               List.foldr (fn ((p,(pth,rls)),(p',(pth',rls'))) => 
                                              if rls >= rls' then
                                                  (p,(pth,rls))
                                              else
                                                  (p',(pth',rls')))
                                          f r
                             | [] => raise Domain)
                           |> map fst
          )
      end

  fun reduce env proc c reach fresh =
    Sim.reduce' env proc |>
    removeBrIn |>
    map (fn ((proc,act,constr,derivProc),rdc) =>
        let
            val perm = freshPermutation fresh proc constr
	    val freshConstr = permConstr perm constr
	    val aggrConstr = Tr.Constraint.compose fresh freshConstr
            val freshAct = permAct perm act
        in (((proc,freshAct,(if reach then aggrConstr else freshConstr),Slv.solve (if reach then aggrConstr else freshConstr),derivProc),aggrConstr),rdc) end) |>
    onlyMostListeners

  fun eqData'(p,q) =
      p </P.eqSkeleton/> q
      orelse
      p </P.eqData/> q

  val visitedP = ref []
  fun resetP () = visitedP := []
  fun addP p =
  let val () = visitedP := p::(!visitedP)
  in
    ()
  end
  fun inP p = exists (fn p' => p </eqData'/> p') (!visitedP)
  fun findP p = List.find (fn p' => p </eqData'/> p') (!visitedP)


(* negative level means no upper bound on depth. use with caution! *)
  fun reductions env proc c level reach fresh =
    if level = 0 orelse inP proc then []
    else
      let val () = addP proc in
        reduce env proc c reach fresh |>
        flatmap (fn (tr as (proc,act,constr,sol,derivProc),fresh) =>
            (sol |> either
                (const []) (* change to const [tr] if you want state with no sol *)
                (fn _ =>
                    case findP derivProc of
                         SOME proc' => [(proc,act,constr,sol,proc')]
                       | NONE => tr::(reductions env derivProc constr (level - 1) reach fresh))))
      end

  fun escape str =
    String.explode str |>
    flatmap (fn c => if c = #"\n" then [#"\\",#"n"]
                     else if c = #"\"" then [#"\\",#"\""]
                     else if c = #"\\" then [#"\\", #"\\"]
                     else [c]) |>
    String.implode

  val trueC = []

  fun enclose s = "\""^ s ^"\""

  fun vizEdge (proc,act,constr,sol,derivProc) =
    enclose (escape (showP proc)) ^ " -> " ^
    enclose (escape (showP derivProc)) ^
    " [label=" ^
        (enclose (
        "act: " ^ escape (showA act) ^ "\\n" ^
        "cstr: " ^ escape (showC constr) ^ "\\n" ^
        "sol: " ^
            (sol |> either (const "NO") (fn s => escape (showS s) )) ))
              ^ "]\n"

  fun viz env proc level filename reach =
    MissingIO.withWriteFile filename (fn out =>
    let
      fun w s = TextIO.output (out,s)
      val () = resetP ()
      val cpu = Timer.startCPUTimer()
      val real = Timer.startRealTimer()
      val edges = reductions env proc trueC level reach trueC
      val real = Timer.checkRealTimer real
      val cpu = Timer.checkCPUTimer cpu
    in
        w "digraph G {\n";
        forall (fn e => w (vizEdge e)) edges;
        w "}";
        (print o String.concat) ["\n",
                                 "Real time:      ",Time.fmt 6 real," seconds\n",
                                 "CPU time (sys): ",Time.fmt 6 (#sys cpu)," seconds\n",
                                 "CPU time (usr): ",Time.fmt 6 (#usr cpu)," seconds\n"]
    end
    )

end;

