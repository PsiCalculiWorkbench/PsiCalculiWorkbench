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
  val viz : Sim.ClEnv.env -> Sim.Psi.psi -> int -> string -> unit
end =
struct
  open Missing
  open A
  open Sim

  fun reduce env proc c =
    Sim.reduce env proc |>
    map (fn (proc,act,constr,derivProc) =>
        let val aggrConstr = Tr.Constraint.compose c constr
        in (proc,act,aggrConstr,Slv.solve aggrConstr,derivProc) end)


  structure P = Sim.Psi
  val visitedP = ref []
  fun resetP () = visitedP := []
  fun addP p =
  let val () = visitedP := p::(!visitedP)
  in
    ()
  end
  fun inP p = exists (fn p' => p </P.eqData/> p') (!visitedP)
  fun findP p = List.find (fn p' => p </P.eqData/> p') (!visitedP)


  fun reductions env proc c level =
    if level <= 0 orelse inP proc then []
    else
      let val () = addP proc in
        reduce env proc c |>
        flatmap (fn (tr as (proc,act,constr,sol,derivProc)) =>
            (sol |> either
                (const []) (* change to const [tr] if you want state with no sol *)
                (fn _ =>
                    case findP derivProc of
                         SOME proc' => [(proc,act,constr,sol,proc')]
                       | NONE => tr::(reductions env derivProc constr (level - 1)))))
      end

  fun escape str =
    String.explode str |>
    flatmap (fn c => if c = #"\n" then [#"\\",#"n"]
                     else if c = #"\"" then [#"\\",#"\""]
                     else if c = #"\\" then [#"\\", #"\\"]
                     else [c]) |>
    String.implode


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

  val trueC = []

  fun viz env proc level filename =
    MissingIO.withWriteFile filename (fn out =>
    let
      fun w s = TextIO.output (out,s)
      val () = resetP ()
      val edges = reductions env proc trueC level
    in
      (w "digraph G {\n";
      forall (fn e => w (vizEdge e)) edges;
      w "}")
    end
    )

end;

