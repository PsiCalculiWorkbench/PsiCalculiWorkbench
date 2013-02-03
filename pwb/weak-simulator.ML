(* uses pwb/missing,
        pwb/simulator
*)

signature WEAK_SYMBOLIC_TRANSITION =
sig
  structure Psi : PSI
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  sharing Psi.Inst = Constraint.Inst

  datatype weak_action
    = Silent
    | Tau
    | Output   of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | Input    of Psi.Inst.term * Psi.Inst.name list
    | BrOutput of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | BrInput  of Psi.Inst.term * Psi.Inst.name list

  type weak_transition
    = Psi.psi * weak_action * Constraint.constraint * Psi.psi

  val addFrame : (Psi.atom list * Psi.Inst.assertion)
                 -> weak_transition -> weak_transition

end;



functor WeakSymbolicTransition(A :
    sig
      structure Psi        : PSI
      structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
      sharing Psi.Inst = Constraint.Inst
    end): WEAK_SYMBOLIC_TRANSITION =
struct
  open A

  datatype weak_action
    = Silent
    | Tau
    | Output   of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | Input    of Psi.Inst.term * Psi.Inst.name list
    | BrOutput of Psi.Inst.term * Psi.Inst.name list * Psi.Inst.term list
    | BrInput  of Psi.Inst.term * Psi.Inst.name list

  type weak_transition
    = Psi.psi * weak_action * Constraint.constraint * Psi.psi


  fun addFrame fr (p,act,c,q) = (p,act,Constraint.addFrame fr c,q)

end;



signature WEAK_SYMBOLIC_PSI_SIMULATOR =
sig
  structure Sim : SYMBOLIC_PSI_SIMULATOR
  structure Tr  : WEAK_SYMBOLIC_TRANSITION

  (**
   * Compute all weak transitions
   *)
  val reduce
    : Sim.ClEnv.env -> Sim.Psi.psi -> Tr.weak_transition list

  val silent
    : Sim.ClEnv.env -> Sim.Psi.psi -> Tr.weak_transition list

  val reduceA
    : Sim.ClEnv.env -> Sim.Psi.psi -> Sim.action_type
      -> Tr.weak_transition list

  sharing Sim.Psi = Tr.Psi
end;



signature WEAK_SYMBOLIC_PSI_REDUCER =
sig
  structure Red : SYMBOLIC_PSI_REDUCER
  structure Tr  : WEAK_SYMBOLIC_TRANSITION

  (**
   * Compute all weak transitions
   *)
  val reduce
    : Red.Sim.ClEnv.env -> Red.Sim.Psi.psi
        -> Red.Sim.Constraint.constraint ->
        (Red.Sim.Psi.psi * Tr.weak_action * Red.Sim.Constraint.constraint
        * Red.Slv.solution * Red.Sim.Psi.psi) list

  val silent
    : Red.Sim.ClEnv.env -> Red.Sim.Psi.psi
        -> Red.Sim.Constraint.constraint ->
        (Red.Sim.Psi.psi * Tr.weak_action * Red.Sim.Constraint.constraint
        * Red.Slv.solution * Red.Sim.Psi.psi) list

  val reduceA
    : Red.Sim.ClEnv.env -> Red.Sim.Psi.psi -> Red.Sim.action_type
        -> Red.Sim.Constraint.constraint ->
        (Red.Sim.Psi.psi * Tr.weak_action * Red.Sim.Constraint.constraint
        * Red.Slv.solution * Red.Sim.Psi.psi) list

  sharing Red.Sim.Psi = Tr.Psi
end;



functor WeakSymbolicPsiReducer(A: sig
  structure Red: SYMBOLIC_PSI_REDUCER
  structure Tr : WEAK_SYMBOLIC_TRANSITION
  sharing Red.Sim.Psi = Tr.Psi
end) : WEAK_SYMBOLIC_PSI_REDUCER =
struct
  open A
  open Red

  open Missing

  fun translateAction  Sim.Tr.Act.Tau           = Tr.Tau
    | translateAction (Sim.Tr.Act.Output   out) = Tr.Output out
    | translateAction (Sim.Tr.Act.Input    inp) = Tr.Input inp
    | translateAction (Sim.Tr.Act.BrOutput out) = Tr.BrOutput out
    | translateAction (Sim.Tr.Act.BrInput  inp) = Tr.BrInput inp


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


  fun onlySolv trs =
    List.filter (fn (tr as (_,_,_,s,_)) =>
        s |> either (const false) (const true)) trs

  fun transAct trs =
    trs |> map (fn (p,act,c,s,p') =>
        (p, translateAction act, c, s, p'))


  fun silent' env orgProc proc constr =
  if inP proc then []
  else
    let
      val () = addP proc
      val taus = Red.reduceA env proc Sim.TAUa constr
    in
      taus |> onlySolv |> transAct |>
        Lst.flatmap (fn (tr as (p,act,c,sol,p')) =>
            (orgProc,act,c,sol,p')::(silent' env orgProc p' c))
    end

  fun silent env proc constr =
  let
    val () = resetP ()
    val sol = Slv.solve constr
  in
    sol |> either (const []) (fn _ =>
        (proc, Tr.Silent, constr, sol, proc)
            ::(silent' env proc proc constr))
  end


  fun actionSym env proc actT constr =
    silent env proc constr |> Lst.flatmap
        (fn (_,_,c,s,p) =>
            Red.reduceA env p actT c |> onlySolv |> transAct |> Lst.flatmap
                (fn (_,act,c',s',p') => silent env p' c' |>
                    map (fn (_,_,c'',s'',p'') =>
                        (proc,act,c'',s'',p'')) ))



  fun reduceA env proc actT constr =
    if actT = Sim.ANYa
        then silent env proc constr @ actionSym env proc Sim.VISa constr
        else actionSym env proc actT constr

  fun reduce e p constr = reduceA e p Sim.ANYa constr

end;





functor WeakSymbolicPsiSimulator(SI: SYMBOLIC_PSI)
    : WEAK_SYMBOLIC_PSI_SIMULATOR =
struct
  structure Sim = SymbolicPsiSimulator(SI)
  structure Tr  = WeakSymbolicTransition(struct
    structure Psi        = SI.Psi
    structure Constraint = SI.Constraint
  end)

  open Missing

  fun translateAction  Sim.Tr.Act.Tau           = Tr.Tau
    | translateAction (Sim.Tr.Act.Output   out) = Tr.Output out
    | translateAction (Sim.Tr.Act.Input    inp) = Tr.Input  inp
    | translateAction (Sim.Tr.Act.BrOutput out) = Tr.BrOutput out
    | translateAction (Sim.Tr.Act.BrInput  inp) = Tr.BrInput  inp

  fun silent e p =
  let
    val taus = Sim.reduceA e p Sim.TAUa
    val tauplus =
        taus |> Lst.flatmap
             (fn (p  ,_,c ,p'') => silent e p'' |> map
                 (fn (p'',_,c',p' ) => (p, Tr.Silent, c @ c', p')))
  in
      (p, Tr.Silent, [], p)::tauplus
  end

  fun action_sym e p ac =
    (silent e p) |> (Lst.flatmap
        (fn (p,_,c,p'')         => (Sim.reduceA e p'' ac) |> Lst.flatmap
          (fn (p'',alpha,c',p''') => (silent e (p''')) |> map
            (fn (p''',_,c'',p')     =>
                (p, translateAction alpha, c @ c' @ c'',p')))))

  fun reduceA e p ac =
      if ac = Sim.ANYa
      then silent e p @ action_sym e p Sim.VISa
      else action_sym e p ac

  fun reduce e p = reduceA e p Sim.ANYa
end;

