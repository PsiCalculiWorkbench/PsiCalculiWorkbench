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


functor WeakSymbolicPsiSimulator(SI: SYMBOLIC_PSI)
    : WEAK_SYMBOLIC_PSI_SIMULATOR =
struct
  structure Sim = SymbolicPsiSimulator(SI)
  structure Tr  = WeakSymbolicTransition(struct
    structure Psi        = SI.Psi
    structure Constraint = SI.Constraint
  end)

  open Missing

  fun translateAction  Sim.Tr.Act.Tau         = Tr.Tau
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

