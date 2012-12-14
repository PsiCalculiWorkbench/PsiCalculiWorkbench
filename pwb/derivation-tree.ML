(* uses pwb/missing *)

signature DerivationTypes =
sig
  (* eqtype premise *)
  type source (* The starting point of a derivation, e.g. a process *)
  type premise (* conclusions and pre-conditions of rules *)
  type rule    (* rule names *)
  type context (* arbitry environment *)

  (*
   *
   *            premisesM1 ... premisesMN
   *            -------------------------RuleM
   *                ...
   *
   *     premise21 ... premise2N
   *    ------------------------Rule2
   * premise11 ... premise1N
   * --------------------- Rule1
   *
   *               \|/
   *
   *            premise
   *
   *  Given a source try to infer all possible rules for that form. If there
   *  are no rules that can be inferred gives nil.
   *
   *)
  val infer      : context -> source -> (source list * rule) list

  (* premise list
   * -------------- rule
   * source (of premise?)
   * *)
  val eval       : context -> (premise list * rule * source) -> premise option

  (*
   * -------------- rule
   * source (of premise?)
   * *)
  val eval_axiom : context -> rule * source -> premise option
end;


signature DERIVATION_TREE =
sig
  structure D : DerivationTypes

  datatype inf  = Inf  of inf  list * D.rule * D.source
  datatype einf = EInf of einf list * D.rule * D.premise

  (* invariant : env must be the same *)
  val generate_derivations : D.context -> D.source -> inf list
  val eval_tree            : D.context -> inf      -> einf option
  val eval_all             : D.context -> D.source -> einf list
end;


functor DerivationTree(DT: DerivationTypes) : DERIVATION_TREE =
struct
  structure D = DT
  local open DT in

  datatype inf
    = Inf of inf list * rule * source

  datatype inf_forest
    = InfForest of (inf_forest list * rule) list * source
    | InfFail

  datatype einf
    = EInf of einf list * rule * premise

    (*
    *                    An  Bn
    *                   -------- Rn
    *                   ...
    *               -------
    *            A2 B2
    *          ------- R2
    *        A1  B1
    *      --------- R1
    *    A0  B0
    *  --------- R0
    *      C
    *
    *      Where any of As or Bs can be, recursively, C.
    *)
  fun generate_inference e source =
  let
    val all_rules_app : (source list * rule) list = infer e source

    fun generate_forests (sources : source list) =
        map (generate_inference e) sources

    val any_failed = List.exists (fn InfFail => true | _ => false)

    fun generate_forests_for_rules (pr : (source list * rule) list) =
      Opt.filterSome
        (map (fn ([], r) => SOME ([], r) (* axiom *)
               | (ps, r) => 
                   let val fs = generate_forests ps in
                     if any_failed fs
                        then NONE
                        else SOME (fs, r)
                     end) pr)
    val fs = generate_forests_for_rules all_rules_app
  in (* [([], AXIOM_NAME), ...] in case of axiom *)
      case fs of
          [] => InfFail
        | _  => InfForest (fs, source)
  end;


  fun unwind InfFail = [] (* val unwind : inf_forest -> inf list *)
    | unwind (InfForest (forests_rule_list, source)) =
    List.concat (map (
        fn ([], rule) => [Inf ([], rule, source)]
         | (forests, rule) =>
            let val infs = Lst.cart_product (map unwind forests) (*!!!*)
            in (map (fn f => Inf (f, rule, source)) infs)
            end)
        forests_rule_list)


  fun eval_tree e (Inf ([], r, p)) =
    Opt.some (fn ep => EInf ([], r, ep)) (eval_axiom e (r, p))
    | eval_tree e (Inf (ps, r, p)) =
    let
      val eps = map (eval_tree e) ps
      val none_failed = List.all (fn (SOME _) => true | NONE => false) eps
    in
      if none_failed then
        let
          val einfs = Opt.filterSome eps
          val prs = map (fn (EInf (_, _, pr)) => pr) einfs
          val ev = eval e (prs, r, p)
        in case ev of
                SOME p => SOME (EInf (einfs, r, p))
              | NONE => NONE
        end
      else NONE
    end

  fun generate_derivations e = unwind o generate_inference e
  fun eval_all e p = Opt.filterSome (map (eval_tree e) (generate_derivations e p))

end;
end;



(*
 *
 * An example: computing the length of a string.
 *
 *)
structure StringProveTypes : DerivationTypes =
struct

  (*
   * Proving that strings can be deconstructed.
   *
   *    Rules   a -> n    as -> m
   *            ----------------- Cons1
   *              a.as -> n + m
   *
   *            as -> n   a -> m
   *            ----------------- Cons2
   *              a.as -> n + m
   *
   *            a -> n   a -> m
   *            --------------- Bogus
   *                  a -> n
   *
   *    Axiom   ------- Char
   *             a -> 1
   *
   *)

  type context = unit
  type source = string
  type premise = string * int
  datatype rule = Cons1 | Cons2 | Char | Bogus

  fun singleton s = (String.size s) = 1
  fun head s = String.extract (s, 0, SOME 1)
  fun rest s = String.extract (s, 1, NONE)

  fun cons1 s =
    if singleton s
        then NONE
        else SOME ([head s, rest s], Cons1)

  fun cons2 s =
    if singleton s
        then NONE
        else SOME ([rest s, head s], Cons2)

  fun rchar s =
    if singleton s
        then SOME ([], Char)
        else NONE

  fun bogus s =
    if singleton s
        then SOME ([s, s], Bogus)
        else NONE

  val rules = [cons1, cons2, rchar, bogus]

  fun infer () s = Opt.filterSome (map (fn rule => rule s) rules)

  fun eval_axiom () (_, a) = SOME (a,1)

  fun eval () ([(_, n), (_, m)], Cons1, a) = SOME (a, n + m)
    | eval () ([(_, n), (_, m)], Cons2, a) = SOME (a, n + m)
    | eval () ([(_, n), (_, m)], Bogus, a) = SOME (a, n    )
    | eval () _ = raise Match (* error *)

end;


structure DerivationTreeSample =
struct
  structure SP = DerivationTree(StringProveTypes);

  fun test () =
  let
    val test = "ab";
    val trees = SP.generate_derivations () test;
  in
    SP.eval_tree () (hd trees)
  end
end;

