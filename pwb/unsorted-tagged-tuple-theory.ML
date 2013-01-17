(* uses pwb/missing,
        pwb/nominal,
        pwb/parser
 *)


(*
 * Unsorted Nominal Term Algebra
 *)



functor PWB_NOM_UNSORTED_TAGGED_TUPLE_THEORY(A: sig
  structure V: UNSORTED_NOMINAL
  structure P: PARSER
  val parseN : V.atom P.parser
end) =
struct
  open A
  open List
  open Missing
  (* finite signature *)

  type fsymbol = string
  type variable = V.atom

  (* function symbol and its arity *)
  type signt = (fsymbol * int) list

  datatype term = Term of fsymbol * (term list)
                | ProjTerm of fsymbol * int * term
                | Var of variable

  datatype predicate = Eq of term * term
                     | IsF of fsymbol * term


  fun ar sigma f =
    find (fn (f',_) => f = f') sigma |>
    maybe NONE (fn (_,n) => SOME n)

  fun makeT sigma f terms =
    case ar sigma f of
         NONE => LEFT ("Unknown symbol: " ^ f)
       | SOME n => if length terms = n
                        then RIGHT (Term (f, terms))
                        else LEFT ("The arity of symbol "^f^" is "^
                                   (Int.toString n) ^" but "^
                                   (Int.toString (length terms))^" terms given")


  fun makePT sigma f i term =
    case ar sigma f of
         NONE => LEFT ("Unknown symbol: " ^ f)
       | SOME n => if i > n 
                    then LEFT ("The arity of "^f^" is "^(Int.toString n)^
                                "; asked for projection "^(Int.toString i))
                    else RIGHT (ProjTerm (f, i, term))

  fun supportT (Term (_, terms)) = flatmap supportT terms
    | supportT (ProjTerm (_,_,term)) = supportT term
    | supportT (Var v) = [v]

  fun supportP (Eq (t1,t2)) = supportT t1 @ supportT t2
    | supportP (IsF (_,t)) = supportT t

  fun substT sigma (Term (f,terms)) = Term (f, map (substT sigma) terms)
    | substT sigma (ProjTerm (f,i,term)) = ProjTerm (f, i, substT sigma term)
    | substT sigma (Var v) =
    sigma |> find (fn (x,t) => x = v)
          |> maybe (Var v) (fn (_,t) => t)

  fun substP sigma (Eq (t1,t2)) = Eq (substT sigma t1, substT sigma t2)
    | substP sigma (IsF (f, t)) = IsF (f, substT sigma t)


  type term_algebra = signt * term

  type term_rewriting_system = signt * ((term * term) list)

  type unif_system = signt * predicate list


  fun dom subst = map fst subst

  (* Assumption: x is not in the domain of sigma *)
  fun composeSubst sigma (x,t) =
    (x,t)::(map (fn (x',t') => (x', substT [(x,t)] t')) sigma)

  fun supportSigma sigma = sigma |> flatmap (fn (x, t) => x :: (supportT t))

  fun supportUS prds = prds |> flatmap supportP

  fun substUS sigma prds = prds |> map (substP sigma)

  fun newN' n names newNames =
    if n = 0
        then newNames
        else let val a = V.new names in
               newN' (n - 1) (a::names) (a::newNames)
             end

  fun newN n names = newN' n names []

  fun unify sigma (s, []) = RIGHT sigma
    | unify sigma (s, (Eq (Term (f1,args1), Term (f2,args2)))::prds) =
    if f1 = f2
        (* case: f(x1,...,xn) = f(y1,...,yn) *)
        then unify sigma (s, (map (fn (x,y) => Eq (x,y)) (zip args1 args2)) @ prds)
        (* case: f(x1,...,xn) = g(y1,...,ym) *)
        else LEFT "error"
    | unify sigma (s, (Eq (Var x, y))::prds) =
        (* case: x = anything *)
        unify
            (composeSubst sigma (x,y))
            (s, substUS [(x,y)] prds)
    | unify sigma (s, (Eq (y, Var x))::prds) = unify sigma (s, (Eq (Var x, y))::prds)
    | unify sigma (s, prds' as (Eq (ProjTerm (f,i,x), y)::prds)) =
    (let
      val n = always id (ar s f)
      val zs = map Var (newN n (supportSigma sigma @ supportUS prds'))
      val eq1 = Eq (x, Term (f, zs))
      val eq2 = Eq (nth (zs, i - 1), y)
    in
      unify sigma (s, eq1::eq2::prds)
    end)
    | unify sigma (s, prds' as (IsF (f, x)::prds)) =
    (let
      val n = always id (ar s f)
      val zs = map Var (newN n (supportSigma sigma @ supportUS prds'))
      val eq = Eq (x, Term (f, zs))
    in
      unify sigma (s, eq::prds)
     end)
    | unify sigma (s, (Eq (Term x, ProjTerm y)::prds)) =
        unify sigma (s, (Eq (ProjTerm y, Term x)::prds))

  (* todo: term rewriting *)


  local open P in

  val ws = many (sat Char.isSpace)
  fun id () = many1 (sat Char.isAlpha) >>= 
    return o String.concat o map Char.toString

  fun parseT s =
                ws >> id () >>= 
    (fn f =>    ar s f |> 
                    maybe (P.error (f ^ "is not in the signature"))
                          (fn n => if n = 0 then return (Term (f,[]))
                                            else
                (ws >> str "(" >>
                (((parseT s) </sepby1/> (ws >> str ",")) >>=
    (fn ts =>   ws >> str ")" >>=
    (fn _ =>    makeT s f ts |> either
                    (fn err => P.error err)
                    (fn t => return t) ))))))
                
                

  end

end;

