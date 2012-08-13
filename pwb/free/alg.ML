(* uses pwb/sort,
        pwb/nominal,
        pwb/missing,
        pwb/parser,
        pwb/free/cnames,
        pwb/psi-parsing
 *)

signature SIGMA =
sig
  structure Sort : SORT
  type function_symbol

  val eq : function_symbol * function_symbol -> bool

  (* A constant is function_symbol with arity ([], Sort)  *)
  val ar : function_symbol -> Sort.sort list * Sort.sort
end;


signature NOM_SIGMA =
sig
  include SIGMA
  val isAtomSort : Sort.sort -> bool
end;

signature NOM_ABS_SIGMA =
sig
  include NOM_SIGMA
  val absSort : Sort.sort -> Sort.sort ->
        (string,Sort.sort) Either.either
  val isAbsSort : Sort.sort -> bool
end;


signature SIGMA_ALGEBRA =
sig
  type carrier
  structure Sigma: SIGMA

  (* length (fst (ar F)) = length (carrier list) *)
  (* TODO: generalise over the failure *)
  val app: Sigma.function_symbol * carrier list
         -> (string, carrier) Either.either
end;


signature NOM_SIGMA_ALGEBRA =
sig
  include SIGMA_ALGEBRA
  include NOMINAL
  sharing type carrier = data
  sharing Sigma.Sort = DataSort = AtomSort
end;



signature NOM_TERM_ALGEBRA =
sig
  include NOM_SIGMA_ALGEBRA

  val var    : atom -> carrier
  (* val var    : Sigma.Sort.sort -> atom -> carrier *)
  val abs    : atom -> carrier -> carrier

  val des    : carrier -> Sigma.function_symbol * carrier list
  val desAbs : carrier -> atom * carrier

  val isVar  : carrier -> bool
  val isAbs  : carrier -> bool
  val isTrm  : carrier -> bool

  val subst  : (carrier * carrier) list -> carrier -> carrier
end;


signature NOMINAL_NAMES =
sig
  eqtype atom
  structure AtomSort : SORT

  val atomSort : atom -> AtomSort.sort
  val new       : atom -> atom list -> atom
  val swapAtom  : atom * atom -> atom -> atom
end;



functor NomSigma(A: sig
                      structure S: SORT
                      val isAtomSort : S.sort -> bool
                    end): NOM_SIGMA =
struct
  open A
  open Missing

  structure Sort = S

  datatype function_symbol = Fs of string * (S.sort list * Sort.sort)

  fun ar (Fs (s,sort)) = sort

  fun eq (Fs (n, (args, res)), Fs (n', (args', res'))) =
    n = n' andalso res </S.eq/> res andalso Lst.eq S.eq args args'
end;


functor NomAbsTermAlgebra(A:
  sig
    structure Sigma : NOM_ABS_SIGMA
    structure Names : NOMINAL_NAMES
    sharing Names.AtomSort = Sigma.Sort
  end) : NOM_TERM_ALGEBRA =
struct
  open A
  open Missing
  open Sigma
  open Names

  val isAbsSort = isAbsSort
  val absSort = absSort

  val eqSort = Sort.eq

  datatype term
    = Term of function_symbol * term list
    | Var  of atom
    | Abs  of atom * term

  type carrier = term

  fun sort (Term (f, _)) = Tpl.snd (ar f)
    | sort (Var a)       = atomSort a
    | sort (Abs (a,trm)) = right $ absSort (atomSort a) (sort trm)

  fun app (f,xs) =
  let
    val (alpha,tau) = ar f
    val alpha' = map sort xs
  in
    if isAbsSort tau
        then LEFT $ "Abstraction sort is not allowed as a result of a function symbol"
        else if Lst.eq eqSort alpha alpha'
            then RIGHT $ Term (f,xs)
            else LEFT  $ "Sorts do not match"
  end

  fun abs a trm = Abs (a, trm)

  val var = Var

  fun isVar (Var _) = true
    | isVar _       = false

  fun isAbs (Abs _) = true
    | isAbs _       = false

  fun isTrm (Abs _) = true
    | isTrm _       = false

  fun des (Term trm) = trm
    | des _          = undefined ()

  fun desAbs (Abs abs) = abs
    | desAbs _         = undefined ()

  structure Nom = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom = atom
    type data = carrier

    val atomSort = atomSort

    val dataSort = sort

    val new = new

    fun swap pi (Term (f, xs)) = Term (f, map (swap pi) xs)
      | swap pi (Var a)    = Var (swapAtom pi a)
      | swap pi (Abs (a,trm))  = Abs (swapAtom pi a, swap pi trm)

    fun support (Term (f, xs)) = List.concat $ map support xs
      | support (Var a) = [a]
      | support (Abs (a, x)) = support x </uncurry Lst.minus/> [a]

    fun eq eq' (Term (f,xs), Term(g, ys)) =
        f </Sigma.eq/> g andalso List.length xs = List.length ys
                         andalso Lst.eq (eq eq') xs ys
      | eq eq' (Var a, Var b) = a = b
      | eq eq' (Abs (a,x), Abs (b,y)) = eq' ((a,x),(b,y))
      | eq eq' _ = false

  end) open Nom


  fun subst sigma (Term (f, trms)) =
    subst sigma (Term (f, map (subst sigma) trms))
    | subst sigma (Abs (a, trm)) = Abs (a, subst sigma trm)
    | subst sigma (x as (Var a)) =
    let
      fun subst' [] x = x
        | subst' (((Var n), trm)::sigmas) x =
        if (Var n) </eqData/> x
            then trm
            else subst' sigmas x
        | subst' _ _ = Err.error "signature.ML: unhandled case in sig"
    in
      subst' sigma x
    end

end;


functor FiniteBaseAbsSortNomSigma(A:
  sig
    eqtype atom_sort
    eqtype base_sort
  end) :
  sig
    include NOM_ABS_SIGMA

    (* TODO: move to a proper signature *)
    eqtype atom_sort
    eqtype base_sort
    val desAtomSort : Sort.sort -> atom_sort
    val desBaseSort : Sort.sort -> base_sort
    val desAbsSort : Sort.sort -> atom_sort * Sort.sort
  end =
struct
  open Missing
  open A

  datatype abs_sort  = AbsSort of atom_sort * sort
  and sort
    = NS of atom_sort
    | BS of base_sort
    | AS of abs_sort

  structure Sort : SORT = struct
    type sort = sort
    fun eq (a,b) = a = b
  end

  fun isAtomSort (NS _) = true
    | isAtomSort _ = false

  fun absSort (NS ns) s = RIGHT $ AS (AbsSort (ns, s))
    | absSort _ _ = LEFT $ "Cannot form an abstraction sort"

  fun isAbsSort (AS _) = true
    | isAbsSort _ = false

    (* TODO: fill in the errors *)
  fun desAtomSort (NS ns) = ns
    | desAtomSort _ = Err.error ""

  fun desBaseSort (BS bs) = bs
    | desBaseSort _ = Err.error ""

  fun desAbsSort (AS (AbsSort s)) = s
    | desAbsSort _ = Err.error ""

  structure Sigma = NomSigma(struct
    structure S = Sort
    val isAtomSort = isAtomSort
  end)

  open Sigma
end;


structure FiniteBaseAbsSortNomSigmaStringList :
  sig
    include NOM_ABS_SIGMA

    type atom_sort = string
    type atom_sorts
    type base_sort = string
    type base_sorts

    val baseSorts : base_sorts -> string list
    val atomSorts : atom_sorts -> string list

    val isValidAtomSort : atom_sort -> atom_sorts -> bool
    val isValidBaseSort : base_sort -> base_sorts -> bool

    val addAtomSort : atom_sort -> atom_sorts -> atom_sorts
    val addBaseSort : base_sort -> base_sorts -> base_sorts


    (* TODO: see the TODO at the FiniteBaseAbsSortNomSigma functor *)
    val desAtomSort : Sort.sort -> atom_sort
    val desBaseSort : Sort.sort -> base_sort
    val desAbsSort : Sort.sort -> atom_sort * Sort.sort
  end =
struct
  open Missing

  datatype atom_sorts = AtomSort of string list
  datatype base_sorts = BaseSort of string list
  type atom_sort = string
  type base_sort = string

  structure Sigma = FiniteBaseAbsSortNomSigma(struct
    type atom_sort = atom_sort
    type base_sort = base_sort
  end)

  open Sigma

  fun baseSorts (BaseSort bs) = bs
  fun atomSorts (AtomSort ns) = ns
  fun isValidBaseSort s (BaseSort bs) = member s bs
  fun isValidAtomSort s (AtomSort ns) = member s ns
  fun addAtomSort s (AtomSort ns) = AtomSort (s::ns)
  fun addBaseSort s (BaseSort bs) = BaseSort (s::bs)

  fun atomSortToString (AtomSort s) = s
end;


structure FiniteBaseAbsSortNomSigmaStringListParser =
struct
  structure Parser = Parser(StringStream)

  structure Sig = FiniteBaseAbsSortNomSigmaStringList
  structure Term = NomAbsTermAlgebra(struct
    structure Sigma = Sig
    structure Names = CountedNames(struct
      structure S : SORT = Sig.Sort
      fun toString sort =
        if Sig.isAtomSort sort
            then Sig.desAtomSort sort
            else Err.undefined ()
    end)
  end)

  structure Lex = PsiLexerParserComb(Parser)


  open Missing
  open Parser
  open Lex
  open Sig


  (* sort      x *)
  (* atom-sort x *)
  (* term-sort x *)
  datatype sort_type = Sort | AtomSort | TermSort

  fun parseSorts () =
  let
    fun sortName kw typ = stok kw >> identifier >>= (fn x => return (typ,x))
  in
               sortName "sort" Sort
    </choice/> sortName "atom-sort" AtomSort
    </choice/> sortName "term-sort" TermSort
  end


  datatype parsed_sort = BS of string | AS of string * parsed_sort

  fun baseSort () = identifier >>= return o BS

  fun anySort () = baseSort () </choice/> absSort ()
  and absSort () =
                    stok "[" >> baseSort () >>=
    (fn (BS bs) =>  stok "]" >> anySort () >>=
    (fn s  =>       return (AS (bs, s)) ))


  fun termSort () =
        (             (anySort () </sepby1/> stok ",") >>=
        (fn sl =>     stok "->" >>
                      baseSort () >>=
        (fn (BS r) => return (sl, r))))
    </choice/>
        (baseSort () >>= (fn (BS s) => return ([], s)))

  fun parseFunSym () =
                    identifier >>=
    (fn n =>        stok ":" >>
                    termSort () >>=
    (fn (ls,r) =>   return (n, ls, r)))


  datatype parsed_term
    = PTerm of string * (parsed_term list)
    | PAbs of string * parsed_term
    | PAtom of string

  fun parseTerm () =
        (           identifier >>=
        (fn fs =>   stok "(" >>
                    (parseTerm () </sepby1/> stok ",") >>=
        (fn args => stok ")" >>
                    return $ PTerm (fs, args) )))
    </choice/>
        (           stok "[" >>
                    identifier >>=
        (fn n =>    stok "]" >>
                    parseTerm () >>=
        (fn t =>    return $ PAbs (n, t) )))
    </choice/>
        (identifier >>= return o PAtom)


  fun test () =
  let
    val t = StringStream.make " lam : [l]l -> l app : l, l -> l var : l -> l"
    (*val p = parse (parseSorts ()) t*)
    val p = parse (parseFunSym () </sepby1/> ws) t

    val t' = StringStream.make " lam ([a]var(a)) " (* \a.a *)
    val p' = parse (parseTerm ()) t'
  in
    PolyML.print p;
    PolyML.print p'
  end

end;



PolyML.print_depth 100;
FiniteBaseAbsSortNomSigmaStringListParser.test ();

