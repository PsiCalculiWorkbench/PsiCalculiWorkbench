(* uses pwb/missing
 *)


signature SORT =
sig
  type sort
  val eq: sort * sort -> bool
end;


signature UNSORTED_NOMINAL =
sig
  eqtype atom
  type   data

  val new         : atom list -> atom
  val newBasedOn  : atom -> atom list -> atom
  val newsBasedOn : atom list -> atom list -> atom list

  val swapAtom  : atom * atom -> atom -> atom
  val swap      : atom * atom -> data -> data
  val support   : data -> atom list
  val fresh     : atom -> data -> bool

  val eqData    : data * data -> bool
end;


signature NOMINAL =
sig
  include UNSORTED_NOMINAL

  structure AtomSort: SORT
  structure DataSort: SORT

  val atomSort  : atom -> AtomSort.sort
  val dataSort  : data -> DataSort.sort
end;



structure Unsorted =
struct
  datatype sort  = SORT
  fun eq _ = true
end;



functor UnsortedToTrivialySortedNominal(N: UNSORTED_NOMINAL): NOMINAL =
struct
  open N
  structure AtomSort = Unsorted
  structure DataSort = Unsorted
  fun atomSort _ = Unsorted.SORT
  fun dataSort _ = Unsorted.SORT
end;


signature NOMINAL_MINIMAL =
sig
  eqtype atom
  type   data

  structure AtomSort: SORT
  structure DataSort: SORT

  val atomSort  : atom -> AtomSort.sort
  val dataSort  : data -> DataSort.sort

  val swap        : atom * atom -> data -> data
  val support     : data -> atom list
  val new         : atom list -> atom
  val newBasedOn  : atom -> atom list -> atom

  val eq  : (((atom * data) * (atom * data)) -> bool) ->
            data * data -> bool
end;


functor Nominal(N : NOMINAL_MINIMAL): NOMINAL =
struct

  structure AtomSort = N.AtomSort
  structure DataSort = N.DataSort
  val atomSort = N.atomSort
  val dataSort = N.dataSort

  type atom = N.atom
  type data = N.data

  fun swapAtom (a, b) d =
    if a = d then b else
    if b = d then a else d

  val swap        = N.swap
  val support     = N.support
  val new         = N.new
  val newBasedOn  = N.newBasedOn

  fun NBOhelper (x,(acc,nos)) =
      let
	  val y = (N.newBasedOn x nos)
      in (y::acc,y::nos)
      end
  fun newsBasedOn xs os = Tpl.fst (List.foldr NBOhelper ([],os) xs)

  fun fresh a d = not (Lst.member a (support d))

  (* A1  ( Alpha equivalence )
    a.x = a'.x'  <=>  (a = a' /\ x = x')  \/  (a' # x /\ x' = (a a')ox)
  *)
  fun alphaEq ((a,x), (a',x')) =
    if a = a'
      then eqData (x,x')
      else let
        val a'' = newBasedOn a ([a,a'] @ (support x) @ (support x'))
      in
        eqData (swap (a,a'') x, swap (a',a'')  x')
      end

  and eqData (d1,d2) = N.eq alphaEq (d1,d2)

end;



functor NominalName(N: sig
  structure AtomSort: SORT
  eqtype atom

  val atomSort  : atom -> AtomSort.sort
  val new       : atom list -> atom
  val newBasedOn: atom -> atom list -> atom
end): NOMINAL =
struct
  structure AtomSort = N.AtomSort
  structure DataSort = N.AtomSort
  type atom = N.atom
  type data = N.atom

  val atomSort = N.atomSort
  val dataSort = N.atomSort

  fun swapAtom (a, b) d =
    if a = d then b else
    if b = d then a else d

  fun support a = [a]
  fun fresh a b = a <> b
  val swap      = swapAtom
  val new       = N.new
  val newBasedOn = N.newBasedOn

  fun NBOhelper (x,(acc,nos)) =
      let
	  val y = (N.newBasedOn x nos)
      in (y::acc,y::nos)
      end
  fun newsBasedOn xs os = Tpl.fst (List.foldr NBOhelper ([],os) xs)

  fun eqData (n,m) = n = m
end;

functor NominalAtom(N: NOMINAL): NOMINAL =
struct
  structure AtomSort = N.AtomSort
  structure DataSort = N.AtomSort
  type atom = N.atom
  type data = N.atom

  val atomSort = N.atomSort
  val dataSort = N.atomSort

  fun swapAtom (a, b) d = N.swapAtom (a, b) d

  fun support a = [a]
  fun fresh a b = a <> b
  val swap      = swapAtom
  val new       = N.new
  val newBasedOn= N.newBasedOn

  fun NBOhelper (x,(acc,nos)) =
      let
	  val y = (N.newBasedOn x nos)
      in (y::acc,y::nos)
      end
  fun newsBasedOn xs os = Tpl.fst (List.foldr NBOhelper ([],os) xs)

  fun eqData (n,m) = n = m
end;


functor NominalList (A: NOMINAL): NOMINAL =
struct
  structure AtomSort = A.AtomSort
  structure DataSort = struct
    datatype sort = NominalListSort
    fun eq _ = true
  end
  type atom      = A.atom
  type data      = A.data list

  val atomSort   = A.atomSort
  fun dataSort l = DataSort.NominalListSort


  val swapAtom = A.swapAtom
  fun swap ab l = map (A.swap ab) l
  fun support l = List.concat (map A.support l)
  fun fresh a l = List.all (A.fresh a) l
  val new       = A.new
  val newBasedOn= A.newBasedOn

  fun NBOhelper (x,(acc,nos)) =
      let
	  val y = (A.newBasedOn x nos)
      in (y::acc,y::nos)
      end
  fun newsBasedOn xs os = Tpl.fst (List.foldr NBOhelper ([],os) xs)

  fun eqData ([], [])       = true
    | eqData ([], ms)       = false
    | eqData (ns, [])       = false
    | eqData (n::ns, m::ms) = A.eqData (n,m) andalso eqData (ns, ms)
end;


functor NominalNameList (N: sig
  structure AtomSort: SORT
  eqtype atom
  val new       : atom list -> atom
  val newBasedOn: atom -> atom list -> atom
  val atomSort : atom -> AtomSort.sort
end) : NOMINAL = NominalList (NominalName (N));


functor NominalAlpha(N: NOMINAL):
sig
  val makeFresh  : N.atom list ->
                   N.data -> N.atom list -> N.data
  val permute    : (N.atom * N.atom) list -> N.data -> N.data
  val freshNames : N.atom list ->
                   N.atom list -> (N.atom * N.atom) list
end =
struct
  structure L = NominalNameList (N)

  fun permute pi t = Lst.foldl N.swap t pi

  fun freshNames names support =
  let
    (* right most binders (sequence) binds the tightest,
     * i.e. right associative, as genPI generates permutations
     * in a reverse order foldl is appropriate here *)
    val dirty = List.filter (not o (Fun.flip L.fresh support)) names

    fun genPI pi [] _ = pi
      | genPI pi (d::dirty) supp =
      let val n = N.newBasedOn d supp
      in genPI ((d,n)::pi) dirty (n::supp)
      end

    val pi = genPI [] dirty support
  in
    pi
  end

  fun makeFresh binders term forNames =
    permute (freshNames binders forNames) term

end;


functor NominalNameListUnsorted(N: sig
  eqtype atom
  val new       : atom list -> atom
  val newBasedOn: atom -> atom list -> atom
end) : NOMINAL = NominalNameList (struct
  structure AtomSort = struct datatype sort = UNI fun eq _ = true end
  open N
  fun atomSort _ = AtomSort.UNI
end);

