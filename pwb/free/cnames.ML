(* uses pwb/sort
 *)

functor CountedNames(A: sig
                          structure S: SORT
                          val toString : S.sort -> string
                        end) =
struct
  open A

  structure AtomSort = S
  structure DataSort = S

  open Missing

  datatype atom = Atom of string * S.sort * int
  type data = atom

  fun max lst = List.foldr (fn (a,b) => if a > b then a else b) 0 lst

  fun someNameOfSort sort = Atom ("-", sort, 0)

  fun new (Atom (name, sort, _)) atoms =
  let val newCnt = max (map (fn Atom (_,_,c) => c) atoms) + 1
  in Atom (name, sort, newCnt)
  end

  fun eq (Atom (na,sa,ca), Atom (nb,sb,cb)) =
    ca = cb andalso sa </S.eq/> sb andalso na = nb

  fun swapAtom (a,b) c =
    if a = c then b else
    if b = c then a else c

  fun atomSort (Atom (_,sort,_)) = sort
  val dataSort = atomSort
  val eqData = eq

  val support = Lst.sngl
  val swap = swapAtom
  fun fresh a b = not $ a </eq/> b


  fun toString (Atom (name, sort, cnt)) =
    name ^ Int.toString cnt ^ "_" ^ A.toString sort
end;

