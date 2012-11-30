(* uses pwb/missing *)

signature FINITE_MAP =
sig
  type key
  type 'a map

  val empty : 'a map
  val add   : 'a map -> key -> 'a -> 'a map
  val find  : 'a map -> key -> 'a option
end;


signature FINITE_SET =
sig
  type elem
  type set

  val member : set -> elem -> bool
  val add : set -> elem -> set
  val empty : set
end;


signature FINITE_STREAM =
sig
  type stream
  type elem

  val head    : stream -> elem
  val tail    : stream -> stream
  val isEmpty : stream -> bool
end;


signature TRIE =
sig
  include FINITE_MAP
  type digit
  val trie  : 'a map -> digit -> 'a map option
  val value : 'a map -> 'a option
end;


signature TOTAL_ORDER =
sig
  type elem
  val leq : elem -> elem -> bool
end;


functor UnbalancedBinaryMap(E: TOTAL_ORDER) : FINITE_MAP =
struct
  open E

  type key = elem
  datatype 'a map = Node | Tree of 'a map * key * 'a * 'a map

  fun eq a b = leq a b andalso leq b a

  val empty = Node

  fun add Node k v = Tree (empty, k, v, empty)
    | add (Tree (l,k',v',r)) k v =
    case (leq k k', leq k' k) of
         (true, true) => Tree (l,k,v,r)
       | (true,false) => Tree (add l k v, k', v', r)
       | (false,true) => Tree (l, k', v', add r k v)
       | _ => Err.error
        "The elements are not totaly ordered in UnbalancedBinaryMap.add"

  fun find Node _ = NONE
    | find (Tree (l,k',v,r)) k =
    case (leq k k', leq k' k) of
         (true, true) => SOME v
       | (true,false) => find l k
       | (false,true) => find r k
       | _ => Err.error "UnbalancedBinaryMap.find"

end;


functor Trie(A: sig
  structure M: FINITE_MAP
  structure S: FINITE_STREAM
  sharing type M.key = S.elem
end) : TRIE =
struct
  open A

  type key = S.stream
  type digit = M.key

  fun obs s =
    if S.isEmpty s
        then NONE
        else SOME (S.head s, S.tail s)

  datatype 'a map = Trie of 'a option * 'a map M.map

  val empty = Trie (NONE, M.empty)

  fun trie (Trie (v, m)) k = M.find m k

  fun value (Trie (SOME x,_)) = SOME x
    | value _ = NONE

  fun find t s =
    case obs s of
         NONE => value t
       | SOME (k,ks) =>
           Opt.bindO (trie t k)
                     (fn t' => find t' ks)

  fun add (t as (Trie (v,m))) s x =
    case obs s of
         NONE => Trie (SOME x, m)
       | SOME (k,ks) =>
            (let val t' = Opt.maybe empty Fun.id (trie t k)
             in Trie (v, M.add m k (add t' ks x)) end)

end;


structure FiniteStringStream :
sig
  include FINITE_STREAM
  val make : string -> stream
end =
struct
  type stream = int * string
  type elem = char

  fun isEmpty (i,s) = i >= String.size s
  fun head (i,s) = String.sub (s,i)
  fun tail (i,s) = (i+1,s)

  fun make s = (0,s)
end;


structure StringTrie : TRIE =
struct
  structure O = struct
    type elem = char
    fun leq a b = Char.<= (a,b)
  end
  structure S = FiniteStringStream
  structure M = UnbalancedBinaryMap(O)
  structure T = Trie(struct
    structure M = M
    structure S = S
  end)
  open T

  type key = string
  type 'a map = 'a T.map

  fun ss s = S.make s

  val empty = T.empty
  fun add m k v = T.add m (ss k) v
  fun find m k = T.find m (ss k)

  type digit = char
  val trie = T.trie
  val value = T.value
end;


structure StringSet : FINITE_SET =
struct
  type elem = string
  type set = unit StringTrie.map

  fun member set el =
    Opt.maybe false (Fun.const true) (StringTrie.find set el)

  fun add set el = StringTrie.add set el ()

  val empty = StringTrie.empty
end;


