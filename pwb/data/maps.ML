(* uses pwb/missing *)

signature FINITE_MAP =
sig
  type key
  type 'a map

  val empty : 'a map
  val add   : 'a map -> key -> 'a -> 'a map
  val find  : 'a map -> key -> 'a option
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


functor Trie(M: FINITE_MAP) : TRIE =
struct
  type key = M.key list
  type digit = M.key

  datatype 'a map = Trie of 'a option * 'a map M.map

  val empty = Trie (NONE, M.empty)

  fun trie (Trie (v, m)) k = M.find m k

  fun value (Trie (SOME x,_)) = SOME x
    | value _ = NONE

  fun find t [] = value t
    | find t (k::ks) = 
        Opt.bindO (trie t k)
                  (fn t' => find t' ks)

  fun add (Trie (_,m)) [] x = Trie (SOME x, m)
    | add (t as (Trie (v,m))) (k::ks) x = 
    let
      val t' = Opt.maybe empty Fun.id (trie t k)
    in
      Trie (v, M.add m k (add t' ks x))
    end

end;


structure CharListTrie =
struct
  structure O = struct
    type elem = char
    fun leq a b = Char.<= (a,b)
  end
  structure M = UnbalancedBinaryMap(O)
  structure T = Trie(M)
  open T
end;


