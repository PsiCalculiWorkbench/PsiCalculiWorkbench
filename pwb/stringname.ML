(* uses pwb/missing *)

structure StringName :
sig
  val swap_name        : string * string -> string -> string
  val generateDistinct : string list -> string
  val generate         : unit -> string
end = struct

  fun swap_name (a, b) d =
    if a = d then b else
    if b = d then a else d

  fun generateDistinct strs =
  let
    val seed = map Char.toString (String.explode "abcdefghijklmnopqrstuvwxyz")
    fun distinct s = List.all (fn x => x <> s) strs

    fun try1 [] = NONE
      | try1 (s::ss) =
      if distinct ("g" ^ s)
        then SOME ("g" ^ s)
        else try1 ss

    fun try2 [] [] _ = NONE
      | try2 (s1::s1s) [] a = try2 s1s a a
      | try2 (s1::s1s) (s2::s2s) a =
      if distinct (s1 ^ s2)
        then SOME (s2 ^ s2)
        else try2 (s1::s1s) s2s a
      | try2 _ _ _ = Err.error "Unhandled pattern in StringName.try2"

    fun try3 n =
    let val s = "n" ^ (Int.toString n)
    in if distinct s
        then s
        else try3 (n + 1)
    end
  in
    case try1 seed of
         NONE => (case try2 seed seed seed of
                      NONE => try3 0
                     | SOME s => s)
       | SOME s => s
  end;


  val sfx = ref "n"
  val cnt = ref 0

  fun suffix x = sfx := x

  fun generate () = (
    cnt := (!cnt) + 1;
    (!sfx) ^ (Int.toString (!cnt)))
end;
