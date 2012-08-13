(* uses pwb/missing
 *)

signature SORT =
sig
  (* TODO: bad, I need to change the atom type instead of this one *)
  eqtype sort

  val eq: sort * sort -> bool

  (* val isSort : sorts -> sort -> bool *)
end;


(*

signature UNSORT =
sig
  include SORT
  val u : sort
end;

signature SUBSET_SORT =
sig
  structure Sort : SORT

  type sort
  val inc : sort -> Sort.sort
end;

*)

structure Unsorted =
struct
  datatype sort  = SORT
  fun eq _ = true
end;

