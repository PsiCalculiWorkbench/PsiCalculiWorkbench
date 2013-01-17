(* uses pwb/missing
 *)

signature SORT =
sig
  type sort
  val eq: sort * sort -> bool
end;

structure Unsorted =
struct
  datatype sort  = SORT
  fun eq _ = true
end;

