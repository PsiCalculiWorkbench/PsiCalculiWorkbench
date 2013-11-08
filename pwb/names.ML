(* uses pwb/parser,
        pwb/missing
 *)

signature NOMINAL_NAME =
sig
  type name

  val new        : name list -> name
  val newBasedOn : name -> name list -> name
  val swap       : name * name -> name
  val permute    : (name * name) list -> name
end;


signature NOMINAL_NAME_SET =
sig
  structure Name : NOMINAL_NAME
  type nameset

  val empty  : nameset
  val add    : Name.name -> nameset
  val union  : nameset -> nameset -> nameset
  val inter  : nameset -> nameset -> nameset
  val member : Name.name -> nameset -> bool

  val swap    : Name.name * Name.name -> nameset -> nameset
  val permute : (Name.name * Name.name) list -> nameset -> nameset

  val toList : nameset -> Name.name list
  val fromList: Name.name list -> nameset
end;


signature NOMINAL_NAME_REPR =
sig
  structure Name : NOMINAL_NAME

  val parse: string -> (string, Name.name) Either.either
  val print: Name.name -> string
end;


signature GLOBAL_NAME_GEN =
sig
  structure Name : NOMINAL_NAME

  val newName : unit -> Name.name
  val init : Name.name list -> unit
end;





structure StringName :
sig
  structure Name : NOMINAL_NAME
  (*structure Set : NOMINAL_NAME_SET*)
  (*sharing Set.Name = Name*)
end =
struct
  structure Name =
  struct
    type name = string

    fun new _ = Err.undefined "";
    fun newBasedOn _ _ = Err.undefined "";
    fun swap _  = Err.undefined "";
    fun permute _  = Err.undefined "";
  end;


end;


