signature ENVIRONMENT =
sig
  type env
  type key
  type value

  val extend : env -> key -> value -> env
  val remove : env -> key -> env
  val find   : env -> key -> value list
  val dom    : env -> key list
  val empty  : env
end;

