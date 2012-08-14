structure PwbSml =
struct
  open PwbSml

  val dpth : int ref = ref 100

  fun supressOutput () = PolyML.print_depth 0
  fun restoreOutput () = PolyML.print_depth (!dpth)

end;
