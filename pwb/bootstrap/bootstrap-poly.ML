structure PwbSml =
struct
  open PwbSml

  val dpth : int ref = ref 100

  fun supressOutput () = PolyML.print_depth (~1)
  fun restoreOutput () = PolyML.print_depth (!dpth)
  fun setOutput i = dpth := i

end;
