(* uses pwb/missing, pwb/parser *)

structure Test =
struct
  structure P = Parser(StringStream)
  open Missing;
  open P;

  fun test () =
    (nofail (chr #"A") >>
    (nofail (str "BB")))
    </choice/>
    zero

  fun run () =
    parse (test ()) (StringStream.make "CAC")

end;

