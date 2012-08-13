
structure MissingIO :
sig
  val withOpenFile  : string -> (TextIO.instream -> unit) -> unit
  val withWriteFile : string -> (TextIO.outstream -> unit) -> unit
  val withOpenString: string -> (TextIO.instream -> unit) -> unit
  val printErr : string -> unit
  val inOutFSytem : (string -> string -> string) -> 
                    (TextIO.outstream -> unit) -> 
                    (TextIO.instream -> unit) -> bool
  val dump : string -> string -> unit
  val slurp: string -> string
  val readAll : TextIO.instream -> string
end =
struct
  open OS


  fun withOpenFile fileName handler =
  let
    val fh = TextIO.openIn fileName
    val () = handler fh
    val () = TextIO.closeIn fh
  in
    ()
  end

  fun withWriteFile fileName handler =
  let
    val fh = TextIO.openOut fileName
    val () = handler fh
    val () = TextIO.closeOut fh
  in
    ()
  end

  fun withOpenString fileName handler =
  let
    val fh = TextIO.openString fileName
    val () = handler fh
    val () = TextIO.closeIn fh
  in
    ()
  end


  fun printErr str = TextIO.output (TextIO.stdErr, str)


  fun inOutFSytem cmd writer reader =
  let
    val inTmp = FileSys.tmpName ()
    val outTmp = FileSys.tmpName ()
    val () = withWriteFile inTmp writer
    val status = Process.system (cmd inTmp outTmp)
  in
    if Process.isSuccess status
        then (withOpenFile outTmp reader; true)
        else false
  end


  fun dump str fileName = withWriteFile fileName (fn s => TextIO.output (s, str))

  fun readAll' str stream = 
  let
    val i = TextIO.input stream
  in
    if String.size i = 0
        then str
        else readAll' (str ^ i) stream
  end

  fun readAll stream = readAll' "" stream

  fun slurp fileName = 
  let
    val rs = ref ""
  in
    (withOpenFile fileName (fn s => (rs := readAll s));
    !rs)
  end

end;


