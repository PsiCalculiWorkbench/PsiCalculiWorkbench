
structure Uses :
sig
  exception UsesError of string

  val uses : string -> unit
  val usesFile : string -> unit
  val collectFileListFromModStrFiles : string -> (string * string) list

  (*val canonicalName : string -> string*)
  (*val isLoaded : string -> bool*)
  val markAsLoadedFile : string -> unit
  val prependToPath : string -> unit
  val appendToPath : string -> unit
  val getLoadPaths : unit -> string list
  val setLoadPaths : string list -> unit

  val getLoadedFiles : unit -> (string * string) list
  val clearLoadedFiles : unit -> unit

  (* dumpUseRel relPath *)
  val dumpUseRel : string -> string
  val dumpUse : unit -> string
end =
struct
  structure Parser = Parser(ParserStreamIO)
  open Missing
  open Parser
  structure Path = OS.Path
  structure FileSys = OS.FileSys

  exception UsesError of string


  val log = PwbLog.write "Pwb Uses Debug"
  val log1 = PwbLog.write "Pwb Uses"


  (* filename, canonical name (md5 hash) *)
  type loaded_files = (string * string) list

  val loadedFiles : loaded_files ref = ref []

  fun getLoadedFiles () = !loadedFiles
  fun clearLoadedFiles () = loadedFiles := []

  fun getCanonicalName fileName =
    fileName |> MissingIO.slurp |> MD5.md5 |> MD5.bintohex
  fun markAsLoadedFile fileName =
  let
    val cname = getCanonicalName fileName
  in(
    loadedFiles := (fileName, cname) :: (!loadedFiles);
    log ("Marking the file \"" ^ fileName ^ "\" with canonical name (MD5) " ^
        cname ^ " as loaded"))
  end
  fun isLoaded fileName =
    exists ((fn c => fn (_, c') => c = c') (getCanonicalName fileName)) (!loadedFiles)


  fun dumpUseRel relPath =
  let
    val paths =
      map (fn (p,_) => OS.Path.mkRelative {path = p, relativeTo = relPath})
        (Missing.reverse (!loadedFiles))
    val useP = map (fn p => "use \""^ p ^ "\";\n") paths
  in
    concat useP
  end

  fun dumpUse () =
    concat (map (fn (p,_) => "use \""^ p ^ "\";\n")
                (Missing.reverse (!loadedFiles)))


  type load_paths = string list

  val loadPaths : load_paths ref = ref []

  fun appendToPath path = loadPaths := (!loadPaths) @ [path]
  fun prependToPath path = loadPaths := path :: (!loadPaths)
  fun getLoadPaths () = !loadPaths
  fun setLoadPaths pths = loadPaths := pths

  fun pathsToStr () =
  let
    fun enc p = "\"" ^ p ^ "\""
    fun str [] = ""
      | str [p] = p
      | str (p1::p2::paths) = (enc p1) ^ ", " ^ (enc p2) ^ (str paths)
  in
    "[" ^ (str (!loadPaths)) ^ "]"
  end




  val smlExtensions = ["ML", "sml"]


  fun modStrToComp modStr = String.fields (fn c => c = #"/") modStr
  fun modStrToPath modStr =
    Path.toString {isAbs = false,
                   vol   = Path.getVolume Path.currentArc,
                   arcs  = modStrToComp modStr}

  fun fileExists file = FileSys.access (file, [])


  fun findFileWithExt modStrPath [] = NONE
    | findFileWithExt modStrPath (ext::exts) =
  let
    val filePath = Path.joinBaseExt {base = modStrPath, ext = SOME ext}
  in
    if fileExists filePath
        then SOME filePath
        else findFileWithExt modStrPath exts
  end

  fun findFile modStrPath =
    if fileExists modStrPath
        then SOME modStrPath
        else findFileWithExt modStrPath smlExtensions


  (*fun resolveLocalModStr modStr = findFile (modStrToPath modStr)*)
  fun resolveLocalModStr fileName =
    if fileExists fileName
        then SOME fileName
        else NONE

  fun resolvePathModStr modStr [] = NONE
    | resolvePathModStr modStr (path::paths) =
  let
    val p1 = Path.fromString path
    val p2 = Path.fromString (modStrToPath modStr)
    val p = Path.toString
        {isAbs = #isAbs p1, vol = #vol p1, arcs = (#arcs p1) @ (#arcs p2)}
  in
    case findFile p of
         NONE => resolvePathModStr modStr paths
       | SOME f => SOME f
  end


  fun resolveModStr modStr =
    if String.isPrefix "@" modStr then
      resolveLocalModStr (String.extract (modStr,1,NONE))
    else
      resolvePathModStr modStr (!loadPaths)




  fun isWord chr  = Char.isGraph chr andalso (chr <> #",")
  fun isSpace chr = Char.isSpace chr
  fun toStr l     = String.concat (map Char.toString l)
  val ws          = sat isSpace
  fun word ()     = many1 (sat isWord) >>= (fn l => return (toStr l))


  (*
    <uses-clause> ::= `uses' <word> (`,' <word>)*
  *)
  fun useParser () =
                    str "uses" >> nofail (many1 ws >>
                    ((many ws >> word ()) </sepby1/> (many ws >> chr #",")))

  (*
    <uses-pragma> ::= `(*' <uses-clause> `*)'
  *)
  fun usesParser () =
                    many ws >> str "(*" >> many ws >>
                    useParser () >>=
    (fn uses =>     nofail (many ws >> str "*)" >>
                    return uses))


  fun readUsesFromFile filename =
  let
    val fh    = TextIO.openIn filename
    val fs    = ParserStreamIO.make fh
    val files = parse (usesParser ()) fs
    val ()    = TextIO.closeIn fh
  in
    case files of
         LEFT (m as (Parser.Error msg,s)) => raise UsesError (errormsg m ^ " in file " ^ filename) 
       | LEFT (Parser.Fail msg,_)  => []
       | RIGHT (fs,_)              => fs
  end


  fun collectFileListFromModStrFiles modStr =
  let
    val loaded = ref []

    fun isVisited cname visited = List.exists (fn (_,_,c1) => cname = c1) visited

    fun strVis [] = ""
      | strVis [(v,_,_)] = v ^ "->"
      | strVis ((v1,_,_)::(v2,_,_)::vs) = strVis vs ^ v2 ^ " -> " ^ v1

    fun loadFile modStr visited =
    let
      val path = resolveModStr modStr
    in
      (case path of
           NONE => raise UsesError
                ("Module '" ^ modStr ^ "' not found in path " ^ pathsToStr () ^
                (case visited of
                     [] => ""
                   | _ => " while visiting " ^ strVis visited))
         | SOME p =>
             (let
               val c = getCanonicalName p
             in
               if isVisited c visited
                  then
                    raise UsesError ("Circular dependency found: " ^
                                     strVis ((modStr,p,c)::visited))
                  else if isLoaded p
                    then (log ("The file \"" ^ p ^ "\" is marked as loaded"); ())
                  else
                    let
                      val modStrs = readUsesFromFile p
                      val () = log ("Visiting file " ^ p ^ " with canonical name " ^ c)
                      val vis = (modStr, p, c)::visited
                      val () = forall (fn ms => loadFile ms vis) modStrs
                      val () = loaded := (!loaded) @ [(modStr,p)]
                      val _ = markAsLoadedFile p
                    in () end
             end))
    end

    val () = loadFile modStr []
  in
    !loaded
  end


  fun printErr str = TextIO.output (TextIO.stdErr, str)


  fun uses' modStr =
  let
    val files = collectFileListFromModStrFiles modStr
  in
    forall (fn (m,f) =>
        (log1 ("Loading module \"" ^ m ^ "\" resolved as the file \"" ^ f ^ "\"");
         use f)) files
  end


  fun uses modStr =
    uses' modStr
        handle (IO.Io {name, ...}) =>
            printErr ("\nError: could not read the file \"" ^ name ^ "\"\n")

  fun usesFile filename = uses ("@" ^ filename)

end;

