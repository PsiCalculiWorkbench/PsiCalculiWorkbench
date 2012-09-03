(* uses pwb/missing,
        pwb/parser
 *)

structure RmnsLiterateProgram =
struct
  structure Parser = Parser(ParserStreamIO)
  open Parser
  open Missing

  (* If I would car for efficiency I would use String representation
  * with constant complexity concatenation operator
  *)

  fun nestedComment () =
  let
    fun any t =    (delayed nestedComment >>= (fn c => any (t ^ c)))
      </choice/>    ((try (str "*)")) >> return t)
      </choice/>    (item >>= (fn c => any (t ^ (String.implode [c]))))
  in
                str "(*" >>=
    (fn _ =>    any "" >>=
    (fn s =>    str "*)" >>
                return ("(*" ^ s ^ "*)") ))
  end

  (* No nesting *)
  fun texComment () =
  let
    fun any tex = (try (str "*)") >> return tex)
      </choice/> (item >>= (fn c => any (c::tex)))
  in
            str "(**" >>=
    (fn _ =>
            any [] >>=
    (fn tex =>
            str "*)" >>
            return (String.implode $ reverse tex)))
  end

  fun sml () =
  let
    fun sml' cs =
                 (try (str "(**") >> return cs)
      </choice/> (eof cs)
      </choice/> (nestedComment () >>= (fn c => sml' (cs ^ c)))
      </choice/> (item >>= (fn c => sml' (cs ^ (String.implode [c]))))
  in
    sml' ""
  end

  fun smlString () =
    ()

  fun isSectionMarkChar c = Char.isSpace c orelse Char.isAlpha c

  fun sectionMark () =
                    many (sat Char.isSpace) >>
                    str "(**[" >> many (sat isSectionMarkChar) >>=
    (fn sm =>       str "]*)" >>
                    return (String.implode sm)
    )


  datatype chunkAttr = TeX | Sml
  type sectionMark = string
  datatype docEl = Doc of chunkAttr * sectionMark * string
  type doc       = docEl list

  fun parseDoc () =
  let
    fun chunk cs sm =
                  eof cs
      </choice/> (sectionMark () >>= (fn sm => chunk cs sm))
      </choice/> (texComment () >>= (fn t => chunk ((Doc (TeX, sm, t))::cs) sm))
      </choice/> (sml () >>= (fn t => chunk ((Doc (Sml, sm, t))::cs) sm))
      </choice/> return cs
  in
    chunk [] "default" >>= return o reverse
  end

  fun forall action [] = ()
    | forall action (x::xs) = (action x; forall action xs)

  fun outputTeX out markedSections doc =
  let
    val _ = print "\n"
    val _ = print $ Int.toString $ length doc
    val _ = print "\n"

    val doc = List.filter
        (fn (Doc (_,sm,_)) => Lst.member sm markedSections) doc

    val _ = print "\n"
    val _ = print $ Int.toString $ length doc
    val _ = print "\n"

    fun pr s = TextIO.output (out, s)

    fun countLines [] _ = []
      | countLines ((Doc (TeX, _, _))::doc) lastNr =
        (0,0) :: countLines doc lastNr
      | countLines ((Doc (Sml, _, s))::doc) lastNr =
      let
        val nr = (List.length $ List.filter (fn c => c = #"\n")
                                               (String.explode s))
                  + lastNr - 1
      in
        (lastNr + 1, nr) :: countLines doc nr
      end

    val cDoc = Lst.zip doc (countLines doc 0)

    fun pp ((Doc (TeX, _, s)), (f,_)) = (pr s)
      | pp ((Doc (Sml, _, s)), (f,_)) =
      let
        val nr = Int.toString f
        val s =
          "\n\\begin{lstlisting}[language=sml,firstnumber="^nr^"]" ^
          s ^
          "\\end{lstlisting}\n"
      in
        pr s
      end
    fun ppPre () =
    let
      val s = ""
    in
      pr s
    end
  in
    (ppPre ();
    forall pp cDoc )
  end

  fun stripTeXComments inFileName outFileName =
  let
    val iin = TextIO.openIn inFileName
    val ins = ParserStreamIO.make iin
    val out = TextIO.openOut outFileName
    fun pr doc =
      forall (fn (Doc (Sml, _, s)) => TextIO.output (out, s) | _ => ()) doc
  in
    (parse (parseDoc () >>= return o pr) ins
    ; TextIO.closeOut out; TextIO.closeIn iin
    ;())
  end

  fun start inFileName outFileName markedSections =
  let
    val iin = TextIO.openIn inFileName
    val ins = ParserStreamIO.make iin
    val out = TextIO.openOut outFileName
  in
    (parse (parseDoc () >>= return o outputTeX out markedSections) ins
    ; TextIO.closeOut out; TextIO.closeIn iin
    ;())
  end

end;

