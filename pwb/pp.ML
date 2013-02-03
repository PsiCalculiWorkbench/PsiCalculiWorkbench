(* uses pwb/missing *)


signature PRETTY_PRINTER =
sig
  type document

  val empty  : document
  val join   : document * document -> document
  val nest   : int -> document -> document
  val text   : string -> document
  val line   : document
  val group  : document -> document
  val fill : document list -> document
  val pretty : int -> document -> string
  val plain : document -> string
end;


functor PrettyPrinterAux(PP: PRETTY_PRINTER) :
sig
  val comma           : PP.document
  val sep             : PP.document -> PP.document list -> PP.document
  val commaSep        : PP.document list -> PP.document
  val filledCommaSep  : PP.document list -> PP.document
  val nl              : PP.document * PP.document -> PP.document
  val sp              : PP.document * PP.document -> PP.document
  val enquote         : PP.document -> PP.document -> PP.document
end =
struct
  open Missing;
  open PP;

  val comma = text ","

  fun sep s l           = List.foldr join empty (intersperse s l)
  fun nl (x,y)          = x </join/> line </join/> y
  fun sp (x,y)          = x </join/> text " " </join/> y
  fun commaSep l        = sep (comma </join/> text " ") l

  fun filledCommaSep docs =
  let
    fun attatchComma [] = []
      | attatchComma (doc::[]) = [doc]
      | attatchComma (doc::(doc'::docs)) =
        (doc </join/> comma) :: (attatchComma (doc'::docs))
  in
    fill $ attatchComma docs
  end 

  fun enquote q doc     = q </join/> doc </join/> q
end;


structure WPrettyPrinter : PRETTY_PRINTER =
struct
local open Missing in

  datatype document
    = NIL
    | JOIN  of document * document
    | NEST  of int * document
    | TEXT  of string
    | LINE
    (* invariant left and right documents must flatten to the same document *)
    | GROUP of document * document


  datatype doc
    = Nil
    | Text of string * doc
    | Line of int * doc


  val empty = NIL
  val join = JOIN
  val nest = curry NEST
  val text = TEXT
  val line = LINE

  fun flatten NIL = NIL
    | flatten (JOIN (x, y)) = JOIN (flatten x, flatten y)
    | flatten (NEST (i, x)) = NEST (i, flatten x)
    | flatten (TEXT s) = TEXT s
    | flatten LINE = TEXT " "
    | flatten (GROUP (x, y)) = flatten x

  fun group x = GROUP (flatten x, x)

  fun enum' a b l = if b >= a then enum' a (b - 1) (b :: l) else l
  fun enum a b = enum' a b []

  fun copy i x = String.concat $ map (const x) $ enum 1 i

  (* Tail recursive version  *)

  fun layout' Nil t = t
    | layout' (Text (s, x)) t = layout' x (s :: t)
    | layout' (Line (i, x)) t = layout' x ((copy i " ")::"\n"::t)

  fun layout x = String.concat $ reverse $ layout' x []

 (* Lazy version *)

  datatype lazy_doc
    = LNil
    | LText of string * (unit -> lazy_doc)
    | LLine of int * (unit -> lazy_doc)

  fun fits' w x =
    if w < 0 then false
    else
      case x of
           LNil => true
         | LText (s, x) => fits' (w - String.size s) (x ())
         | LLine (i, x) => true


  fun better' w k x y = if fits' (w - k) x then x else y ()

  fun be' w k []                     = LNil
    | be' w k ((i, NIL)::z)          = be' w k z
    | be' w k ((i, JOIN (x, y))::z)  = be' w k ((i, x)::(i,y)::z)
    | be' w k ((i, NEST (j, x))::z)  = be' w k ((i+j, x)::z)
    | be' w k ((i, TEXT s)::z)       = LText (s, fn () => be' w (k + String.size s) z)
    | be' w k ((i, LINE)::z)         = LLine (i, fn () => be' w i z)
    | be' w k ((i, GROUP (x, y))::z) =
        better' w k (be' w k ((i, x)::z)) (fn () => (be' w k ((i, y)::z)))

  fun forceDoc LNil = Nil
    | forceDoc (LText (s,x)) = Text (s, forceDoc $ x ())
    | forceDoc (LLine (i,x)) = Line (i, forceDoc $ x ())

  fun best' w k x = forceDoc $ be' w k [(0, x)]

  val best = best'

  fun pretty w x = layout $ best w 0 x

  fun plain NIL = ""
    | plain (JOIN (a,b)) = plain a ^ plain b
    | plain (NEST (i,a)) = plain a
    | plain (LINE) = "\n"
    | plain (TEXT x) = x
    | plain (GROUP (_,a)) = plain a




  fun nl (x,y) = x </join/> line </join/> y
  fun sp (x,y) = x </join/> text " " </join/> y

  fun fill [] = empty
    | fill [x] = x
    | fill (x::y::zs) =
        GROUP (
            flatten x </sp/> fill (flatten y :: zs),
            x </nl/> fill (y :: zs))

(*
  (* Example *)
  datatype tree = Node of string * (tree list)

  fun showTrees [t] = showTree t
    | showTrees (t::ts) = showTree t <\join\> text ","
                                     <\join\> line
                                     <\join\> showTrees ts

  and showBracket [] = empty
    | showBracket ts = text "[" <\join\> nest 1 (showTrees ts)
                                <\join\> text "]"

  and showTree (Node (s, ts)) =
    text s <\join\> nest (String.size s) (showBracket ts)

  val sampleTree =
    Node ("aaa", [ Node ("bbbbb", [Node ("ccc", []), Node ("dd", [])]),
                   Node ("eee", []),
                   Node ("ffff", [Node ("gg", []), Node ("hhh", []),
                                  Node ("ii", [])])
                 ])

  val s =
    text "a" </join/>
        nest 2 (line </join/> text "b" </join/>
            nest 2 (line </join/> text "c" </join/>
                nest 2 (line </join/> text "d" )))

  val x =
    fill $ map
        (fn x =>
        let val s = Char.toString x
        in
          nest 2 (line </join/> text s)
        end)
     $ String.explode "abcdefg"
*)

end;
end;
