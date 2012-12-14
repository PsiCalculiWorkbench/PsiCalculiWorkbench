infixr 0 $
infix  3 <\
infix  3 \>
infix  3 <\\
infix  3 \\>
infixr 3 </
infixr 3 />
infixr 3 <//
infixr 3 //>
infix  1 |>

structure Fun :
sig
  val id    : 'a -> 'a
  val const : 'a -> 'b -> 'a
  val callWith: 'a -> ('a -> 'b) -> 'b
  val flip  : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val $     : ('a -> 'b) * 'a -> 'b
  val />    : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val </    : 'a * ('a -> 'b) -> 'b
  val //>   : ('a -> 'b -> 'c) * 'b -> 'a -> 'c
  val <//   : 'a * ('a -> 'b) -> 'b

  val <\    : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val \>    : ('a -> 'b) * 'a -> 'b
  val <\\    : 'a * ('a -> 'b -> 'c) -> 'b -> 'c
  val \\>    : ('a -> 'b) * 'a -> 'b
  val |>    : 'a * ('a -> 'b) -> 'b
end = struct
  fun id x       = x
  fun const x _  = x
  fun callWith x f  = f x
  fun flip f b a = f a b
  fun f $  x     = f x
  fun x |> f     = f x

  (* http://mlton.org/InfixingOperators *)
  fun x <\ f = fn y => f (x, y)     (* Left section      *)
  fun f \> y = f y                  (* Left application  *)
  fun x <\\ f = fn y => f x y     (* Left section      *)
  fun f \\> y = f y                  (* Left application  *)

  fun f /> y = fn x => f (x, y)     (* Right section     *)
  fun x </ f = f x                  (* Right application *)
  fun f //> y = fn x => f x y        (* Right section     *)
  fun x <// f = f x                  (* Right application *)

  (* infixing functions with 2-tuple as a domain *)
  (* left associative *)
  (* x1 </f1/> x2 </f2/> ... </fn/> x(n+1) *)

  (* right associative *)
  (* x1 <\f1\> x2 <\f2\> ... <\fn\> x(n+1) *)
end;

local open Fun in

structure Err :
sig
  exception Error of string
  val error      : string -> 'a
  val undefined  : string -> 'a
end
=
struct
  exception Error of string

  fun error     msg = raise Error msg
  fun undefined msg = raise Error $ "Undefined case: " ^ msg
end;

structure Opt :
sig
  val some       : ('a -> 'b) -> 'a option -> 'b option
  val filterSome : 'a option list -> 'a list
  val maybe      : 'b -> ('a -> 'b) -> 'a option -> 'b
  val maybeL     : (unit -> 'b) -> ('a -> 'b) -> 'a option -> 'b
  val always     : ('a -> 'b) -> 'a option -> 'b

  val bindO : 'a option -> ('a -> 'b option) -> 'b option
  val returnO : 'a -> 'a option
  val errorO : 'a -> 'b option
end = struct
  fun some f (SOME x) = SOME (f x)
    | some f     NONE = NONE

  fun maybe _ f (SOME x) = f x
    | maybe x _    NONE  = x

  fun maybeL _ g (SOME x) = g x
    | maybeL f _ NONE     = f ()

  fun always f (SOME x) = f x
    | always _  NONE    = Err.error "Application of 'always' failed."

  fun filterSome lst =
    map (fn (SOME x) => x | _ => raise Match) $
        List.filter (maybe false $ const true) lst

  fun bindO v f = maybe NONE f v
    (*case v of*)
         (*NONE => NONE*)
       (*| SOME x => f x*)

  fun returnO v = SOME v
  fun errorO x = NONE

end;


structure Tpl :
sig
  val fst      : 'a * 'b -> 'a
  val snd      : 'a * 'b -> 'b
  val curry    : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry  : ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
  val flip     : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val swap     : 'a * 'b -> 'b * 'a
  val tuple    : 'a -> 'b -> 'a * 'b
  val revTuple : 'b -> 'a -> 'a * 'b
end = struct
  fun fst (a,b)       = a
  fun snd (a,b)       = b
  fun curry f a b     = f (a,b)
  fun uncurry f (a,b) = f a b
  fun flip f a b     = f b a
  fun swap (a,b)      = (b,a)
  fun tuple a b       = (a,b)
  fun revTuple b a    = (a,b)
end;


structure Lst :
sig
  val empty        : 'a list -> bool
  val foldr        : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val foldl        : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val flatmap      : ('a -> 'b list) -> 'a list -> 'b list
  val flatmapmix   : ('a -> 'b list) -> 'a list -> 'b list
  val reduce       : ('a * 'a -> 'a) -> 'a list -> 'a
  val member       : ''a -> ''a list -> bool
  val insert       : ''a -> ''a list -> ''a list
  val union        : ''a list -> ''a list -> ''a list
  val intersection : ''a list -> ''a list -> ''a list
  val minus        : ''a list -> ''a list -> ''a list
  val cart_product : 'a list list -> 'a list list
  val all          : ('a -> bool) -> 'a list -> bool
  val any          : ('a -> bool) -> 'a list -> bool
  val exists       : ('a -> bool) -> 'a list -> bool
  val reverse      : 'a list -> 'a list
  val filter       : ('a -> bool) -> 'a list -> 'a list
  val sngl         : 'a -> 'a list
  val zip          : 'a list -> 'b list -> ('a * 'b) list
  val zipwith      : ('a * 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val intersperse  : 'a -> 'a list -> 'a list
  val enum         : int -> int -> int list
  val power        : 'a list -> 'a list list
  val eq           : ('a * 'b -> bool) -> 'a list -> 'b list -> bool
  val forall       : ('a -> unit) -> 'a list -> unit
  val nubBy        : ('a * 'a -> bool) -> 'a list -> 'a list
  val nub          : ''a list -> ''a list
end = struct
  open List
  open Err

  fun empty [] = true
    | empty _ = false

  (* uncurried versions *)
  fun foldr f i l = List.foldr (Tpl.uncurry f) i l
  fun foldl f i l = List.foldl (Tpl.uncurry f) i l
  fun flatmap f l = List.foldr (fn (a,b) => (f a)@b) [] l
  fun flatmapmix f l = 
      List.foldr (fn (a,b) => List.revAppend(b,(f a))) [] l
  fun reduce f []  = undefined "Lst.reduce []"
    | reduce f [a] = a
    | reduce f (x::xs) = List.foldl f x xs

  fun member x lst     = exists (fn a => a = x) lst
  fun insert x ys      = if member x ys then ys else x::ys
  fun union xs ys      = foldl insert ys xs
  fun intersection a b = filter (flip member $ b) a
  fun minus seta setb  = filter (not o (flip member) setb) seta

  (* aliases *)
  val any = exists

  fun reverse l =
  let
    fun reverse' [] n = n
      | reverse' (x::xs) n = reverse' xs (x::n)
  in
    reverse' l []
  end

  fun cart_product [] = [[]]
    | cart_product (l::ls) =
    List.concat $
        map (fn x => map (fn y => x :: y) $ cart_product ls) l

  fun sngl a = [a]

  fun zip a b = ListPair.zip (a,b)

  fun zipwith f a b = List.map f $ zip a b

  fun intersperse s []           = []
    | intersperse s [x]          = [x]
    | intersperse s (a::b::rest) = [a, s] @ (intersperse s (b::rest));

  fun enum' a b l =
    if a > b then l else
    if a = b + 1
        then l
        else enum' a (b-1) (b::l)
  fun enum a b = enum' a b []

  fun power [] = [[]]
    | power (e::es) = let val p = power es in p @ map (fn x => e::x) p end

  fun eq elEq [] []           = true
    | eq elEq (x::_) []       = false
    | eq elEq [] (y::_)       = false
    | eq elEq (x::xs) (y::ys) = x </elEq/> y andalso eq elEq xs ys


  val forall = List.app

  fun nubBy eq [] = []
    | nubBy eq (x::xs) = x :: nubBy eq (List.filter (not o (eq/>x)) xs)

  fun nub xs = nubBy (op=) xs
end;

structure Either :
sig
  datatype ('a, 'b) either = LEFT of 'a | RIGHT of 'b

  val either    : ('a -> 'c) -> ('b -> 'c) -> ('a,'b) either -> 'c
  val rights    : (('a,'b) either) list -> 'b list
  val lefts     : (('a,'b) either) list -> 'a list
  val partition : ('a,'b) either list -> 'a list * 'b list

  val right : ('a,'b) either -> 'b
  val left : ('a,'b) either -> 'a

  (* Monad operations *)
  val bindE   : ('a,'b) either -> ('b -> ('a,'d) either) -> ('a,'d) either
  val returnE : 'b -> ('a, 'b) either
  val errorE  : 'a -> ('a, 'b) either
end
=
struct
  datatype ('a, 'b) either = LEFT of 'a | RIGHT of 'b

  fun right (RIGHT x) = x
    | right (LEFT _) = Err.error "Either.right failed"

  fun left (RIGHT _) = Err.error "Either.left failed"
    | left (LEFT x) = x

  fun either f _ (LEFT  a) = f a
    | either _ g (RIGHT b) = g b

  fun rights e =
    map (fn (RIGHT a) => a | _ => Err.error "Either.rights impossible case") $
        List.filter (fn (RIGHT _) => true | _ => false) e

  fun lefts e =
    map (fn (LEFT a) => a | _ => Err.error "Either.lefts impossible case") $
        List.filter (fn (LEFT _) => true | _ => false) e

  fun partition e = (lefts e, rights e)

  fun bindE v f =
    case v of
         LEFT x => LEFT x
       | RIGHT y => f y

  fun returnE v = RIGHT v

  fun errorE e = LEFT e

end;


structure Missing =
struct
  open Fun
  open Opt
  open Tpl
  open Lst
  open Err
  open Either
end;

end; (* local open Fun in *)

