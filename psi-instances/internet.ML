(* uses src/workbench *)

structure WebInstanceNom (* : PSI_INSTANCE_NOM *) =
struct
  type     name      = string
  datatype term
    = ADDR
    | Ch of term * string
    | Name of name


  datatype condition = Eq of term * term | True
  datatype assertion = Unit

  val unit                     = Unit
  val chaneq                   = Eq
  fun compose _                = Unit

  fun entails (Unit,Eq (m, n)) = (m = n)
    | entails (Unit,True)      = true

  fun new _ xvec        = StringName.generateDistinct xvec
  fun swap_name (a,b) n = StringName.swap_name (a,b) n

  fun supportT (Name n)   = [n]
    | supportT (Ch (n,s)) = supportT n
    | supportT ADDR       = []
  fun supportC (Eq (m, n))  = supportT m @ supportT n
    | supportC True         = []

  fun supportA _            = []

  fun swapT pi (Name n)    = Name (swap_name pi n)
    | swapT pi (Ch (n,s))    = Ch (swapT pi n, s)
    | swapT pi ADDR = ADDR
  fun swapC _  True        = True
    | swapC pi (Eq (t1, t2)) = Eq (swapT pi t1, swapT pi t2)

  fun swapA _ _ = Unit

  fun substT sigma ADDR = ADDR
    | substT sigma (Name a) =
        (case List.find (fn (b,_) => a = b) sigma of
             NONE       => Name a
           | SOME (_,t) => t)
    | substT sigma (Ch (t,s)) = Ch (substT sigma t, s)

  fun substC s True           = True
    | substC s (Eq (t1, t2)) = Eq (substT s t1, substT s t2)

  fun substA _ _ = Unit
  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b

end;


structure WebSymbolicInstance (* : SYMBOLIC_PSI_FLAT *) =
struct
  open WebInstanceNom

  fun var a = Name a

  structure Constraint = Constraint(WebInstanceNom)

  fun dom sigma = map (fn (n,t) => n) sigma
  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  structure L = NominalNameListUnsorted(
      struct type atom = name val new = new end)

  fun freshL avec bvec =
    List.all (fn b => L.fresh b avec) bvec

  fun mgu [] sigma = Either.RIGHT sigma
      (* (*@  \textsc{(TrT)} case @*) *)
    | mgu ((avec, Unit,  True )::cs) sigma =
      mgu cs sigma
    | mgu ((avec, Unit,  Eq (ADDR, ADDR) )::cs) sigma =
      mgu cs sigma

      (* (*@  \textsc{(Decom)} case @*) *)
    | mgu ((avec, Unit, (eqt as (Eq (Ch (a,s), Ch (b,s')))))::cs)
          sigma =
          if s = s' then
            mgu ((avec, Unit, (Eq (a,b)))::cs) sigma
          else Either.LEFT [eqt]


    | mgu ((avec, Unit, (eqt as Eq (ADDR, Ch(a,b))))::cs) sigma =
        Either.LEFT [eqt]

    | mgu ((avec, Unit, (eqt as Eq (Ch(a,b), ADDR)))::cs) sigma =
        Either.LEFT [eqt]

      (* (*@  \textsc{(Swap)} case @*) *)
    | mgu ((avec, Unit, (Eq (ADDR, Name b)))::cs) sigma =
        mgu ((avec, Unit, (Eq (Name b, ADDR)))::cs) sigma
    | mgu ((avec, Unit, (Eq (Ch (a,s), Name b)))::cs)
          sigma =
        mgu ((avec, Unit, (Eq (Name b, Ch(a,s))))::cs)
            sigma
      (* (*@  If the name is on the left hand side of the channel equivalence @*) *)
    | mgu ((avec, Unit, (Eq (Name a, n)))::cs) sigma =
       if Name a = n then mgu cs sigma (* (*@  \textsc{(TrN)} case @*) *)
         else
           (* (*@ if $a\freshin\ve{a} \;\land\; \ve{a}\freshin N \;\land\; a\freshin N $ @*) *)
           if L.fresh a avec andalso
              freshL avec (supportT n) andalso
              L.fresh a (supportT n)
             then
                (* compose the produced substitution
                 * sequence with the accumulated and
                 * apply it to the residual *)
               mgu (Constraint.subst cs [(a, n)])
                   (composeSubst sigma (a, n))
             else (* otherwise (*@ \textsc{(Fail)} @*) *)
               Either.LEFT [(Eq (Name a, n))]

  fun solve cs =
    case mgu cs [] of
         Either.RIGHT sigma => Either.RIGHT [(sigma, Unit)]
       | Either.LEFT phi    => Either.LEFT  [phi]

  structure BisimConstraint = BisimConstraint(WebInstanceNom)
  val solveBisim = NONE
end;



structure WebCalculus : C_PSI =
struct
  open WebSymbolicInstance

  val addr = "www.stuff.com"

  fun printN n = n
  fun printT (ADDR) = "/" ^ addr ^ "/"
    | printT (Ch (t,s)) = "[" ^ printT t ^ ", " ^ s ^ "]"
    | printT (Name n) = n
  fun printC True = "T"
    | printC (Eq (t1, t2)) =
        (printT t1) ^ " = " ^ (printT t2)
  fun printA _ = "1"

  structure Parser = Parser(StringStream)
  structure Lex    = PsiParserBase(Parser)

  local
    open Parser
    open Lex
    open Missing
  in

  fun parseResult p s =
    case parse p (StringStream.make s) of
         RIGHT ((r,s)::_) => RIGHT r
       | RIGHT _ => Err.undefined ()
       | LEFT  _ => LEFT "Error parsing"

  fun page () =
                Lex.identifier >>=
    (fn part1 => str "." >> Lex.identifier >>=
    (fn part2 => return (part1 ^ "." ^ part2)))

  fun term () =
        (stok "/" >> stok addr >> stok "/" >> return ADDR)
    </choice/>
        (stok "[" >> delayed term >>=
        (fn sock => stok "," >> page () >>=
        (fn file => stok "]" >> return (Ch (sock,file)) )))
    </choice/>
        (Lex.identifier >>= return o Name)

  fun parseN s = parseResult (Lex.identifier) s
  fun parseT s = parseResult (term ()) s
  fun parseC s = parseResult (stok "T" >> return True) s
  fun parseA s = parseResult (stok "1" >> return Unit) s
  end

end;

structure Web = Command(WebCalculus);
