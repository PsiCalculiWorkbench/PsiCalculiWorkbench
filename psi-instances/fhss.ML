(**\label{sec:fhss-example}
\lstset{style=sml-literal}

In this section, we go through an implementation of a Psi-calculus instance
modelling Frequency hopping spread spectrum (FHSS). This instance showcases
terms with more complex structure than a name, although they are still
syntactic. Additionally, this instance features additional rules to the
transition constraint solver of the Pi-calculus instance to handle these terms.

This time we diverge from following the literate-programming style
as closely as in the Pi-calculus instance example
(Section~\ref{sec:pi-calculus-example}) by omitting non essential code but
preserving the order of code as it would appear in a file, thus we abstain
from numbering code lines.
We concentrate on the differences to the Pi-calculus instance arising from the
introduction of non-trivial terms; we leave out straightforward implementation
details and functionality which is transferable without much effort from the
Pi-calculus instance; we also omit the \SML{} structure declarations as it
should be clear now of which structures various \SML{} datatypes and
functions are part of.

\vspace{1em}

Here we reproduce from \cite[section 4.1.1]{lics++} a short description of
what FHSS is and what FHSS instance is modelling.

\begin{quote}
Wireless communication over a constant radio frequency has a number of
drawbacks. In a hostile environment a radio can be tuned in to the correct
frequency and monitor the communication which is also vulnerable to
jamming. A solution to these problems is to jump quickly between different
frequencies in a scheme called frequency hopping spread spectrum (FHSS),
first patented in 1942.  To eavesdrop it would then be necessary to
match both the order of the frequencies and the pace of switching. Jamming
is also made more difficult since the available power would have to be
distributed over many frequencies.
\end{quote}

*)(**[skip]*)
structure FHSSInstanceNom (* : PSI_INSTANCE_NOM *) =
struct
(**[default]*)(**

Let us start with a simple example, the following is a valid agent of the FHSS
instance:
\[
\out{\mathsf{nextFreq}(b)}\langle \mathsf{nextFreq}(b) \rangle . P
\;\; \pll \;\;
\inn{\mathsf{nextFreq}(\mathsf{nextFreq}(a))}{(x)} . Q
\]
which tries to communicate through channels
$\mathsf{nextFreq}(\mathsf{nextFreq}(a))$ and $\mathsf{nextFreq}(b)$, so in
order for the communication to succeed $b$ must be equal to
$\mathsf{nextFreq}(a)$. After a communication the agent continues as
\[
P \;\;\pll\;\; Q[x := \mathsf{nextFreq}(b)]
\]
or with a solution applied,
\[
(P \;\pll\; Q[x := \mathsf{nextFreq}(b)])[b := \mathsf{nextFreq}(a)]
\]


Let us define the FHSS instance formally (this definition is based
on~\cite[Section 4.1.1]{lics++}), we additionally introduce a $\top$ condition
as in the Pi-calculus instance.
\[
\begin{array}{rcl}
\mathbf{T} & \defn & \N \cup \{ \mathsf{nextFreq}(M) : M \in \mathbf{T} \} \\
\mathbf{C} & \defn & \{M = N : M,N \in \mathbf{T} \} \cup \{ \top \} \\
\mathbf{A} & \defn & \{ 1 \} \\
\unit   & \defn & 1 \\
\sch    & \defn & = \\
\ftimes & \defn & \lambda \langle \Psi_1, \Psi_2 \rangle . 1 \\
\vdash  & \defn &
    \{ \langle 1, M = M \rangle : M \in \mathbf{T} \}
    \cup \{ \langle 1, \top \rangle \}
\end{array}
\]
where $\N$ is countably infinite set of atomic names as usual and
$\top \notin \mathbf{T}$.

*)(**[skip]*)
  type     name      = string
(**[default]*)(**

The difference with Pi-calculus is the $\mathbf{T}$ nominal datatype.
Other nominal datatypes and operations are unchanged.

Unsurprisingly, the definition of the terms nominal datatype $\mathbf{T}$ forms
a carrier set for a term algebra. In a term algebra variables are part of the
carrier set (cf. Appendix \ref{sec:some-notions-from-universal-algebra}).

The signature is
\[
\Sigma = \{ \mathsf{nextFreq} \}
\]
where the function symbol $\mathsf{nextFreq}$ arity is 1.  Since we can use
names as variables, we invoke the $T$ constructor
(Definition~\ref{def:sigma-terms} in Appendix~\ref{sec:theory-preliminaries}) on
the above signature and names to get a set.  Given that $\mathbf{T}$ is a least
fixed-point of the above definition, and~$T(\Sigma, \N)$ constructs a least set,
inductively, they coincide
\[
T(\Sigma, \N) = \mathbf{T}
\]
and thus $\mathbf{T}$ is a carrier set of the
$\Sigma$-term algebra $\mathcal{T}(\Sigma, \N)$.


A natural choice to implement this datatype is \SML{}'s algebraic datatypes.
We have two cases: one for names, and one the function symbol.
*)
  datatype term = Name     of name
                | NextFreq of term
(**[skip]*)
  datatype condition = Eq of term * term | True
  datatype assertion = Unit
(**[default]*)(**


Because no binders are present in $\mathbf{T}$, the computation of the equality
on terms in the entailment is trivial, and we use the built-in \SML{}
equality to compute the syntactic equality.

*)(**[skip]*)
  val unit                     = Unit
  val chaneq                   = Eq
  fun compose _                = Unit
(**[default]*)
  fun entails (Unit,Eq (m, n)) = (m = n)
    | entails (Unit,True)      = true
(**[skip]*)
  fun new xvec          = StringName.generateDistinct xvec
  fun swap_name (a,b) n = StringName.swap_name (a,b) n
(**[default]*)(**

Obviously, any term of $\mathbf{T}$ always contains exactly one name. A channel
equivalence condition contains exactly two names, so we just do a structural
recursion to extract those names.

*)
  fun supportT (Name n)     = [n]
    | supportT (NextFreq m) = supportT m
  fun supportC (Eq (m, n))  = supportT m @ supportT n
    | supportC True         = []
(**[skip]*)
  fun supportA _            = []
(**[default]*)(**

The swapping of names in terms are easily implemented with the
function~\sml{swap_name}.
We only need to propagate the \sml{swap_name} function down to the
contained name.
*)
  fun swapT pi (Name n)      = Name (swap_name pi n)
    | swapT pi (NextFreq t)  = NextFreq (swapT pi t)
  fun swapC _  True          = True
    | swapC pi (Eq (t1, t2)) = Eq (swapT pi t1, swapT pi t2)
(**[skip]*)
  fun swapA _ _ = Unit
(**[default]*)(**

Again, as we do not have binders in terms we do not need to concern our selves
with a possibility of name capture whenever we do a substitution.
The function \sml{substT} implements a substitution function for terms. Given a
substitution sequence \sml{sigma} it first recursively gets to the name
of a term, and then tries to find a substitution mapping with that name.
If found returns the term from the mapping, otherwise it returns the name
unchanged.

*)
  fun substT sigma (Name a)     =
        (case List.find (fn (b,_) => a = b) sigma of
             NONE       => Name a
           | SOME (_,t) => t)
    | substT sigma (NextFreq n) = NextFreq (substT sigma n)
(**[skip]*)
  fun substC s True           = True
    | substC s (Eq (t1, t2)) = Eq (substT s t1, substT s t2)

  fun substA _ _ = Unit
(**[default]*)(**


As mentioned previously, alpha equivalence is the same as syntactic equivalence
for terms.
*)
  fun eqT _ (a,b) = a = b
(**[skip]*)
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b

end;

structure FHSSSymbolicInstance (* : SYMBOLIC_PSI_FLAT *) =
struct
  open FHSSInstanceNom

  fun var a = Name a

  structure Constraint = Constraint(FHSSInstanceNom)

  fun dom sigma = map (fn (n,t) => n) sigma
  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  structure L = NominalNameList(
      struct type atom = name val new = new end)
(**[default]*)(**

For finding a substitution function for a syntactic equation system (this is
what a transition constraint for FHSS is) we again employ the 
Martelli-Montanari (MM) unification algorithm. This time, as we are dealing with
more complex
terms, we reintroduce and adapt the rules used to solve the Pi-calculus instance
transition constraints (see section \ref{sec:pi-calculus-example}) to the FHSS
instance case and add two new rules\footnote{In fact, these two new rules are
required by the MM algorithm, but are not needed for Pi-calculus instance case.}
for dealing with
non-trivial terms. We refer to \cite{Klop92termrewriting} for more details on
MM, and to \cite{BN98} for the alternative presentation of the algorithm.

Here we present the rules for solving transition constraint for FHSS, a brief
description follows afterwards.
\[
\begin{array}{l}
(\nu \ve{a})\constr{\mathrm{nextFreq}(N) \sch \mathrm{nextFreq}(M)}
 \land  C  \rightarrowtail  (\nu\ve{a})\constr{N \sch M} \land C \\
\hfill \text{\textsc{(Decom)}} \\
%
(\nu \ve{a})\constr{\mathrm{nextFreq}(N) \sch a}
 \land
 C  \rightarrowtail  (\nu\ve{a})\constr{a \sch \mathrm{nextFreq}(N)} \land C \\
\hfill \text{\textsc{(Swap)}} \\
%
(\nu \ve{a})\constr{\top}
 \land  C
 \rightarrowtail
  C \\
\hfill \text{\textsc{(TrT)}} \\
%
(\nu \ve{a})\constr{a \sch a}
 \land  C
 \rightarrowtail
  C \\
\hfill \text{\textsc{(TrEq)}} \\
%
(\nu \ve{a})\constr{a \sch N}
 \land  C
 \stackrel{[a := N]}{\rightarrowtail}
  C[a := N] \\
 \qquad \text{if } a, N \freshin \ve{a} \;\land\;
        a\freshin N
\hfill \text{\textsc{(Elim)}} \\ \\
%
(\nu \ve{a})\constr{a \sch N}
 \land  C
 \rightarrowtail
    \blacksquare \\
 \qquad \text{if } a \not= N \;\land\;
   ( a \in n(N) \lor a \in\ve{a} \lor n(N) \subseteq \ve{a})
\hfill \text{\textsc{(Fail)}} \\ \\

\end{array}
\]

The \textsc{(Decom)} rule, as the name suggests, decomposes terms into
structurally smaller terms and returns the decomposition for further
unification,
since only the difference between terms is at play,
e.g.~the constraint
$\mathsf{nextFreq}(\mathsf{nextFreq}(a)) \sch \mathsf{nextFreq}(b)$
entails the solutions~$[b := \mathsf{nextFreq}(a)]$.
The \textsc{(Swap)} rule exchanges the positions of terms in channel equivalence
if the right hand side term is a name. With this rules we do not need to
introduce symmetric versions
of other rules.
The \textsc{(Elim)} rule produces a substitution mapping (a partial solution).
Such a substitution mapping is valid only when neither side of the equation
has restricted names, and the name on the left side is not in the term
of the right hand side (as this would give rise to an infinite term),
e.g.~constraints $(\nu\ve{a})\constr{a \sch \mathsf{nextFreq}(a)}$ are
disallowed. The
second check is also known by the name ``occurs check''
\cite{Klop92termrewriting}; more will be said about it later.
The second check has a second purpose, it also says that this is not a
trivial case (handled by \textsc{(TrEq)}).
And the \textsc{(Fail)} rule is triggered if it is not a trivial case and not a
\textsc{(Elim)} case. As before a solution -- a substitution sequence -- is
produced when there are no more rules to apply. See
\ref{sec:pi-calculus-example} for a simpler case.


The following example should make it clearer how the above rules interact.
Let us return to the agent we gave at the beginning of this section, but
let us swap the constituent agents over the parallel.
\[
\inn{\mathsf{nextFreq}(\mathsf{nextFreq}(a))}{(x)} . Q
\;\; \pll \;\;
\out{\mathsf{nextFreq}(b)}\langle \mathsf{nextFreq}(b) \rangle . P
\]

This agent gives rise to the transition constraint:
\[
(\nu\varepsilon)\constr{\mathsf{nextFreq}(\mathsf{nextFreq}(a)) \sch
    \mathsf{nextFreq}(b)}
\]

The course of unification rule application might look like:
\[
\begin{array}{rc}
(\nu\varepsilon)\constr{\mathsf{nextFreq}(\mathsf{nextFreq}(a)) \sch
    \mathsf{nextFreq}(b)}
        & \overset{}{\underset{\text{\textsc{(Decom)}}}{\rightarrowtail}} \\
(\nu\varepsilon)\constr{\mathsf{nextFreq}(a) \sch b}
        & \overset{}{\underset{\text{\textsc{(Swap)}}}{\rightarrowtail}} \\
(\nu\varepsilon)\constr{b \sch \mathsf{nextFreq}(a)}
        & \overset{[b:=\mathsf{nextFreq}(a)]%
            }{\underset{\text{\textsc{(Elim)}}}{\rightarrowtail}} \\
\mathbf{true}[b:=\mathsf{nextFreq}(a)] = \mathbf{true} &  \\
\end{array}
\]

Since there is only one \textsc{(Elim)} rule above, the computed substitution
sequence is $[b:=\mathsf{nextFreq}(a)]$, which is identical to the
substitution sequence we deduced at the beginning of the section.

In contrast, suppose we have a constraint:
\[
(\nu\varepsilon)\constr{a \sch \mathsf{nextFreq}(a)}
\]

The \textsc{(Fail)} rule would be triggered as $a$ is in the support of
$\mathsf{nextFreq}(a)$, i.e.~$a \in \{a\}$. The motivation of this rule is
that this kind of constraint gives rise to the infinite term:
\[
\mathsf{nextFreq}(\mathsf{nextFreq}(\cdots (\mathsf{nextFreq}(\cdots))\cdots))
\]

Obviously, this kind of term cannot be computed and it is not part
of the least fixed-point definition of $\mathbf{T}$.
*)(**[skip]*)

(**

The function \sml{freshL} checks if vectors given do not share a name, that is
$\ve{a}\freshin\ve{b}$.
*)
  fun freshL avec bvec =
    List.all (fn b => L.fresh b avec) bvec
(**[default]*)(**
The rules above produces a substitution sequences which composed gives a
substitution which is a Most General Unifier (cf.
Section~\ref{sec:pi-calculus-example} and \cite{Klop92termrewriting}).
The following function implements the above rules. It takes a
transition constraint and an accumulated substitution sequence and returns
either a complete substitution sequence for the constraint or a condition which
triggered a failure rule.  We also assume that the function \sml{composeSubst}
composing substitution sequences is defined
(Section~\ref{sec:pi-calculus-example}), and that the function \sml{freshL},
computing $\ve{a} \freshin \ve{b}$, is also defined.

*)
  fun mgu [] sigma = Either.RIGHT sigma
      (* (*@  \textsc{(TrT)} case @*) *)
    | mgu ((avec, Unit,  True )::cs) sigma =
      mgu cs sigma
      (* (*@  \textsc{(Decom)} case @*) *)
    | mgu ((avec, Unit, (Eq (NextFreq a, NextFreq b)))::cs)
          sigma =
        mgu ((avec, Unit, (Eq (a,b)))::cs) sigma
      (* (*@  \textsc{(Swap)} case @*) *)
    | mgu ((avec, Unit, (Eq (NextFreq a, Name b)))::cs)
          sigma =
        mgu ((avec, Unit, (Eq (Name b, NextFreq a)))::cs)
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
(**

Just like in the Pi-calculus example we implement the function \sml{solve} by
using the function \sml{mgu}.
*)
  fun solve cs =
    case mgu cs [] of
         Either.RIGHT sigma => Either.RIGHT [(sigma, Unit)]
       | Either.LEFT phi    => Either.LEFT  [phi]
(**[skip]*)

  structure BisimConstraint = BisimConstraint(FHSSInstanceNom)
  val solveBisim = NONE

end;



structure FHSSCalculus : C_PSI =
struct
  open FHSSSymbolicInstance

  fun printN n = n
(**[default]*)(**

At this point, we are only left with implementing the printing and parsing
functions, and most of them are directly transferable from Pi-calculus instance
example. We only describe the printing and parsing of terms; other details
are exactly as in the Pi-calculus instance.

Recall that we are using strings to represent names. The matter of printing a term
then becomes only to prepend the required amount of \sml{"nextFreq"}
strings.
*)
  fun printT (Name n) = n
    | printT (NextFreq t) = "nextFreq(" ^ printT t ^ ")"
(**[skip]*)
  fun printC True = "T"
    | printC (Eq (t1, t2)) =
        (printT t1) ^ " = " ^ (printT t2)
  fun printA _ = "1"
(**[default]*)(**

We use the same structures for parsing
as before in the Pi-calculus instance
(Section~\ref{sec:pi-calculus-example})
but this time we make their definitions visible in the current namespace. In
addition, we open the \sml{Missing} structure which provides some auxiliary
functions.  In particular, we use the construct \sml{</.../>}, which makes any
function, accepting a tuple as an argument, into a left associative infix
operator, e.g.~the function \sml{fun add (x,y) = x + y} could be used infix in
\sml{2 </add/> 5} to add two numbers and produce the result \sml{5}.


*)
  structure Parser = Parser(StringStream)
  structure Lex    = PsiParserBase(Parser)
(**[skip]*)
  local
    open Parser
    open Lex
    open Missing
  in
(**
Taken from the Pi-calculus
*)
  fun parseResult p s =
    case parse p (StringStream.make s) of
         RIGHT ((r,s)::_) => RIGHT r
       | RIGHT _ => Err.undefined ()
       | LEFT  _ => LEFT "Error parsing"
(**[default]*)(**

The grammar production rule for the terms are bit more interesting this time,
since it is recursive.

\begin{grammar}
<term> ::= `nextFreq' `(' <term> `)' | <identifier>
\end{grammar}

This rule is straightforward to express with an parser combinators. But before we
do that, we need to address a technicality arising from the usage of recursive
parser combinators. \SML{} is a functional programming language with eager
evaluation strategy, i.e.~function arguments are evaluated before they are applied
to a function. When using recursion in parser combinators we may get an
undesired effect that the parser combinator is applied too ``early'' i.e.~too
eagerly. In most cases we want the parser combinator to be
applied when the previous combinator in the sequence is completed, and not when
it becomes an argument to a sequencing operator. For tackling this we use the
\sml{delayed} function which takes a parser combinator function with type
\sml{unit -> 'a parser} and calls it only when the previous parser combinator
completes. An alternative is to use the sequencing operator \sml{>>=} even when
the result of a previous combinator is not needed and there is a need for a
recursive application.

Let us return to the function implementing the above grammar production rule.
The two alternatives of a grammar production are modelled with the combinator
\sml{choice} and using the previously described construct to make it into an infix
operator.  The first alternative is to match the string~\sml{"nextFreq"} 
and the opening parenthesis as tokens, then try to parse an inner term and
finally to match the matching closing parenthesis and returning the resulting
term.  The second alternative is to parse an identifier and return it as a name
term.  The function is quite similar to the production rule, alas a bit more
verbose since it is intertwined with actions.

*)
  fun term () =
        (stok "nextFreq" >> stok "(" >>
        (delayed term) >>=
        (fn t => stok ")" >> return (NextFreq t)))
    </choice/>
        (Lex.identifier >>= return o Name)
(**[skip]*)


  fun parseN s = parseResult (Lex.identifier) s
  fun parseT s = parseResult (term ()) s
  fun parseC s = parseResult (stok "T" >> return True) s
  fun parseA s = parseResult (stok "1" >> return Unit) s
  end

end;

structure FHSS = Command(FHSSCalculus);
(**[default]*)(**

This ends the FHSS instance example. Adding structured terms does not complicate
the instance significantly since the same known techniques apply, e.g.~the
standard mgu computation.

*)
