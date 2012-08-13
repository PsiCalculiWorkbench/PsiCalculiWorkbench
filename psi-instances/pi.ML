(**\label{sec:pi-calculus-example}
\lstset{style=sml-numbered-literal}

As our first example we will implement a Pi-calculus symbolic instance based
on~\cite[Section 2.4]{lics++} with some minor divergence
to the Psi-calculus nominal datatypes. The Pi-calculus instance does \emph{not} feature
the more advanced capabilities of Psi-calculus, e.g.~non-trivial assertions, and
terms with binders, therefore it is a perfect means to show the mechanics of
implementing an instance without concerning ourselves with more intricate
details.

This section is a complete step-by-step
presentation of the \SML{} implementation of the Pi-calculus instance in
literate programming style. \SML{} lines are numbered to make a clear
distinction between the running text and the \SML{} code.

The instance is defined in three steps:

\begin{itemize}
\item First we define nominal datatypes, equivariant operators, substitution
functions and functions deciding alpha equality. These requirements are
listed in the \sml{PSI_INSTANCE_NOM} signature.

\item Next we define the requirements needed to construct a symbolic
Psi-calculus simulator on the instance. The requirements are a function which
maps names to terms, a constraint solver for transition constraints, and a
constraint solver for constraints produced by the bisimulation algorithm.  The
\sml{SYMBOLIC_PSI_FLAT} signature satisfies the requirements for this step.

\item The final step is to define functions for pretty printing and parsing
the nominal datatypes. The signature for this is \sml{C_PSI}.
\end{itemize}

The previously mentioned signatures in fact are part of the \sml{C_PSI} interface
and \sml{PSI_INSTANCE_NOM} $\subset$ \sml{SYMBOLIC_PSI_FLAT}
$\subset$ \sml{C_PSI}. Indeed, the file looks like the following:
%
%% All that just for centering the listing
\begin{center}
\begin{tabular}{c}
{
\begin{lstlisting}[boxpos=c,language=sml,numbers=none,frame=]
structure PiInstanceNom      = struct
  ...
end;
structure PiSymbolicInstance = struct
  open PiInstanceNom
  ...
end;
structure PiCalculus : C_PSI = struct
  open PiSymbolicInstance
  ...
end;
Pi = Command(PiCalculus);
\end{lstlisting}
}
\end{tabular}
\end{center}

This splitting of structures for implementing one signature is because of
\SML{} lack of mutually recursive definitions for structures, as we need
to refer to functions and datatypes when implementing the constraint
solvers, printers and parsers. The first two structures are not restricted
to the signature, otherwise it would close the datatype constructors.

The following text will be divided in three sections accordingly.



\subsubsection*{Instance definition}

First we will define \SML{} datatypes to represent nominal datatypes, then the
\SML{} functions implementing equivariant operators, next the nominal
equivariant functions on \SML{} datatypes, making those datatypes full fledged
nominal datatypes, and substitution functions.

*)
structure PiInstanceNom (* : PSI_INSTANCE_NOM  *) =
struct
(**
Before we begin writing down datatypes, let us look at the definition of nominal
datatypes for Pi-calculus instance as defined in \cite{lics++}.  We diverge here
from \cite{lics++} by extending $\mathbf{C}$ with condition $\top$
to represent an always entailed condition, such that we can encode \mbox{$P + Q$}
as $\case{\ci{\top} P \casesep \ci{\top} Q}$, rather than $(\nu a)\case{\ci{a =
a} P \casesep \ci{a = a} Q}$ where we would need to introduce a new name.

\index{instace!pi-instance}
\[
\begin{array}{rcl}
\mathbf{T} & \defn & \N \\
\mathbf{C} & \defn & \{a = b : a,b \in \mathbf{T} \} \cup \{ \top \} \quad \text {where } \top \not\in \mathbf{T} \\
\mathbf{A} & \defn & \{ 1 \} \\
\end{array}
\]

where $\N$ is countably infinite set of atomic \emph{names} as usual.

A good candidate to represent names is the \sml{string} type, since the
framework provides the structure \sml{StringName} with default functionality,
and \sml{term} is defined as name.  $\mathbf{C}$ forms a carrier
for a condition term algebra, hence it is only natural to represent it with
algebraic datatypes%
\footnote{
It is worth noting that an instance implementor is free to choose any \SML{}
datatypes for implementing nominal datatypes as long it is possible to provide
functions required by the \sml{NOMINAL} signature for the corresponding types.
}
of \SML{}, in \sml{condition} below.  \sml{Eq (a,b)}
corresponds to $a = b$ and \sml{T} to $\top$, and \sml{assertion} is an empty
data constructor \sml{Unit}.


*)
  type name          = string
  type term          = name
  datatype condition = Eq of term * term | T
  datatype assertion = Unit
(**

Next we turn to model the operators of Psi-calculus.
Let us recall the definition of the operators. The difference with \cite{lics++}
is that we always entail~$\top$.

\[
\begin{array}{rcl}
\sch    & \defn & = \\
\ftimes & \defn & \lambda \langle \Psi_1, \Psi_2 \rangle . 1 \\
\unit   & \defn & 1 \\
\vdash  & \defn & \{ \langle 1, a = a \rangle : a \in \N \} \cup \{ \langle 1, \top \rangle \}
\end{array}
\]

As we can see, channel equivalence is defined as an equality condition.
This is trivial in
our \SML{} representation, \sml{chaneq} below. The composition and the
unit of assertions are straightforward and the \SML{} code is close to the above
definition.
The entailment, $\vdash$, relation is defined as a boolean function on the
\sml{assertion} and \sml{condition} datatypes. The \sml{assertion} datatype
has only one constructor, therefore the function \sml{entails} has two cases:
\sml{Eq(m,n)} computes a \sml{string} equality on \sml{m} and \sml{n},
and \sml{T} always returns \sml{true}.
*)
  fun chaneq  (a,b)            = Eq (a,b)
  fun compose (psi1,psi2)      = Unit
  val unit                     = Unit
  fun entails (Unit,Eq (m, n)) = (m = n)
    | entails (Unit,T)         = true
(**
The function \sml{swap_name} is not necessary for the implementation of the
instance and it is derived by the \sml{Command} functor, but we need it for the
definitions of the swapping function, and the substitution function. The
\sml{swap_name} function implements the usual swap function on names $(a\; b)
\cdot n$.  The \sml{StringName} structure provides a default implementation for
generating new names and swapping names for the type \sml{string} which we use
here.

*)
  fun swap_name (a,b) n = StringName.swap_name (a,b) n
(**
The \sml{new} function is used for generating fresh names, the requirement is
that \sml{new} provides a name which is not in the \sml{xvec} list,
i.e.~$(\forall n \in \ve{x})  n \not= new (\ve{x})$. Again \sml{StringName}
provides the default implementation.
*)
  fun new xvec = StringName.generateDistinct xvec
(**
The Pi-calculus terms, conditions and assertions do not have binders, thus the
implementation of the \emph{support} is routine. The support is represented as a
list of names.  The function \sml{supportT} computes the term support, and as we
have names as our terms we only return the given name as a singleton list. The
function \sml{supportC} result can contain two names or none, and \sml{supportA}
returns an empty list.
*)
  fun supportT n           = [n]
  fun supportC (Eq (a, b)) = [a, b]
    | supportC  T          = []
  fun supportA _           = []
(**


As terms are just names, swapping a name in a term is the same as applying the
\sml{swap_name} function. Similarly for conditions while assertions are not
affected by swapping.
*)
  fun swapT pi n = swap_name pi n
  fun swapC _  T = T
    | swapC pi (Eq (t1, t2)) =
        Eq (swap_name pi t1, swap_name pi t2)
  fun swapA _ _  = Unit
(**


We also require an instance to provide an $\alpha$-equivalence for the
nominal datatypes. All the equality functions take as a first argument
a function to be called for deciding $\alpha$-equality for a datatype with
binders.
None of the nominal datatypes in Pi-calculus feature binders, and so
$\alpha$-equality is just syntactic equality, as can be seen below expressed
with built-in \SML{} equality and the first argument ignored.
However, it is worth mentioning how to use these functions to implement
an $\alpha$-equality for nominal datatypes with binders which bind into the whole
instance of a datatype.

Consider the lambda calculus language
\[
M,N ::= \lambda x . M \;|\; M N \;|\; x
\]
we define the nominal set of the terms of the lambda calculus as
\[
\mathbf{T} =
               \{ \lambda x . N : x\in\mathcal{N} \land
                                  N\in\mathbf{T} \}
          \cup \{ M N : M \in\mathbf{T} \land N\in\mathbf{T} \}
          \cup \mathcal{N}
\]
and the \SML{} datatype for terms is
\[
\text{\sml{datatype lam = Lam of name * lam
                     | App of lam * lam
                     | Var of name}}
\]
with nominal operations defined on it as expected. Thus a possible
implementation of $\alpha$-equality over \sml{lam} terms may be:
\begin{center}
\begin{tabular}{c}
{
\begin{lstlisting}[boxpos=c,language=sml,numbers=none,frame=]
fun eqT aEq (Lam (x,m), Lam (y,n)) =
        aEq ((x,m), (y,n))
  | eqT aEq (App (n,m), App (n',m')) =
        eqT aEq (n,n') andalso eqT aEq (m,m')
  | eqT aEq (Var x, Var y) =
        x = y
  | eqT _ _ = false
\end{lstlisting}
}
\end{tabular}
\end{center}

In the first case, two lambda abstractions are equated. We make use of the
provided \sml{aEq} function, which takes two tuples, where each tuple has as a
first member a binder and as a second a term in which the binder binds into. The
function \sml{aEq} finds a fresh name for both terms and swaps both bound names
with that name in those terms, and then calls back into \sml{eqT} with the
swapped name terms.  This kind of mutual recursive behaviour of functions
\sml{aEq} and \sml{eqT} relates to the Nominal Logic axiom \textbf{A1} from
\cite{Pitts02nominallogic}
\[
a.x = a'.x' \iff
    (a = a' \land x = x') \lor (a'\freshin x \land x' = (a\,a')x)
\]
where $a.x$ is an abstraction with $a$ being a binder binding into $x$:
in our setting,
the function \sml{eEq} does the right hand side judgment, and
the equating of terms $x$ and $x'$ are done by the function \sml{eqT}.

The $\alpha$-equality of application case is just a matter of recursively
calling \sml{eqT} with structurally smaller terms and by passing along the same
\sml{aEq}.  Equating variables is just checking their name equality.

Since, as mentioned, Pi-calculus terms do not feature terms with binders,
therefore we just ignore the provided function and use the builtin \SML{}
equality.
*)
  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b
(**
Next we define a substitution function on the nominal datatypes. Each substitution
function takes a substitution sequence \sml{sigma} (a list of name and term
pairs) and an instance of a nominal datatype.

The function \sml{substT} finds a matching name in \sml{sigma}, if found it
returns the pairing term (name), otherwise it returns the name unchanged.
\sml{substC} distributes as \sml{substT}, and assertions are not affected by the
substitution.
*)
  fun substT sigma n =
    case List.find (fn (x,_) => x = n) sigma of
           NONE       => n
         | SOME (_,t) => t
  fun substC sigma T             = T
    | substC sigma (Eq (t1, t2)) =
        Eq (substT sigma t1, substT sigma t2)
  fun substA sigma Unit          = Unit
(**

This ends the first part of definitions.
*)
end;
(**

We need to close this structure as this structure's definitions will be used by
functors in the structure \sml{PiSymbolicInstance}.




\subsubsection*{Symbolic instance definition}

We continue by defining extra requirements for the symbolic Psi-calculus and by
implementing a constraint solver for a symbolic simulator and symbolic
bisimulation checker.

\phantomsection\label{sec:pi-calculus-example-struct}
*)
structure PiSymbolicInstance (* : SYMBOLIC_PSI_FLAT *) =
struct
(** First we include the previously defined structure. *)
  open PiInstanceNom
(**
Additionally the symbolic Psi-calculus requires that names should be among the
terms (Definition~\ref{def:entailmentrelation}), i.e. $\N \subseteq \mathbf{T}$.
This is modeled in the tool's framework by the function 
\sml{var : name -> term}; in our case it is the identity function.
*)
  fun var x = x
(**

Now we turn our attention to solving the transition constraints.
Before we can do anything useful we need to define the \sml{Constraint}
sub-structure which implements constraint datatypes and some
useful functions, like substitution and nominal functions.

The functor \sml{Constraint} defines the constraints needed for the
simulator (symbolic operational semantics), of the form:
\[
\begin{array}{lcl}
C,C' & ::= & (\nu\ve{a})\constr{\Psi \vdash \varphi} \\
  &  |  & C \land C'
\end{array}
\]

The $C$ constrain \sml{Constraint.constraint} is a synonym for
\sml{Constraint.atomic list} and $(\nu\ve{a})\constr{\Psi \vdash \varphi}$ is
\sml{Constraint.atomic (avec, psi, phi)}. These datatypes are nominal
datatypes, meaning they have \sml{swap}, \sml{new}, etc.~defined on
them in
the \sml{Constraint} structure. The \sml{Constraint} functor also
provides a default implementation of capture avoiding substitution.
As we can see, the functor uses the definitions from \sml{PiInstanceNom},
which is one of the reasons we need to split the structure.
*)
  structure Constraint = Constraint(PiInstanceNom)
(**
The Pi-calculus instance conditions are syntactic and their
interpretation is syntactical equality on names defined by the
entailment relation. Furthermore we can view, the
transition constraint as a syntactic equation system. In order
to solve this system, we implement a syntactic unification algorithm
known as Martelli-Montanari algorithm. We use the form of algorithm
given in \cite{Klop92termrewriting}, which treats equations as a sequence
of goals rather than a term rewriting system since it is easier to
implement in our framework.

The outcome of a successful unification is a substitution sequence. This
sequence is computed by composing smaller sequences at an appropriate
algorithm step, as we will see later. We only need a special case where
substitution sequence is extended with a new substitution clause.

\[
\lsubst{\ve{L}}{\ve{x}}\lsubst{L'}{x'} =
\left\{
  \begin{array}{ll}
  \lsubst{\ve{L}\lsubst{L'}{x'}}{\ve{x}} & \text{ if } x' \in \ve{x} \\
  \lsubst{\ve{L}\lsubst{L'}{x'}}{\ve{x}} \cup \lsubst{L'}{x'} & \text{ if } x' \not\in \ve{x}
  \end{array}
\right.
\]

In \SML{} a substitution sequence is represented as a list of pairs of
name and term. Hence getting the domain $\ve{x}$ of $\lsubst{\ve{L}}{\ve{x}}$
is just a matter of taking the first member of each pair.
*)
  fun dom sigma = map (fn (n,t) => n) sigma
(**

Below is the implementation of the substitution sequence composition given
above, where \sml{sigma} is $\lsubst{\ve{L}}{\ve{x}}$ and \sml{s}
is $\lsubst{L'}{x'}$. So firstly it applies the substitution \sml{s} to
the range of \sml{sigma} and then adds \sml{s} to the sequence if $x'$ is not
in the domain of \sml{sigma}.

*)
  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end
(**
Next we present the unification rules tailored to the Pi-calculus case.
We omit the assertion from the constraint, since
it is always unit, we write~$(\nu\ve{a})\constr{\varphi}$ for
$(\nu\ve{a})\constr{\unit \vdash \varphi}$, and we write
$\constr{\varphi}$ for $(\nu\varepsilon)\constr{\varphi}$.

These rules solve the unification problem for the Pi-calculus instance.
\[
\begin{array}{lcccll}
(\nu \ve{a})\constr{a \sch b} & \land & C  & \overset{[b := a]}{\rightarrowtail}
    & C{[b := a]} \;\text { if }  a,b\freshin \ve{a} \text{ and } a\freshin b &
    \text{\textsc{(Elim)}}\\

(\nu \ve{a})\constr{a \sch a} & \land & C & \rightarrowtail & C &
    \text{\textsc{(Tr1)}} \\

(\nu \ve{a})\constr{\top} & \land & C & \rightarrowtail & C &
    \text{\textsc{(Tr2)}} \\

(\nu \ve{a})\constr{a \sch b} & \land & C & \rightarrowtail & \blacksquare
    \;\text { if } a\freshin b \text{ and } a \in\ve{a} \lor b \in \ve{a} &
    \text{\textsc{(Fail)}}
\end{array}
\]

The first rule, (\textsc{Elim}), produces a singleton substitution sequence and
applies that to the residual whenever both names are free and are not the same.
Notice that in the substitution the order of the names are swapped. This is done
because when an agent does an input or an output the fresh name generated for
the subject name is placed on the right hand side of the equality. In this
manner we will always be substituting away the generated name, in order to give
a more ``informative'' substitution sequence.  (\textsc{Fail}) rule says that
there is no name which can be equated to a restricted name, and stops with a
failure.  (\textsc{Tr1}) and (\textsc{Tr2}) handle trivial cases.  The algorithm
succeeds with $\Box$, when there are no more constraints and the labels of the
rewrite steps gives a sequence of substitution sequences.

As an example of the application of the above rules, let us consider this
example:
\[
\case{\ci{a \sch c}{
    \case{\ci{c \sch b}{
        \case{\ci{a \sch b}{
            d(x)
        }}
    }}
}}
\]

This agent would give rise to the following constraint.
\[
\constr{d \sch f} \land
\constr{a \sch b} \land
\constr{c \sch b} \land
\constr{a \sch c}
\]
where $f$ is a freshly chosen name.

One possible sequence of unification rule application is the following

\[
\begin{split}
\constr{d \sch f} \land
\constr{a \sch b} \land
\constr{c \sch b} \land
\constr{a \sch c} &
\stackrel{[f := d]}{\rightarrowtail}  \\
\constr{a \sch b} \land
\constr{c \sch b} \land
\constr{a \sch c} &
\stackrel{[b := a]}{\rightarrowtail}  \\
\constr{c \sch a} \land
\constr{a \sch c} &
\stackrel{[a := c]}{\rightarrowtail}
\constr{c \sch c} \rightarrowtail \Box
\end{split}
\]

We just showed that the channel equivalence, $=$, is transitive.  By composing
all the substitutions on the arrows in sequence we get a solution substitution
$[f:=d][b:=a][a:=c] = [f:=d,b:=c,a:=c]$. It is clear that this solution is not
unique, for instance the substitution $[f:=d, b:=a, c:=a]$ also satisfies the
above constraint. In fact, the unification algorithm gives a substitution unique
up to a permutation of names, i.e.~a bijective renaming
(cf.~\cite{Klop92termrewriting}).

In contrast to the above example, below is an agent which gives rise to
a transition constraint with no solutions.
\[
(\nu a)a(x)
\]

The constraint to be solved is $(\nu a)\constr{a \sch b}$ (where $b$
is chosen fresh $b \freshin a$); this satisfies the (\textsc{Fail}) rule.

Before we continue implementing the unification, we define a convenience
sub-structure which provides nominal functions for a list of names, such that
we can compute $a \freshin \ve{x}$ with \sml{L.fresh a xvec}.
*)
  structure L = NominalNameList(
      struct type atom = name val new = new end)
(**

The function \sml{mgu} is an implementation of the above unification rules. We
represent success, $\Box$, by returning \sml{Either.RIGHT sigma} with the
substitution sequence, and failure, $\blacksquare$, by returning
\sml{Either.LEFT phi} with the offending condition. The function \sml{mgu} takes
a constraint as the first argument, and the accumulated substitution sequence as
the second. The function \sml{mgu} computes a new substitution sequence when the
(\textsc{Elim}) rule is applicable.

The lines that correspond to each of the above unification rules are annotated
to the right.

*)
  fun mgu [] sigma = Either.RIGHT sigma                (*@ $\Box$ @*)
    | mgu ((avec, Unit,  T )::cs) sigma =              (*@ (\textsc{Tr2}) @*)
      mgu cs sigma
    | mgu ((avec, Unit, (Eq (a,b)))::cs) sigma =
      if a = b then mgu cs sigma                       (*@ (\textsc{Tr1}) @*)
      else
        if L.fresh a avec andalso L.fresh b avec       (*@ (\textsc{Elim})@*)
            then mgu (Constraint.subst cs [(b,a)])
                     (composeSubst sigma (b,a))
            else Either.LEFT [Eq (a,b)]                (*@ $\blacksquare$ @*)
(**

The last thing we need to provide to complete the implementation of a
constraint solver for transition constraints is the \sml{solve} function.
The \sml{solve} function accepts a constraint and produces either a list of
solutions or a list of failed conditions. In our case, the function \sml{solve}
is just a wrapper for the \sml{mgu} function.  A solution to the constraint is
only the substitution sequence, as Pi-calculus has trivial assertions. And the
\sml{mgu} function gives a Most General Unifier (up to a name permutation, or
bijective renaming substitution \cite{Klop92termrewriting}). That is, it is
sufficient to return only the substitution sequence produced by \sml{mgu} as all
other solutions are entailed by the \sml{mgu} (again, up to name permutation).

*)
  fun solve cs =
    case mgu cs [] of
         Either.RIGHT sigma => Either.RIGHT [(sigma, Unit)]
       | Either.LEFT phi    => Either.LEFT  [phi]
(**[Bisimulation]*)(**


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\section{Pi-calculus bisimulation constraint solver}
\label{sec:pi-calculus-example-bisimulation}





In this section, we continue the  Pi-calculus instance example
implementation~(Section \ref{sec:pi-calculus-example-skip-bisim}). We implement
a bisimulation constraint solver (Appendix \ref{sec:bisim-algorithm}) for the
instance. As in other examples
(Section~\ref{sec:instance-implementation-examples}), we use a literal
programming style for describing the constraint solver and we omit the line
numbering.

The constraints used by the symbolic bisimulation algorithm is more complex than
that of symbolic transition constraints. Even when a Psi-calculus instance does
not provide any additional logic, bisimulation constraints entail a first-order
logic without quantifiers and with equality. Knowing this, to find a solution to
a bisimulation constraint is the same problem as to find a model satisfying a
preposition logic formula (SAT).  We use one of the classical algorithms for SAT
in propositional logic, DPLL \cite{Davis1960, Davis1962}. The DPLL algorithm is
extendible with additional theories \cite{Nieuwenhuis06solvingsat}. The theories
enable the algorithm to be used to solve formulae of superset of propositional
logic. Our implementation of the algorithm is not intended to be efficient, 
the main purpose of it is to provide a sample implementation of a bisimulation
constraint solver.
Furthermore, the freshness constraint (Definition~\ref{def:bisim-constraints} in
Appendix~\ref{sec:bisim}) solution depends on a complete model of the
constraint which it is part of. We introduce an additional step to handle
freshness constraints. This step backtracks if it fails.  This kind of
additional steps might be complicated to use in an off-the-shelf SAT
solver.

While it is feasible to translate a first-order logic without quantifiers and
with an equality (ground logic) into a propositional logic
\cite{ground-logic-sat} and thus solve it with a SAT algorithm, it is not clear
that such translation exists for freshness constraints.


A constraint that is produced by the bisimulation algorithm contains trivially
solvable sub-constraints and a constraint accepted by the DPLL algorithm must
be in CNF form. Trivial constraints can be solved at a separate stage with a
simpler constraint solver. We use a term rewriter~\cite{BN98} to convert
constraints into CNF constraints and to solve trivial constraints.  A term
rewriter is provided by the tool's framework, we demonstrate how to implement
term rewriting rules.

Recall that the structure \sml{PiSymbolicInstance}
(Section~\ref{sec:pi-calculus-example}) contains the \SML{} code presented here.



\subsection{Constraints}

The table below lists the bisimulation algorithm constraint forms (see Appendix
\ref{sec:bisim-algorithm} for the bisimulation algorithm) and the \SML{}
representation.

\[
\begin{array}{ll}
\text{Notation}                      & \text{\SML{} code} \\
\mathbf{true}                        & \text{\sml{True}} \\
\mathbf{false}                       & \text{\sml{False}} \\
(\nu\ve{a})\constr{\unit \vdash a \sch b} & \text{\sml{Atomic (avec, unit, Eq(a,b))}} \\
\constr{a = b}                       & \text{\sml{TermEq (a,b)}} \\
\constr{a \freshin P}                & \text{\sml{FreshP (a,p)}} \\
C \land C'                           & \text{\sml{Conj (c,c')}} \\
C \lor C'                            & \text{\sml{Disj (c,c')}} \\
C \Rightarrow C'                     & \text{\sml{Imp (c,c')}} \\
\end{array}
\]

First we define negation since we need it translation into CNF.
\[
\neg C \defn C \Rightarrow \mathbf{false}
\]

We write $(\nu\ve{a})\constr{a \sch b}$ for $(\nu\ve{a})\constr{\unit \vdash a
\sch b}$, and $\constr{a = b}$ denotes a term equality constraint.


Similarly to the transition constraints, the bisimulation constraint is a nominal
datatype and has a substitution function defined on it, we get
the default implementation of bisimulation constraint by applying the
functor~\sml{BisimConstraint}.

*)
  structure BisimConstraint = BisimConstraint(PiInstanceNom)
(**

The functor BisimConstraint defines the constraints required by the bisimulation
constraint generation algorithm.





\subsection{Term rewriting and all that}

A term rewriter is a syntactic transformation function which maps terms to terms
by applying a set of term rewriting (transformation) rules, usually a set of
identities (one direction) \cite{BN98}. In our case, the terms are
constraints. A term rewriter is provided by the \sml{BisimConstraint}
structure.  For a full account of term rewriting systems see
\cite{Klop92termrewriting, BN98}.

As mentioned in the introduction, we use a term rewriter for simplifying
constraints (solving trivial sub-constraints) produced by the bisimulation
algorithm, we also use a term rewriter for translating a constraint to a
Conjunctive Normal Form (CNF).

The function \sml{rewrite} (from the structure \sml{BisimConstraint}) takes a
list of term rewriting rules and a constraint. A term rewriting rule is a
function which given a constraint and returns either a constraint if the rewrite
rules is applicable or, otherwise, a failure. For instance a term rewriting rule
\[
C \land \mathbf{true} \rightarrow C
\]
can be implemented as a \SML{} function
\begin{center}
\begin{tabular}{c}
{
\begin{lstlisting}[boxpos=c,language=sml,numbers=none,frame=]
val conjRightUnit = fn (Conj (c,True)) => SOME c
                     |  _              => NONE
\end{lstlisting}
}
\end{tabular}
\end{center}

For instance, in order to remove all the right units in a constraint \sml{c}
with the above term rewriting rule, we do \sml{rewrite [conjRightUnit] c}.



Now we are ready to express the term rewriting rules for solving the trivial
constraints, they are as follows.
\begin{mathpar}
\constr{\unit\leq\unit} \rightarrow \mathbf{true} \and
(\nu\ve{a})\constr{\top} \rightarrow \mathbf{true} \and
(\nu\ve{a})\constr{a \sch a} \rightarrow \mathbf{true} \and
\constr{a = a} \rightarrow \mathbf{true} \and
(\nu\ve{a})\constr{a \sch b} \rightarrow \mathbf{false}
    \text{ if } a\freshin b \land (a\in\ve{a} \lor b\in\ve{b})
\end{mathpar}
Compared with rules for solving trivial transition constraints in
Section~\ref{sec:pi-calculus-example}, we add two more rules to solve
additional cases. The static
implication case is always $\mathbf{true}$ as the Pi-calculus instance does not
feature assertions; term equality is the same as channel equivalence without
binders.

Additionally, we can trivially solve freshness constraints if there are no
sub-constraints in a constraint $C$ with the channel equivalence (or the term
equivalence) which contain a name used in a freshness constraint. By
parameterising the term rewriter on a constraint $C$ we get
\[
\constr{a \freshin P} \rightarrow_C \mathbf{true}
    \quad\text{if } a \freshin C
\]

Since in Pi-calculus instance we can regard channel equivalence and term
equality as the same constraint, we convert channel equivalence to term equality
and we name this transformation a normalisation.
\[
(\nu\ve{a})\constr{a \sch b} \rightarrow \constr{a = b}
    \quad\text{if } a,b \freshin \ve{a} \\
\]


After solving the trivial constraints, we get a number of redundant constraints
which we can prune by simplification. For example, the simplification rules
\sml{simplificationRules} provided by the functor \sml{BisimConstraint}
are the following (the symmetric versions are elided).
\begin{mathpar}
\mathbf{false}\land C \rightarrow \mathbf{false}  \and
\mathbf{true}\land C \rightarrow C \and
C \land C \rightarrow C \and
C \land (C \lor C') \rightarrow C \and
\mathbf{false} \lor C \rightarrow C \and
\mathbf{true} \lor C \rightarrow \mathbf{true} \and
C \lor C \rightarrow C \and
\mathbf{false} \Rightarrow C \rightarrow \mathbf{true} \and
C \Rightarrow \mathbf{true} \rightarrow \mathbf{true} \and

\dots\land C \land\dots\land \neg C \land\dots \rightarrow \mathbf{false} \and
\dots\lor C \lor\dots\lor \neg C \lor\dots \rightarrow \mathbf{true} \and

\neg\neg C \rightarrow C \and
\end{mathpar}


Note the above rewriting rules are identities in first-order logic. It is not
hard to show that these hold for the bisimulation constraints.


First, we make all the definition locally visible.
*)
  local open BisimConstraint in
(**

The following code implements the trivial constraint solving and simplification
rules.
*)
  val trivialConditionRules =
    (fn (StImp (psi,psi')) => SOME True
      | _ => NONE) ::
(***)
    (fn (Atomic (avec, unit, T)) => SOME True
      | _ => NONE) ::
(***)
    (fn (Atomic (avec, unit, Eq (a, b))) =>
        if a = b then SOME True else NONE
      | _ => NONE) ::
(***)
    (fn (TermEq (a, b)) =>
        if a = b then SOME True else NONE
      | _ => NONE) ::
(***)
    (fn (Atomic (avec, unit, Eq (a, b))) =>
        if a <> b andalso
          (Lst.member a avec orelse Lst.member b avec)
            then SOME False else NONE
      | _ => NONE) ::
(***)
    (fn (Atomic ([], unit, Eq(a,b))) => SOME (TermEq (a,b))
      | _ => NONE) ::
(***)
    (fn (Atomic ((avec as (n::ns)), unit, Eq (a,b))) =>
        if L.fresh a avec andalso L.fresh b avec
            then SOME (Atomic ([], unit, Eq(a,b)))
            else NONE
      | _ => NONE) ::
(***)
    []
(**
The trivial freshness constraint rule.
*)
  fun freshnessRule c =
    (fn (FreshP (a,p)) =>
        if BisimConstraint.fresh a c then SOME True
        else NONE
     | _ => NONE) :: []
(**


As we already mentioned, we employ the term rewriter for transforming
a constraint into a CNF form. Let us first recall that CNF is a formula of the
form
\[
(\ell_{1,1} \lor \dots \lor \ell_{1,m_1}) \land \dots \land
(\ell_{n,1} \lor \dots \lor \ell_{n,m_n})
\]
i.e. a conjunction of disjunctions of literals. A literal can be of two kinds
a positive and a negative of some atomic formula $A$:
\[
\ell ::= A \;\;|\;\; \neg A
\]

In the Pi-calculus instance case, an atomic formula is one of:
\[
A ::= \constr{a = b} \;\;|\;\; \constr{a \freshin P} \\
\]

In \SML{} code.
*)
  fun isLiteral (FreshP _)              = true
    | isLiteral (Imp (FreshP _, False)) = true
    | isLiteral (TermEq _)              = true
    | isLiteral (Imp (TermEq _, False)) = true
    | isLiteral _                       = false
(**

For obtaining a CNF formula from an arbitrary constraint, the following
procedure is used:
\begin{itemize}
\item Remove implications.
\item Move all the negations inwards.
\item Distribute disjunctions over conjunctions.
\end{itemize}

The first step is this rewrite rule
\[
C \Rightarrow C' \rightarrow \neg C \lor C'
\]

The second step is de Morgan's laws
\begin{mathpar}
\neg(C \land C') \rightarrow \neg C \lor \neg C' \and
\neg(C \lor C') \rightarrow \neg C \land \neg C'
\end{mathpar}

And the last step
\begin{mathpar}
C \lor (C' \land C'') \rightarrow (C \lor C') \land (C \lor C'') \and
\end{mathpar}

The above procedure is implemented by using these term rewriting rules in the
function \sml{cnf} in the \sml{BisimConstraint} structure.









\subsection{DPLL algorithm}


After the simplification, normalisation, and transformation to a CNF form we
use the Davis-Putnam-Logemann-Loveland\cite{Davis1960, Davis1962} algorithm
to find a model, i.e.~a solution to the constraint. The simplest form of DPLL
algorithm is used to find a model (a valuation to variables) to a propositional
logic formula but the bisimulation constraint give more expressiveness than
propositional logic. The DPLL algorithm can be extended to
supersets of propositional logic by treating the atomic formulas of background
theory $T$ as propositional variables, and by defining custom decision
procedures for the theory $T$ in the model. This method generally known as SAT
Modulo Theory (SMT), see~\cite{Nieuwenhuis06solvingsat} for a description and
survey of SMT approaches. We also use~\cite{Nieuwenhuis06solvingsat} as a
guideline and we present here their formulation of the algorithm as a transition
system.

The DPLL algorithm accepts a formula in CNF form. When describing the algorithm
we use the following notation for CNF formula.
\[
\ell_{1,1} \lor \dots \lor \ell_{1,m_1}, \dots,
\ell_{n,1} \lor \dots \lor \ell_{n,m_n}
\]
i.e., we separate the conjuncts with commas.


A central concept in DPLL is a (partial) model. A model is a consistent set of
literals $\ell_1,\dots,\ell_n$. The set can be thought as a conjunction so
consistency means an absence of a contradiction. The decision procedure of the
theory $T$ is parameterised with a relation~$\mathcal{M}\models C$. This
relation, intuitively, means if the constraint $C$ can be solved trivially by
considering literals in the model $\mathcal{M}$ as true. In our presentation, by
replacing literals of a model~$\mathcal{M}$ in the constraint $C$ with
constraints $\mathbf{true}$ and by expecting the outcome of the simplification
and the trivial constraint solving to reduce the constraint $C$ to the
constraint $\mathbf{true}$. If a model is inconsistent, we say it is in a fail
state $\bot$.

The algorithm is formulated with a transition systems where transitions take the
form:
\[
\mathcal{M} \Vdash C \hookrightarrow \mathcal{M'} \Vdash C
\]
the model $\mathcal{M}$ is a partial model, and the transition goes into a
partial model $\mathcal{M'}$ with more literals accounted for. Note the
constraint is not changed although in the implementation we simplify the
constraint according the partial model.



We implement the simplest form of DPLL algorithm, given by the state transition
rules below, taken from \cite{Nieuwenhuis06solvingsat} with modifications
discussed later.
\[
\begin{array}{l}
\mathcal{M} \Vdash C,\textsc{c}\lor\ell
\;\;\hookrightarrow\;\;
\mathcal{M} \ell \Vdash C, \textsc{c}\lor\ell \\
\qquad\text{if } \mathcal{M} \models \neg \textsc{c} \;\land\; l\not\in\mathcal{M}
\hfill\qquad\textsc{(UnitProp)}
\\


\mathcal{M} \Vdash C
\;\;\hookrightarrow\;\;
\mathcal{M} \ell \Vdash C \\
\qquad\text{if }
(\exists \textsc{c} \in C) \ell \in \textsc{c} \;\land\;
(\forall \textsc{c} \in C) \neg\ell \not\in \textsc{c} \;\land\;
\ell \not\in \mathcal{M}
\hfill\qquad\textsc{(PureLit)}
\\


\mathcal{M} \Vdash C
\;\;\hookrightarrow\;\;
\mathcal{M} \ell^d \Vdash C \\
\qquad\text{if }
\ell\not\in\mathcal{M} \land
(\exists \textsc{c} \in C) \ell\in\textsc{c} \lor \neg\ell\in\textsc{c}
\hfill\qquad\textsc{(Decide)}
\\


\mathcal{M} \Vdash C, \textsc{c}
\;\;\hookrightarrow\;\;
\blacksquare \\
\qquad\text{if }
\mathcal{M} = \bot \lor
(\mathcal{M}\models \neg\textsc{c} \land \nexists \ell^d \in \mathcal{M})
\hfill\qquad\textsc{(FailC)}
\\


\mathcal{M} \ell^d \mathcal{N} \Vdash C, \textsc{c}
\;\;\hookrightarrow\;\;
\mathcal{M} \neg\ell \Vdash C, \textsc{c} \\
\qquad\text{if }
(\mathcal{M}\ell^d \mathcal{N} = \bot \lor
\mathcal{M}\ell^d \mathcal{N} \models \neg \textsc{c})
    \;\land\;
\nexists {\ell'}^d \in \mathcal{N}
\hfill\qquad\textsc{(Backtrack)}
\\

\end{array}
\]

Recall the constraint $C$ is in a CNF form.  We mark a literal $\ell$ as
$\ell^d$ to denote a decision point where we might backtrack if a consistent model
is not found. Note the literal is positive. If there is no more rules to
apply then $\mathcal{M}$ is a complete model.

We briefly summarise the DPLL rules:
\textsc{(UnitProp)} applies whenever there is
a clause in a constraint such that by taking out the literal $\ell$ model entails
the rest of the clause as false, therefore it forces the literal $\ell$ to be
added as a positive in a model as it makes the clause true; \textsc{(PureLit)}
applies when there is a clause with the literal $\ell$ which no other clause in
the constraint $C$ has a negative of that literal so this forces literal into a
model as a positive, otherwise the decision rule applies \textsc{(Decide)},
which adds a literal as a positive and marks it as a decision, such that the
\textsc{(Backtrack)} rule can return to that point where the decision was made
and reverse it (negate the literal and unmark it as a decision) if the decision
was wrong. Lastly, fail \textsc{(FailC)} if a model entails negative clause and
there were no decisions made.  If none of the above rules apply then we are left
with a complete model which satisfies the constraint.  We extend the original
DPLL algorithm with the disjuncts in rules \textsc{(FailC)} and
\textsc{(Backtrack)} where it is checked if a model itself is in a consistent
state (cf. \cite{Nieuwenhuis06solvingsat}).

Next we describe the model and its construction from literals.






\subsection{Model}

Here we consider the T part in the SMT problem.  From the previous section
recall the operation in the transition system
\[
\mathcal{M} \ell
\]
we call it \emph{concatenation}. So, the objective of this section is to define
this operation for the Pi-calculus instance bisimulation constraints, and by
doing so establish the background theory.

Let us reiterate the constraints that form the model.
\[
A ::= \constr{a = b} \;\;|\;\; \constr{a \freshin P} \\
\]

The equality is transitive coupled with a fact that literals may be negated, the
naïve approach does not work as it produces an inconsistent model.  For
instance, if we have a model
\[
\mathcal{M} = \constr{a = b},\constr{b = c}
\]
and we have a literal to concatanate with
\[
\ell = \neg\constr{a = c}
\]
by just adding the literal $\ell$ to the model $\mathcal{M}$ gives the following
model $\mathcal{M},\ell$
\[
\mathcal{M},\ell = \constr{a = b},\constr{b = c},\neg\constr{a = c}
\]
but this model is inconsistent because by transitivity the constraint
$\constr{a=c}$ is in the model $\mathcal{M}$.

The solution we use is to compute an equivalence closure (a transitive,
reflexive, symmetric closure) every time a literal is added to a model, we
denote it by
\[
\mathcal{M}^=
\]
Continuing with the example the model is (we omit the reflexive and symmetric
literal)
\[
\mathcal{M}^= = \constr{a = b},\constr{b = c},\constr{a = c}
\]
now it is trivial to detect the inconsistency. In fact, in our implementation
we do not even need to check for such inconsistency as the model would entail
the literal $\neg\constr{a = c}$ in a constraint considered as the constraint
$\mathbf{false}$ and it would be reduced by the simplifier. As we later see, the
computation of equivalence closure will benefit us when extracting a solution
from a model.

Formally, an equivalence closure on a binary relation $R$ can be given as the
least relation $R^=$:
\[
\begin{array}{rcl}
R^= & =    & \{ (b,a) : (a,b) \in R^= \} \\
    & \cup & \{ (a,c) : \exists b . (a,b) \in R^= \land (b,c) \in R^= \} \\
    & \cup & R
\end{array}
\]

The equivalence closure on a model $\mathcal{M}$ is
\[
\mathcal{M}^=  = \{ \constr{a = b} : \constr{a = b} \in \mathcal{M} \}^=
               \;\cup\; \mathcal{M}
\]
i.e.~treating literals of the form $\constr{a = b}$ in $\mathcal{M}$ as binary
tuple and by extracting these tuples, then computing an equivalence closure on
them,  and finally adding them back to the model.


The implementation of computing equivalence closure on a model is also
split into two operations.

The least fixed-point definition of equivalence closure gives straightforward
computation algorithm. The function \sml{eqClosure'} computes $R^=$ given
above when it is provided with a list of tuples.
*)
  fun eqClosure' ids =
  let
    (* a tuple membership testing in a list *)
    fun eqInClosure (a,b) ids =
      Lst.exists (fn id => id = (a,b)) ids

    (* symmetry *)
    val r = map (fn (a,b) => (b,a)) ids
    val r = List.filter (fn (a,b) =>
                           not (eqInClosure (a,b) ids)) r
    val r = ids @ r

    (* transitivity *)
    val t = map (fn (a,b) =>
                map (fn (_,c) => (a,c))
                    (List.filter (fn (b',c) => b = b') r)) r
    val t = List.concat t
    val t = List.filter
              (fn (a,b) => not (eqInClosure (a,b) r)) t
  in
    if null t
        then r
        else eqClosure' (r @ t)
  end
(**

The fixed-point computation for an equivalence closure presented above is not an
efficient way for computing an equivalence closure but it is a straightforward
way and it is easy to implement. For a more efficient solution see
Galler-Fischer \cite{GallerFischer} data structure for computing equivalence
classes.

The function \sml{eqClosure} is the final step for computing and equivalnce
closure of the model $\mathcal{M}$.
*)
  fun eqClosure m =
  let
    val (eq,m') = Either.partition
        (map (fn c =>
                case c of
                     TermEq _ => Either.LEFT c
                   | _ => Either.RIGHT c ) m)
    val eqT = map (fn (TermEq eq) => eq
                    | _ => Err.undefined () ) eq
    val eqCl = eqClosure' eqT
    val eq' = map (fn eq => TermEq eq) eqCl
  in
    eq @ m'
  end
(**
A syntactic equality on literals is not sufficient as the term equality and
negation of the term equality is commutative, what is more, a freshness
constraint may contain alpha equivalent agents. This motivates us to be explicit
in the following definition of constraint equality
\begin{align*}
\constr{a = b} = \constr{a' = b'} & \Leftrightarrow
    a = a' \land b = b' \;\; \lor \;\; a = b' \land b = a' \\
\neg\constr{a = b} = \neg\constr{a' = b'} & \Leftrightarrow
    a = a' \land b = b' \;\; \lor \;\; a = b' \land b = a' \\
\constr{a \freshin P} = \constr{a' \freshin P'} & \Leftrightarrow
    a = a' \land P =_\alpha P' \\
\neg\constr{a \freshin P} = \neg\constr{a' \freshin P'} & \Leftrightarrow
    a = a' \land P =_\alpha P'
\end{align*}

The function \sml{lEq} implements above equivalence. It expects two literals
and returns true if they are equivalent and false if they are not.
*)
  fun lEq l l' =
    case (l, l') of
         (TermEq (a,b), TermEq (a',b')) =>
            (a = a' andalso b = b') orelse
            (a = b' andalso b = a')
       | (Imp(TermEq (a ,b ), False),
          Imp(TermEq (a',b'), False)) =>
            (a = a' andalso b = b') orelse
            (a = b' andalso b = a')
       | (FreshP(a,p), FreshP(b,q)) => a = b andalso
                                       Psi.eqD(p,q)
       | (Imp(FreshP(a,p),False),
          Imp(FreshP(b,q),False)) => a = b andalso
                                     Psi.eqD(p,q)
       | _ => false
(**

Computing of $\ell \in \mathcal{M}$, now becomes straightforward.
*)
  fun inM l m = Lst.exists (fn l' => lEq l l') m
(**
We also require a function which would compute a negation of a literal,
i.e.~$\neg(\neg\ell) = \ell$ and $\neg(\ell) = \neg\ell$.
*)
  fun negL (Imp (c, False)) = c
    | negL c = (Imp (c, False))
(**


Now we have everything needed to define the concatenation
operation~$\mathcal{M}\ell$ on the model $\mathcal{M}$ and the literal $\ell$. A
concatenation may result in a new model with the literal taken into the account
of a model
or the inconsistent state $\bot$. The concatenation operation is the theory
part of SMT, however, there is a need to do theory judgment at the point
when a full model is constructed by the DPLL algorithm, see
\sml{validateAndReturn} and \sml{dpllSAT} functions.

We have four cases of literals to consider. In all cases, we do not need to check
for an inconsistency arising from a model already containing a negated literal to
that being added.  As we mentioned before, we are guaranteed that such negated
literal would not be considered for an addition to a model.

When adding a term equality literal to a model, we check if the model
would be consistent after the addition. A freshness constraint
disallows a name to be used in the domain of a substitution,
and a model serves as a means to extract a substitution sequence,
consequentially an inconsistency may arise if both of the equality sides
are disallowed in a substitution sequence. Note this needs to be
checked for the model with an added literal and an equivalence closure, for
instance if we have 
$\constr{a = b}, \constr{a\freshin P}, \constr{c\freshin P}$ model
and a candidate literal is $\constr{b = c}$ and if we would not require
an equivalence closure then such candidate would be added to a model
but there is no substitution sequence which would satisfy such model, we
may compute these substitution sequences from above model
$[a:=c, b := c]$,
$[b:=a]$, $[b:=c]$,
$[b:=a,c:=b]$ but neither of
them satisfy such model. The second clause requires that there must not
be an induced equivalence and disequality.
A resulting model is an equivalence closure.

\[
\begin{array}{l}
\mathcal{M} \constr{a = b} =
\left\{ \begin{array}{ll}
\bot & \text{if } \exists P,P',c,d .
    \constr{c\freshin P},\constr{d\freshin P'},\constr{c = d} \in
  \mathcal{M'} \\
\bot & \text{if }  \exists c,d . \neg\constr{c = d}, \constr{c = d}
     \in \mathcal{M'} \\
\mathcal{M'} & \text{otherwise}
\end{array}
\right.
\end{array}
\]

where $\mathcal{M'} = (\mathcal{M}, \constr{a = b})^=$.



The disequality case does not pose any complications as the negations
are reduced before applying this operation (more on this later).
\[
\mathcal{M} \neg\constr{a = b} = \mathcal{M}, \neg\constr{a = b}
\]

In case when adding a freshness constraint, the only inconsistency that may arise
is disallowing both of the sides of some equality in a model for a
substitution.
\[
\begin{array}{l}
\mathcal{M} \constr{a \freshin P} =
\left\{\begin{array}{ll}
\bot & \text{if } \exists b,P' .
    \constr{b \freshin P'}, \constr{a = b} \in \mathcal{M} \\
\mathcal{M}, \constr{a \freshin P} & \text{otherwise}
\end{array}\right.
\end{array}
\]


The last case is simply adding the literal into the model.

\[
\mathcal{M} \neg\constr{a \freshin P} =
\mathcal{M}, \neg\constr{a \freshin P}
\]


Note the concatenation operation does not guaranty a model is free from
inconsistencies. The clauses that check for inconsistencies arising from
freshness constraints are there for an early detection, a recheck is needed for
freshness constraints in a model as the last step since they \emph{depend} on
the substitution sequence constructed, i.e., a complete model.



The function \sml{extendM} computes the concatenation operation given a
model \sml{m} and a literal \sml{l}, returns a new model \sml{SOME} on
success, otherwise \sml{NONE} if the model would be inconsistent after
addition of the literal.
*)
  fun extendM m (l as TermEq (a,b)) =
  let
    val meq = eqClosure (l::m)
    val fr  = List.concat
        (map (fn (FreshP (a,_)) => [a] | _ => []) meq)
  in
    if Lst.exists
        (fn (TermEq (c,d)) => Lst.member c fr
                              andalso Lst.member d fr
          | _ => false) meq
     then NONE
     else
       if Lst.exists
            (fn (ell as TermEq (a,b)) => inM (negL ell) meq
              | _ => false) meq
         then NONE
         else SOME meq
  end
    | extendM m (l as Imp(TermEq(a,b), False)) = SOME (l::m)
    | extendM m (l as FreshP (a,_)) =
        if Lst.exists (fn (FreshP (b,_)) =>
            inM (TermEq (a,b)) m  | _ => false) m
        then NONE
        else SOME (l::m)
    | extendM m (l as (Imp (FreshP _, False))) = SOME (l::m)
    | extendM _ _ = Err.error "An undefined case in extendM"
(**




\subsection{The implementation of DPLL}


The implementation we give here is reminiscent of On-Line SAT solver (see
\cite[Section 3.2]{Nieuwenhuis06solvingsat} for a survey of SMT techniques),
i.e., a theory judgement is made every time a literal is added to a model, and
instead of restarting a SAT procedure whenever model is inconsistent, the
algorithm backtracks to the last known good point where model was still
consistent.


In our implementation of the DPLL algorithm, a state transition simplifies a CNF
constraint
\[
\mathcal{M},C \Vdash \mathcal{M'},simp_\mathcal{M'}(C)
\]
such that literals entailed by the model with an added literal are simplfied.
This gives us a strict termination condition
\[
\mathcal{M},C \Vdash \mathcal{M'},\mathbf{true}
\]
i.e., $\mathcal{M'}$ is a complete model to the initial constraint.

For implementing the $simp_\mathcal{M}$ function we yet again use the term
rewriter.  We introduce additional to the simplification term rewriting rules
parameterised over the model $\mathcal{M}$.
\begin{mathpar}
\ell \rightarrow_\mathcal{M} \mathbf{true} \text{ if } \ell \in \mathcal{M}\and
\ell \rightarrow_\mathcal{M} \mathbf{false} \text{ if } \neg\ell \in \mathcal{M}
\end{mathpar}

The function \sml{modelRules} implements the above term rewriting rules.
The function given a model \sml{m} produces a singleton list with term
rewriting rule.
*)
  fun modelRules m =
    [fn l =>
        if isLiteral l then
          if inM l m then SOME True
          else if inM (negL l) m then SOME False
          else NONE
        else NONE]
(**
The above entailment rewriting rules are applied together with the
simplification rules.  The function \sml{simpM} runs a term rewriter on \sml{c}
constraint using the simplification rules an the rules we defined above.
*)
  fun simpM m c =
    rewrite (simplificationRules @ modelRules m) c
(**
In order to simplify the implementation of the DPLL algorithm, we treat
constraints in CNF form as a list of lists, that is, a list of list of
disjuncts. The function \sml{disjToList} accepts a constraint which is
disjunction of atomic constraints and returns a list of atomic constraints.
*)
  fun disjToList (Disj (c,c')) = disjToList c @ disjToList c'
    | disjToList c = [c]
(**
Similarly, the function \sml{cnfToList} accepts a constraint in CNF form
and produces a list of lists of atomic constraints.
*)
  fun cnfToList (Conj (c,c')) = cnfToList c @ cnfToList c'
    | cnfToList c = [disjToList c]
(**
The function \sml{simpClause} uses the above simplification on a clause
\sml{c}. The implementation is very simple: we reconstruct a
disjunction, then we apply the term rewriter and finally we split the
disjunction into a list. So this function implements the relation
$\mathcal{M}\models c\lor
c'\lor\dots$ for a
disjunction.
*)
  fun simpClause m c =
    disjToList (simpM m (disjunct c))
(**
The function \sml{simpCNF} is similar to the above \sml{simpClause} but it
accepts a CNF. This is the relation $\mathcal{M}\models C$.
*)
  fun simpCNF m c =
    cnfToList (simpM m (conjunct (map disjunct c)))
(**

The problem that we are solving is finding a solution for a bisimulation
constraint $C$, while the model we get from the DPLL algorithm is conjunction of
constraints. We face with yet another layer of constraint solving but we
already solved a similar problem for the transition constraints. The function
\sml{modelSubst} computes a \emph{mgu} given a model \sml{m}.

*)
  fun modelSubst m = modelSubst' m []
  and modelSubst' [] sigma = sigma
    | modelSubst' (TermEq(a,b)::eqs) sigma =
        modelSubst'
            (map (fn e => BisimConstraint.subst e [(a,b)]) eqs)
            (composeSubst sigma (a,b))
    | modelSubst' (_::eqs) sigma = modelSubst' eqs sigma
(**

We may not get a correct solution by extracting it from any model. We first need
to prepare a model for extraction. This is due to the freshness constraints
since it constrains the domain of the substitution function. We are helped with
the fact that the model is an equivalence closure, so we only need to orient the
equalities, more specifically delete the non conforming equalities.  The
function \sml{orientM} given a model \sml{m} returns a model consisting only
with literals of kind of term equality.
*)
  fun orientM m =
  let
    val fr =
      List.concat (map (fn (FreshP (a,_)) => [a] | _ => []) m)
    val eq =
      List.filter (fn (TermEq (a,_)) => not (Lst.member a fr)
                    | _ => false) m
  in
    eq
  end
(**


By inspecting the DPLL rules, we notice that the model entailment relation
comes only in the form $\mathcal{M} \models \neg\textsc{c}$, where
$\textsc{c}$ is a clause. Therefore we can compute such relation
just by simplifying the clause w.r.t. a model $\mathcal{M}$ and expecting to
find a constant $\mathbf{false}$. This is exactly what the function
\sml{modelsNegC} does, it expects a model \sml{m} and a clause \sml{c}.
*)
  fun modelsNegC m c =
    case simpClause m c of
         [False] => true
       | _       => false
(**

We are now at a position where we have definitions required to implement DPLL
algorithm. We will implement the rules \textsc{(UnitProp)} and
\textsc{(PureLit)} as separate functions. They are called by the main function
\sml{dpllSAT}. The failure is represented by \sml{NONE}. The decision rule
\textsc{(Decide)} is implemented as two recursive calls returning the first one
that succeeded that we get a backtracking rule for free by using \SML{}
backtracking mechanics.

The function \sml{pureLit} implements the rule \textsc{(PureLit)}. It
takes a model \sml{m} and a CNF as a list, it traverses the list a clause at a
time by checking each literal in a clause for a negation of a literal in the
rest of the CNF. There is no need to check the whole
CNF for the negation as the previous queries would have identified a literal
at the current position. The function \sml{pureLit} returns \sml{SOME} literal
if it finds a literal which has no negation in any of the clauses, otherwise
returns \sml{NONE}. 
*)
  fun pureLit m [] = NONE
    | pureLit m (c::cnf) =
    case
      List.find
        (fn l => not (inM l m) andalso
            Lst.all (fn c => not (inC (negL l) c)) cnf) c
      of NONE => pureLit m cnf
       | SOME l => SOME l
(** This is just an auxiliary function for the above which checks if
a literal \sml{l} is in a clause \sml{c}. *)
  and inC l c = Lst.exists (fn l' => lEq l l') c
(**

The other rule \textsc{(UnitProp)} is implemented by the function
\sml{unitProp}. It takes the same arguments as the \sml{pureLit} function.  The
function tries to find a clause in a CNF formula in which taking out a literal
would simplify that clause to $\mathbf{false}$ by examining each clause in
order.  The function returns \sml{SOME} literal if such clause exist and
otherwise \sml{NONE}.
*)
  fun unitProp m [] = NONE
    | unitProp m (cl::cnf) =
    case
      List.find
        (fn (l,c) => (not (inM l m)) andalso modelsNegC m c)
        (splitL cl)
      of NONE => unitProp m cnf
       | SOME (l,_) => SOME l
(**
The function \sml{splitL} is an auxiliary function for the above. This function
given a list, \sml{splitL} returns a tuple list where every tuple contains an
element from the original list and the original list without that element.
*)
  and splitL' [] pls = []
    | splitL' (l::ls) pls =
        (l, pls @ ls) :: splitL' ls (pls @ [l])
  and splitL ls = splitL' ls []
(**

Now we look at a series of mutually recursive functions which complete the
DPLL algorithm.

The model may become inconsistent and therefore we should be
able to backtrack, i.e., the function \sml{extendAndDpll} first tries to extend
the model \sml{m} with the literal \sml{l} and if it fails returns a failure,
otherwise calls the main function \sml{dpllSAT} with the extended model.

*)
  fun extendAndDpll m l cnf =
    case extendM m l of
         NONE => NONE
       | SOME m => dpllSAT m cnf
(**

The function \sml{splitDpll} is an implementation of both
\textsc{(Backtrack)} and \textsc{(Decide)} rules. So given a
model \sml{m}, a literal \sml{l}, and a CNF \sml{cnf} first try
to solve the \sml{cnf} with positive literal, if that fails it backtracks
and then tries to solve the \sml{cnf} by extending the model with a negative
literal.

*)
  and splitDpll m l cnf =
    case extendAndDpll m l cnf of
         SOME m => SOME m
       | NONE   => extendAndDpll m (negL l) cnf
(**

The main function of an implementation of the DPLL algorithm. It accepts
a model \sml{m} and a constraint \sml{cnf} in a CNF form.
The first thing it does at each recursive call is simplify the given CNF
and checks if it completed constructing a model and then validates it,
if not, then it chains the above rules, first by trying unit propagation,
then by trying  pure literal, and lastly by doing a decision. The decision
takes the first literal of the first clause, other rules use the found
literal.

*)
  and dpllSAT m [] = validateAndReturn m
    | dpllSAT m (cnf as (c::cs)) =
  let
    val cnf' = simpCNF m cnf
  in
    case cnf' of
         [[True]] => validateAndReturn m
       | _ => (
    case unitProp m cnf' of
         SOME l => extendAndDpll m l cnf'
       | NONE =>
         (case pureLit m cnf' of
               SOME l => extendAndDpll m l cnf'
             | NONE =>
               let
                 val l = hd c
               in
                 splitDpll m l cnf'
               end) )
  end
(**

\subsection{Additional consistency check}

Even though we are checking for inconsistencies when we are constructing a
model, we may not find all of them until a model is fully constructed.  So, as a
last step, we check if freshness constraints and freshness constraint negations
hold with a complete model. Recall, freshness constraint's $\constr{a \freshin
P}$ solution space is defined by $a \freshin P\sigma \land a \freshin
dom(\sigma)$, and for the negation we have $a \in n(P\sigma) \lor a \in
dom(\sigma)$. For the former we only need to check the first conjunct
$a\freshin P\sigma$ as the second is already true by the way we construct a
model and extract a substitution sequence, and for the latter we check both
disjuncts.

The function \sml{validateAndReturn} takes a model \sml{m} and returns a
substitution sequence, it does this by first constructing a substitution
sequence from a model and checking if all the freshness constraints and their
negation hold, and if that is the case it returns the substitution sequence,
otherwise it fails with \sml{NONE}.

*)
  and validateAndReturn m =
  let
    val sigma = modelSubst (orientM m)
  in
    if
      Lst.all (
          fn (FreshP (a,p)) => Psi.fresh a (Psi.subst p sigma)
           | (Imp (FreshP (a,p), False)) =>
               not (Psi.fresh a (Psi.subst p sigma)) orelse
               Lst.member a (dom sigma)
           | _ => true
      ) m
    then SOME sigma
    else NONE
  end
(**

The final step is to `plug in' the DPLL algorithm into the framework.


\subsection{Putting it together}

The function \sml{solveBisim} is an implementation of the bisimulation
constraint solver. It is similar to the \sml{solve} function, it takes
a constraint \sml{c} and produces a list of substitution and assertion
or a counter example.

*)
  fun solveBisim' _ c =
  let
    val c    = rewrite ( trivialConditionRules
                       @ simplificationRules) c
    val c    = rewrite (freshnessRule c) c
    val c    = cnf c
    val cnf  = cnfToList c
    val sol  = dpllSAT [] cnf
    val sols = case sol of SOME sigma => [sigma]
                  | NONE => []
    val sols = map (fn sigma => (sigma, unit)) sols
  in
    case sols of
         [] => Either.LEFT []
       | _  => Either.RIGHT sols
  end

  val solveBisim = SOME solveBisim'
(**
This ends the \sml{local open BisimConstraint}.


*)
  end
(**
%At this point continue into section \ref{sec:pi-calculus-example-skip-bisim}
%on page \pageref{sec:pi-calculus-example-skip-bisim}.

This ends the implementation of the constraint solver for the constraints
generated by the bisimulation algorithm. The solution to such constraints
require more advanced techniques but SMT techniques are well established field
\cite{Nieuwenhuis06solvingsat}. We did not show how to interface with an
external SMT solver, since we intended to show the principles underlying such
solutions. We think that by exposing an implementation we make a clearer
connection with SMT theory and how one would go about designing models and
interfacing with an external SMT solver.  The real challenge is to define a
model and the decision procedure for that model.


*)
(**[default]*)(** \phantomsection\label{sec:pi-calculus-example-skip-bisim}%

\[
\vdots
\]
This Pi-calculus instance implementation also hosts a constraint solver for
the constraints generated by the bisimulation algorithm
(Appendix~\ref{sec:pi-calculus-example-bisimulation}). The constraints
are more complicated to
solve\footnote{
The bisimulation constraints expresses at least a first order logic
with equality and freshness constraints and without quantifiers.}
and require a more complicated algorithm for finding solutions. However,
the approach is in the same vein as presented here: a bisimulation constraint
solver is a function that takes a constraint and produces either a solution or a
counter example.
Such a constraint solver is not required for the simulation of agents, therefore
we omit it here and direct an
interested reader  to Appendix~\ref{sec:pi-calculus-example-bisimulation} for a
full implementation.

\[
\vdots
\]
*)
end;
(**



\subsubsection*{Implementation of printers and parsers}

The last piece in the construction of a working simulator with command
interpreter is ability to pretty print and parse nominal datatypes.

At this stage we can restrict the \sml{PiCalculus} structure to the
\sml{C_PSI} signature.
*)
structure PiCalculus : C_PSI =
struct
(** As before we input the previously defined structure. *)
  open PiSymbolicInstance
(**


First we need to settle on the \texttt{ASCII} syntax of the
members of the nominal datatypes. For names we choose an alphanumeric
representation, conditions for equality will be formed with \texttt{=},
the top value is written \texttt{T} and the unit assertion is \texttt{1}.

In summary

\begin{center}
\begin{tabular}{ll}
Notation & \texttt{ASCII} \\ \hline
$a$      & \texttt{a} \\
$a \sch b$  & \texttt{a = b} \\
$\top$   & \texttt{T} \\
$\unit$  & \texttt{1}
\end{tabular}
\end{center}


First we turn to printing. Every nominal datatype and names have corresponding
print functions which take a member from nominal datatype and return
a string representation of it.

Names are represented by strings so printing functions are almost
trivial, as the \sml{printC} inserts a \texttt{=} between the
channel equality names.
*)
  fun printN a = a
  fun printT a = a
  fun printC (Eq (a, b)) = a ^ " = " ^ b
    | printC  T = "T"
  fun printA psi = "1"
(**



Parsing is more intricate. We parse nominal datatypes with the combinator
library provided with the tool, although it would not be very difficult to write
a custom parser for the terms of the Pi-calculus instance.

First we need to construct a parser structure which provides the combinators
on string streams.
*)
  structure Parser = Parser(StringStream)
(**
The functor \sml{PsiParserBase} provides the Psi-calculus language lexical parser
combinators: the notion of whitespace, identifier, etc.
*)
  structure Lex = PsiParserBase(Parser)
(**
None of the structures defined above are opened here in order to make the origin
of functions clear.

Parsing combinators deserve some treatment here. A parsing combinator is a
value or a function with a result of the type \sml{'a parser}. The type \sml{'a}
denotes a parse result. The basic combinators are provided by the \sml{Parser}
structure, we use the \sml{return} combinator, which
does not consume any input and always succeeds by returning the value passed to
it as a parse result. A parser combinator may fail resulting in
a parse error and/or backtracking if it is a part of another parser combinator.
This means that parser combinators implement top down recursive
descent parser\footnote{The problem of not handling left recursive grammars is
inherited.}.
In contrast, the \sml{zero} value is a combinator which does not consume any
input and always fails.

We also use lexical parser combinators provided by the structure
\sml{Lex}. Lexical combinators are in an accord with the lexical rules of
Psi-calculi tool (Section~\ref{sec:syntax}).
The combinator \sml{identifier} parses a series of alphanumeric
characters but removes any whitespace (including comments), and it
first returns the concatenated characters as a string. The other combinator of
interest is the function \sml{stok} (mnemonic for `string token') which also
first removes any whitespace and then matches the remaining input with its
string argument; if there is no match it fails.

More complex parsers are built from basic combinators by using sequencing
functions \sml{p >>= q} with type \sml{'a parser * ('a -> 'b parser) -> 'b
parser}, \sml{>>} with type \sml{'a parser * 'b parser -> 'b parser}.  \sml{p
>>= q} sequences two parsers, by first applying the parser \sml{p}, and then
  giving
 parse result of \sml{p} to the function \sml{q} which returns a new parser,
 which in turn can
be used for further sequencing or application.  \sml{p >> q} is the same as
\sml{>>=}, but ignores the result of \sml{p}, and applies \sml{q} directly.
Another crucial building block of parsers is a choice\footnote{It is worh noting
that \sml{>>=} is associative, the combinator \sml{zero} is a left and right
unit for \sml{choice} combinator.  In fact, the type \sml{'a parser} together
with the discussed functions is a monad, cf. \cite{Hutton1998}.
}
between
combinators, which comes in two flavours: deterministic and non-deterministic.
The one we use is the deterministic choice combinator.  The \sml{choice}
parser combinator composes two parser combinators by trying to apply the first
parser combinator to a stream; if the combinator succeeds, \sml{choice} returns
that parser's result and otherwise it tries the second parser combinator.

These parser combinators are modelled after \cite{Hutton1998}, which contains
a reference and examples.

% val parse : 'result parser -> Stream.stream ->
%             ((string fail * Stream.stream) list,
%              ('result * Stream.stream) list) Either.either


Let us first define some aliases.
*)
  fun p >>= q = Parser.>>= (p,q)
  fun p >>  q = Parser.>>  (p,q)
(**

We are now at the point where we can define the syntax of the datatypes.
We will first define parsers for the names, conditions and assertion. And
afterwards we provide the requisites for the signature.
As mentioned before, the syntax of a name will coincide with the identifier
syntax of Psi Workbench. The value \sml{Lex.identifier} is a parser
combinator which define Psi Workbench's identifier syntax.
The value \sml{Lex.identifier} is of the type \sml{string parser}.
*)
  val name = Lex.identifier
(**
Now we define the syntax for conditions, which can be expressed in the
following grammar production rules.

\begin{grammar}
<cond-eq> ::= <name> `=' <name>

<cond-t>  ::= `T'

<cond>    ::= <cond-eq> | <cond-t>
\end{grammar}

The \sml{condEq} parser combinator defines the syntax of the \syntax{<cond-eq>}.
The parser combinator \sml{condEq} parses a name binds it to \sml{a}, then
expects some whitespace and matches \sml{"="}, and then again a name by
binding it to \sml{b} and if none of the parsers failed builds a channel
equality datatype.  Hence, the combinator's \sml{condEq} type is
\sml{condition parser}.
*)
  val condEq =  name >>=
    (fn a =>    Lex.stok "=" >>
                name >>=
    (fn b =>    Parser.return (Eq (a,b))
    ))
(**
The sequencing functions form a production rule, and \sml{>>=} provides
a way to refer to the results (in similar fashion as in attribute grammars).
The \sml{Parser.return} function lifts an ordinary \SML{} value into a parser
combinator;
this kind of parser combinator does not consume any input and always succeeds by
returning the value provided. The combinator \sml{Lex.stok} takes a string as an
argument and treats it as a token by matching it to the input before discarding
any whitespace including comments; if the input matches then it succeeds,
otherwise it fails.

The parser to for the \syntax{<cond-t>} is now straightforward.
*)
  val condT = Lex.stok "T" >> Parser.return T
(**
By using deterministic choice to combine the \sml{condT} and
\sml{condEq} we complete the \syntax{<cond>} implementation.
*)
  val cond = Parser.choice (condT, condEq)
(**
Assertion is similar to the \sml{condT}.
*)
  val assr = Lex.stok "1" >> Parser.return Unit
(**
Parsing functions of nominal datatypes are required to take a string and return
either a corresponding nominal datatype or an error string. But
\sml{Parser.parse} takes a parser combinator and a stream, so to bridge
this
we define an auxiliary function. If a parser succeeds it returns a
list of results, and since we only used deterministic choice to
construct parsers there will be one result returned. The second case clause is
just for inhibiting a compiler warning of non exhaustive pattern matching.
*)
  fun parseResult p s =
    case Parser.parse p (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"
(**
We can now fill in all the required parsing functions.
*)
  fun parseN s = parseResult name s
  fun parseT s = parseN s
  fun parseC s = parseResult cond s
  fun parseA s = parseResult assr s
(**

An important design decision when implementing printers and parsers is to make
them
circular, i.e., \sml{parse a = parse (print (parse a))} and
\sml{print a = print (parse (print a))}.
This is not strictly
enforced, but it is a good convention, as the output of the command
interpreter then can be reused as an input. Let's take conditions as an example,
say we have a string \sml{"a=b"} which would be parsed into
\sml{Eq("a","b")} by \sml{parseC}. The function \sml{printC} would
produce a string \sml{"a = b"} (note the spaces). The parser
\sml{parseC} would again, given the string \sml{"a = b"}, return
\sml{Eq("a","b")}, which is the same as previously. The parser function
\sml{parseC} is implemented in terms of \sml{stok} and \sml{identifier}
which contract any whitespace and only parses the `essence'.

*)
end;
(**



The final matter is to construct a structure with the \sml{Command} functor.
The structure provides a \sml{start : unit -> unit} function to start the
command interpreter.
*)
structure Pi = Command(PiCalculus);
(**

In order to load this file, the file \texttt{workbench.ML} must be loaded first
which provides all the definitions required above (see
Section~\ref{sec:loading-the-command-interpreter}).

This ends the Pi-calculus instance implementation using Psi-calculus workbench
framework. Most of the mathematical machinery involved in defining a
Psi-calculus instance is quite straightforward to carry over to \SML{} code.
This is not very surprising as we use term algebras, and \SML{}'s algebraic
datatypes are designed to easily represent term algebras. The same is true for
most of the associated operations. The most involved part is the design and the
implementation of a constraint solver for both transition and bisimulation
constraints.




*)
