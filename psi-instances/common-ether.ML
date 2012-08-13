(**\label{sec:common-ether-example}
\lstset{style=sml-literal}

In this section, we explore non-trivial assertions.  The Psi-calculus instance
that we implement is called common ether~\cite[Section 2.6]{lics++}.  Although
the assertions that we define are quite simple they induce a surprisingly
big state space for even the transition constraint solving.  We implement a
constraint solver for transition constraints and describe the details as in
other examples.

We take the same approach when presenting as in the FHSS instance example
(Section \ref{sec:fhss-example}). We describe only the differences with the
Pi-calculus instance example (Section \ref{sec:pi-calculus-example}). Not the
whole code is listed (although it is listed in the same order as it appears in a
file), and we skip the \SML{} structure definitions.


\vspace{1em}



As usual, we begin with an example of an agent of this instance.  In the
following example, we introduce step-by-step the features of this instance.  Let
us take the following agent and let us assume $a\freshin b$:
\[
\inn{a}{(x)}.P \;\pll\; \out{b}{y}.Q
\]
because of the above assumption, communication would not be possible in the
Pi-calculus instance. But using assertions, we can enable
communication.  We
model a single global communication channel, without requiring a global
knowledge of available receiving or transmitting channel names. In the
environment we record the available names for accessing the global communication
channel.
\[
(\pass{\{a\}}\pll\inn{a}{(x)}.P) \;\;\pll\;\; (\out{b}{y}.Q \pll \pass{\{b\}})
\]
may silently transition into
\[
(\pass{\{a\}}\pll P)[x:=y] \;\;\pll\;\; (Q \pll \pass{\{b\}})
\]

How can we make these seemingly independent environments coalesce? This is a
feature of the operational semantics: recall that the rules \textsc{Com} and
\textsc{Par} compose juxtaposed assertions of the frame of an agent with the
current assertion (Figure~\ref{fig:symbolic-operational-semantics}). By taking
assertion composition as set union we derive the following
\begin{mathpar}
\inferrule*[Left=Com]{
\inferrule*[Left=Par]{
    \{a,b\}\frames\transs{\inn{a}{(x)}.P}{\cdots}{\cdots}{\dots}
}{
    \{b\}\frames\transs{\pass{\{a\}}\pll\inn{a}{(x)}.P}{\cdots}{\cdots}{\dots}
}
\and
\inferrule*[left=Par]{
    \{a,b\}\frames\transs{\out{b}{y}.Q}{\cdots}{\cdots}{\dots}
}{
    \{a\}\frames\transs{\out{b}{y}.Q \pll \pass{\{b\}}}{\cdots}{\cdots}{\dots}
}
}{
\unit\frames\transs{(\pass{\{a\}}\pll\inn{a}{(x)}.P) \;\;\pll\;\; (\out{b}{y}.Q
\pll \pass{\{b\}})}{\tau}{C}{\dots}
}
\end{mathpar}
Note that at the top of the derivation tree the whole environment is available
and there it is trivial to make a decision.

One peculiarity arises, that channel equivalence is not reflexive.  But this is
allowed by Psi-calculus since channel equivalence must be transitive and
symmetric but not necessarily reflexive
(Definition~\ref{def:entailmentrelation} in Section~\ref{sec:psi-calculus}).
Consider the following agent with no environment.
\[
\inn{a}{(x)} \pll \out{a}{y}
\]
the above agent does not have a $\tau$ transition, while the following has
\[
\inn{a}{(x)} \pll \out{a}{y} \pll \pass{\{a\}}
\]
so by adding the environment $\pass{\{a\}}$ the above agent $\tau$ transitions
into
\[
\nil \pll \nil \pll \pass{\{a\}}
\]


A more interesting example agent
\[
((\nu a) \pass{\{a\}} \pll \inn{a}{(x)}.P) \;\;\pll\;\;
((\nu b) \pass{\{b\}} \pll \out{b}{y}.Q)
\]
silently transitions into
\[
((\nu a) \pass{\{a\}} \pll P)[x:=y] \;\;\pll\;\;
((\nu b) \pass{\{b\}} \pll Q)
\]




%\[
%(\nu a\,b)\constr{ \{ a,b \} \vdash a = b}
%\]
%
%talk about how the rules were derived, by giving example for ce5-ce7 rules
%\[
%(\nu\varepsilon)\constr{\emptyset \vdash a = b}
%\]
%where $a\freshin b$


*)(**[skip]*)
structure CommonEtherNom (* : PSI_INSTANCE_NOM *) =
struct
(**[default]*)(**

\vspace{1em}

Let us formalise the above discussion into the Psi-calculus instance definition.

\[
\begin{array}{rcl}
\mathbf{T} & \defn & \N \\
\mathbf{C} & \defn & \{a = b : a,b \in \mathbf{T} \} \\
\mathbf{A} & \defn & \mathcal{P}_\mathrm{fin} (\N) \\
\sch    & \defn & = \\
\ftimes & \defn & \cup \\
\unit   & \defn & \emptyset \\
\vdash  & \defn & \{ \langle \Psi, a \sch b \rangle : a,b \in \Psi
                    \;\land\; \Psi \in \mathbf{A} \}
\end{array}
\]

While the agent's observed behaviour is quite complex, the instance definition is
compact and succinct. To represent the communication channel, a set of names is
sufficient. That is the nominal datatype for assertions is all possible subsets of
names. Composition of environments is set union.


*)(**[skip]*)
  type name          = string
  type term          = name
  datatype condition = Eq of name * name
(**[default]*)(**



Probably the simplest way to represent a set in \SML{} is with the list data
structure. The assertion is a set of names so in \SML{} we choose to represent
it as a name list.  We allow duplicates in a list, this does not introduce
problems but we need to be careful and have this in mind.

*)
  type assertion = name list
(**[skip]*)

  fun chaneq  (a,b)            = Eq (a,b)
  fun compose (psi1,psi2)      = psi1 @ psi2
(**[default]*)(**


Implementing set operations is straightforward, and the
unit constant and entail operations are almost a direct translation
of the above definition. We use the auxiliary function \sml{Lst.member} to test
membership in a list.
*)
  val unit = []
  fun entails (psi,Eq (a, b))  =
    Lst.member a psi andalso Lst.member b psi
(**[skip]*)

  fun swap_name (a,b) n = StringName.swap_name (a,b) n
  fun new xvec = StringName.generateDistinct xvec

  fun supportT n           = [n]
  fun supportC (Eq (a, b)) = [a, b]
(**[default]*)(**

The support of an assertion is exactly the assertion as it is only a list of
names.
*)
  fun supportA psi = psi
(**[skip]*)

  fun swapT pi n           = swap_name pi n
  fun swapC pi (Eq (a, b)) = Eq (swapT pi a, swapT pi b)
(**[default]*)(**


The functor \sml{NominalNameList} derives a nominal datatype structure
of an atom list. An \sml{atom} list is the data of the nominal datatype and
the structure \sml{L} contains all the nominal operations defined on it.
An assertion is such a nominal datatype.
*)
  structure L = NominalNameList(struct
    type atom = name
    val  new = StringName.generateDistinct end)
(**


The above structure \sml{L} provides the needed implementation of the
swapping function for an assertion.
*)
  fun swapA pi psi = L.swap pi psi
(**[skip]*)
  fun substT sigma n =
    case List.find (fn (x,_) => x = n) sigma of
           NONE       => n
         | SOME (_,t) => t
  fun substC sigma (Eq (a, b)) = Eq (substT sigma a, substT sigma b)
(**[default]*)(**


The function \sml{substA} implements a substitution function by distributing a
function over a list which for every element tries to find a substitution
mapping and replaces the name if found and leaves it unchanged if not. Compare
this with
the function \sml{substT} in the Pi-calculus instance example:
the anonymous function is the same as the function
\sml{substT}.
In fact, the function \sml{substA} is a unique extension of \sml{substT} to an
endomorphism (see \cite{BN98} or Appendix
\ref{sec:some-notions-from-universal-algebra}).

*)
  fun substA sigma psi =
    map (fn n =>
        case List.find (fn (a,b) => a = n) sigma of
             SOME (_,x) => x
           | NONE => n) psi
(**[skip]*)
  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
(**[default]*)(**


Because we use lists to represent sets and we allow duplicates,
we cannot use built-in \SML{} equality to decide assertion equivalence.
The order and the frequency of elements in a list has no significance.
We check if every element in an assertion appears at least once in the
other assertion, and vice versa. If it is the case then both assertions
are deemed to be equivalent.

*)
  fun eqA _ (psi,psi') =
    Lst.all (fn a => Lst.member a psi') psi andalso
    Lst.all (fn a => Lst.member a psi ) psi'
(**[skip]*)
end;




structure CommonEtherSymbolicInstance (* : SYMBOLIC_PSI_FLAT *) =
struct
  open CommonEtherNom

  fun var x = x

  structure Constraint = Constraint(CommonEtherNom)

  fun x |> f = f x

  structure L = NominalNameList(
      struct type atom = name val new = new end)

  fun dom sigma = map (fn (n,t) => n) sigma
  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end
(**[default]*)(**



%\subsubsection*{Instance definition}

Now we turn to the description and implementation of a transition constraint
solver. We will express the constraint solver as a transition system. This
transition systems is non-deterministic and forms a tree of solutions. The
function implementing the transition system follows the branches of
a solution tree and returns the leafs as a solution to the constraint.


\begin{figure}[t!]
\[
\begin{array}{l}
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma[a' := b'], \Psi'), C \rangle \\
\qquad \text{if } a\freshin\ve{a} \land a'\freshin\Psi'' \land
                  b\freshin\ve{a} \land b' \in \Psi''
\hfill \text{\textsc{(Ce1)}}
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma, \Psi' \ftimes \{a'\}), C \rangle \\
\qquad \text{if } a\freshin\ve{a} \land a'\freshin\Psi'' \land
                                        b' \in \Psi''
\hfill \text{\textsc{(Ce2)}}
\\
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma[b':=a'], \Psi'), C \rangle \\
\qquad \text{if } a\freshin\ve{a} \land a'\in\Psi'' \land
                  b\freshin \ve{a} \land b' \freshin \Psi''
\hfill \text{\textsc{(Ce3)}}
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma, \Psi' \ftimes \{b'\}), C \rangle \\
\qquad \text{if }                       a'\in\Psi'' \land
                  b\freshin \ve{a} \land b' \freshin \Psi''
\hfill \text{\textsc{(Ce4)}}
\\
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma, \Psi' \ftimes \{a',b'\}), C \rangle \\
\qquad \text{if } a\freshin \ve{a} \land a'\freshin\Psi'' \land
                  b\freshin \ve{a} \land b' \freshin \Psi''
\hfill \text{\textsc{(Ce5)}}
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma[a':=b'], \Psi' \ftimes \{b'\}), C \rangle \\
\qquad \text{if } a\freshin \ve{a} \land a'\freshin\Psi'' \land
                  b\freshin \ve{a} \land b' \freshin \Psi''
\hfill \text{\textsc{(Ce6)}}
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma[b':=a'], \Psi' \ftimes \{a'\}), C \rangle \\
\qquad \text{if } a\freshin \ve{a} \land a'\freshin\Psi'' \land
                  b\freshin \ve{a} \land b' \freshin \Psi''
\hfill \text{\textsc{(Ce7)}}
%
\\
\\
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\langle (\sigma, \Psi') , C \rangle \\
\qquad\text{ if } \Psi'' \vdash a' = b'
\hfill \text{\textsc{(Ce8)}}
\\
\\
%
%
\langle (\sigma, \Psi'), (\nu\ve{a})\constr{\Psi\vdash a \sch b} \land C \rangle
\rightarrowtail
\blacksquare \\
\qquad\text{ if } \Psi'' \nvdash a' = b' \land (a \in \ve{a} \land b \in
  \ve{b})
\hfill \text{\textsc{(Ce9)}}
\\
\end{array}
\]
\caption%
{Common ether constraint refinement transition rules. The last
rule is not strictly necessary, but it is included for completeness.
We also define for each rule
$\Psi'' = \Psi\sigma\ftimes\Psi'$ and $a' = a\sigma$ and $b' = b\sigma$.
Note $a',b',\Psi''$ may be variants of an alpha conversion in order to
respect $\ve{a}\freshin \sigma,\Psi'$.
}
\label{common-ether:rules}
\end{figure}


In Figure~\ref{common-ether:rules} the transition system $\rightarrowtail$ for
solving a transition constraint is given. The state (configuration) of the
system is of the form
\[
\langle (\sigma, \Psi'), C \rangle
\]
where the tuple $(\sigma, \Psi')$ represents a partial solution to some
constraint and the constraint $C$ is a constraint which still needs to be
satisfied. A transition of $\rightarrowtail$ is a refinement of a
partial solution to extend the partial solution to include the next
conjunct in the configuration
\[
\langle (\sigma, \Psi'), C \land C' \rangle
\rightarrowtail
\langle (\sigma', \Psi''), C' \rangle
\]
that is the tuple $(\sigma', \Psi'') \in sol(C)$. Recall that we treat
transition constraints as lists
\[
(\nu\ve{a_1})\constr{\Psi_1\vdash \varphi_1}
    \land ((\nu\ve{a_2})\constr{\Psi_2\vdash \varphi_2}
    \land \cdots ( \cdots \land \mathbf{true} ) \cdots )
\]
and there is no generality lost since $\land$ is associative.

In order to find a solution $(\sigma,\Psi')$ to a constraint $C$ we invoke
\[
\langle (\mathrm{Id},\emptyset), C \rangle \rightarrowtail^* \langle
(\sigma,\Psi'), \mathbf{true} \rangle
\]
where $\rightarrowtail^*$ is a transitive reflexive closure of
$\rightarrowtail$, and $\mathrm{Id}$ is the identity (empty) substitution.
We may also extract all the solutions generated by the rules in
figure \ref{common-ether:rules} by taking all possible paths.

Now that the mechanics of the transition system is established, we
turn to the motivation of the rules. We start with
\textsc{(Ce5)} - \textsc{(Ce7)}. Suppose we have the constraint
\[
C = (\nu\varepsilon)\constr{ \emptyset \vdash a \sch b}
\]
where neither $a$, nor $b$ are bound and $a\freshin b$. Note that
$sol(C) = sol(C \land\mathbf{true})$. What solutions to $C$ we can deduce?
We can always make names channel equivalent by just putting them
in the environment, thus one possible solution is $(Id, \{a,b\})$
(rule \textsc{(Ce5)}), i.e., $\{a,b\}\vdash a \sch b$ holds by definition.
Another possibility is putting only one name into an environment
and replacing the other with that name, this gives us this solution
$([a:=b], \{b\})$, i.e., $\{b\} \vdash b \sch b$ (rule \textsc{(Ce6)}).
And the last possibility is a symmetric version of the previous solution
(rule \textsc{(Ce7)}). There are more solutions to the $C$ constraint, but
we do not want to include ``junk''.

This generalises to partial solutions. For the above example the tree of
solutions look like
\[
\xymatrix@M+=0.8em@C=0em{
 & \langle (Id, \emptyset), C \rangle
 \ar@{>->}[d]\ar@{>->}[dl]\ar@{>->}[dr] & \\
\langle (Id, \{a,b\}), \mathbf{true} \rangle &
\langle ([a:=b], \{b\}), \mathbf{true} \rangle &
\langle ([b:=a], \{a\}), \mathbf{true} \rangle
}
\]

Now suppose we have the constraint
\[
(\nu\varepsilon)\constr{\{b\} \vdash a \sch b}
\]
there are two possible solutions either we substitute $a$ with $b$
(rule \textsc{(Ce1)}) or add the name $a$ to the environment
(rule \textsc{(Ce2)}).
If we were to restrict the name $b$ as
\[
(\nu b)\constr{\{b\} \vdash a \sch b}
\]
then we would be facing one possibility -- adding $a$ to the environment
(rule \textsc{(Ce2)}). The rules \textsc{(Ce2)} and \textsc{(Ce4)} are
symmetrical versions of the rules \textsc{(Ce1)} and \textsc{(Ce3)}, respectively.

The rule \textsc{(Ce8)} is a trivial case when the constraint is entailed
without need for further refinement.
The rule \textsc{(Ce9)} signifies failure where there are no
solutions for a constraint. This is the case when no other rule applies.


The function \sml{tr} implements the rules given in figure
\ref{common-ether:rules}. The function is presented with a partial solution and a
constraint, and tries to determine which of the rules are applicable by testing
side conditions of rules (the first element of a tuple of the list \sml{rules}).
Then the list of applicable rules is constructed by collecting only the
functions with a true side condition and those functions are evaluated, i.e.~a
partial solution is computed. If there are no such functions \sml{tr} signals a
failure with the function \sml{fail}. If there are such functions then a node is
constructed with the function \sml{node}, and all the branches are recursively
computed. The functions \sml{node} and \sml{fail} are discussed later.

*)
  fun tr ((sigma, psi'), []) = node ((sigma,psi'),[])
    | tr ((sigma, psi'),((c as (avec, psi, (Eq (a,b))))::cs))
    = Constraint.subst [c] sigma |>
    (fn [(_, psi'', (Eq (a',b')))] =>
        let
          val psi'' = compose (psi'', psi')
          (* menmonic af = a is fresh in avec *)
          val af    = L.fresh a avec
          val bf    = L.fresh b avec
          val af'   = L.fresh a' psi''
          val bf'   = L.fresh b' psi''
          (* mnemonic am = a is member of avec *)
          val am    = not af
          val bm    = not bf
          val am'   = not af'
          val bm'   = not bf'
          val rules = [
          (* CE1 *)
          ((af andalso af' andalso bf andalso bm'),
            (fn () => (composeSubst sigma (a',b'), psi'))),

          (* CE2 *)
          ((af andalso af' andalso bm'),
            (fn () => (sigma, compose(psi', [a'])))),

          (* CE3 *)
          ((af andalso am' andalso bf andalso bf'),
            (fn () => (composeSubst sigma (b',a'), psi'))),

          (* CE4 *)
          ((am' andalso bf andalso bf'),
            (fn () => (sigma, compose(psi', [b'])))),

          (* CE5 *)
          ((af andalso af' andalso bf andalso bf'),
            (fn () => (sigma, compose(psi', [a',b'])))),

          (* CE6 *)
          ((af andalso af' andalso bf andalso bf'),
            (fn () => (composeSubst sigma (a',b'),
                       compose(psi', [b'])))),

          (* CE7 *)
          ((af andalso af' andalso bf andalso bf'),
            (fn () => (composeSubst sigma (b',a'),
                       compose(psi', [a'])))),

          (* CE8 *)
          ((entails (psi'', Eq (a',b'))),
            (fn () => (sigma, psi')))
          ]

          val valid = map (fn (_,c) => c ())
            (List.filter (fn (cond, sol) => cond) rules)
        in
          case valid of
               [] => fail ()
             | _  => node ((sigma,psi'),
                           map (fn sol => tr (sol, cs)) valid)
        end
      | _ => Err.undefined ())
(**

These two functions imitate the construction of the solution tree and can be
thought of as
typical \SML{} data constructors. But we do not need the internal nodes of the
tree, hence
these functions discard the intermediate results. The function \sml{fail} just
returns an empty list. The function \sml{node} takes two arguments (as a tuple)
where the first is the node -- a partial solution $(\sigma,\Psi)$ -- and the
second is a list of nodes branches. Since we do not keep the intermediary
structure, when a we encounter a leaf node (a node without branches) we return
a singleton list with that node, otherwise we drop the node and return the
union of branches.

*)
  and fail () = []
  and node (n,[]) = [n]
    | node (n,l)  = List.concat l
(**

The only thing is left to do is to plug the function \sml{tr} into
the function \sml{solve}.
*)
  fun solve cs =
  let
    val sols = tr (([], []), cs)
  in
    case sols of
         [] => Either.LEFT []
       | _  => Either.RIGHT sols
  end
(**


This ends the common ether example. The common ether Psi-calculus instance
introduces the non-trivial assertions, due to this extra effort is required for
designing a transition constraint solver. It is a mix of finding a mgu and
careful case analysis. This demonstrates the Psi-calculus versatility, showing
that we can implement very interesting logics completely outside of the
Psi-calculi meta-theory.

*)(**[skip]*)
  structure BisimConstraint = BisimConstraint(CommonEtherNom)
  val solveBisim = NONE
end;

structure CommonEtherCalculus : C_PSI =
struct
  open CommonEtherSymbolicInstance

  fun printN a = a
  fun printT a = a
  fun printC (Eq (a, b)) = a ^ " = " ^ b
  fun printA psi = String.concat (Lst.intersperse ", " psi)

  structure Parser = Parser(StringStream)
  structure Lex = PsiParserBase(Parser)

  local
    open Parser
    open Missing
  in

  fun parseResult p s =
    case Parser.parse p (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  val name = Lex.identifier

  val cond =  name >>=
    (fn a =>    Lex.stok "=" >>
                name >>=
    (fn b =>    Parser.return (Eq (a,b))
    ))
  val assr = name </sepby/> (Lex.stok ",")

  fun parseN s = parseResult name s
  fun parseT s = parseResult name s
  fun parseC s = parseResult cond s
  fun parseA s = parseResult assr s

  end
end;
(**[default]*)(**


%  We may introduce an ordering on the solutions for measuring the quality
%  of the solutions. The ordering on the substitution
%  function is the usual one $\sigma \leq \tau \iff (\exists \rho) \tau =
%  \sigma\rho$, as we are dealing with renaming substitutions therefore
%  the ordering can be simplified to
%
%  \[
%  \sigma \leq \tau \iff dom(\sigma) \subseteq dom(\tau)
%  \]
%
%  The ordering on assertions is the obvious one.
%
%  \[
%  \Psi \leq \Psi' \iff \Psi \subseteq \Psi'
%  \]
%
%  And the ordering on solutions is the induced one.
%
%  \[
%  (\sigma, \Psi) \leq (\sigma', \Psi') \iff \sigma \leq \sigma' \land
%  \Psi\leq\Psi'
%  \]
%
%  All the above introduced orderings are partial orders.
%
%
%  The rules given in the figure \ref{common-ether:rules} are
%  sound, complete and terminating.
%
%  \begin{lemma}[Completeness]
%  If $(\sigma, \Psi') \in sol(C)$ then there is $(\sigma', \Psi'')$
%  such that
%  $\langle (\mathrm{Id},\emptyset), C \rangle \rightarrowtail^* \langle
%  (\sigma',\Psi''), \mathbf{true} \rangle$ and
%  $(\sigma', \Psi'') \leq (\sigma, \Psi')$.
%  \end{lemma}
%
%  \begin{lemma}[Soundness]
%  If $\langle (\mathrm{Id},\emptyset), C \rangle \rightarrowtail^* \langle
%  (\sigma,\Psi'), \mathbf{true} \rangle$ then
%  $(\sigma, \Psi') \in sol(C)$.
%  \end{lemma}
%
%  \begin{lemma}[Termination]
%  The rules given in the figure \ref{common-ether:rules} are terminating.
%  \end{lemma}
%  \begin{proof}
%  Obvious, as the constraint only, structuraly, gets smaller.
%  \end{proof}

*)(**[skip]*)
structure CommonEther = Command(CommonEtherCalculus)

