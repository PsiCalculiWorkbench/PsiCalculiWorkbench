Symbolic Semantics
==================

.. Some math definitions
.. math::

    \newcommand\ve[1]{\tilde{#1}}
    \newcommand\sort[1]{\mathsf{Sort}(#1)}
    \newcommand\entails\vdash
    \newcommand\chEq{\stackrel{\cdot}{\leftrightarrow}}
    \newcommand\frameEq\simeq
    \newcommand\compose\otimes
    \newcommand\Unit{\mathbf{1}}


Requirements on psi-calculus parameters
---------------------------------------

Channel properties

.. math::

    \text{Channel Symmetry}\; & \Psi\entails M \chEq N  \implies \Psi\entails N\chEq M \\
    \text{Channel Transitivity}\; & \Psi\entails M \chEq N \land  \Psi\entails N \chEq L \implies \Psi\entails M\chEq L


Assertion properties

.. math::

    \text{Composition} & \Psi\frameEq\Psi' \implies \Psi\compose\Psi'' \frameEq \Psi'\compose\Psi'' \\
    \text{Identity} & \Psi\compose\Unit \frameEq \Psi \\
    \text{Associativity} & (\Psi\compose\Psi')\compose\Psi'' \frameEq \Psi\compose(\Psi'\compose\Psi'') \\
    \text{Commutativity} & \Psi\compose\Psi' \frameEq \Psi'\compose\Psi

Entailement properties

.. math::

    \text{Wakening}\; \Psi\entails\varphi \implies \Psi\compose\Psi'\entails\varphi

Name are terms

.. math::

    \mathcal{N} \subseteq \mathbf{T}


Broadcast requirements
----------------------

.. math::

    \Psi\entails M \stackrel{\cdot}{\prec} K \implies n(K) \subseteq n(M)

    \Psi\entails K \stackrel{\cdot}{\succ} M \implies n(K) \subseteq n(M)


Sorted Substitution Requirements
--------------------------------

Substitution :math:`[\ve{a} := \ve{N}]` is well formed if

.. math::

    \sort{a_i}\prec\sort{N_i}

substitution must land in the same datatype it started with.

requirements, :math:`T \in \mathbf{T, A, C}`

.. math::

    T[\ve{a} := \ve{N}] = ((\ve{a}\,\ve{b})\cdot T)[\ve{b} := \ve{N}]

alpha-renaming of substituted variables, and

.. math::

    \sort{M\sigma} \leq \sort{M}
    



Extra requirements of bisimulation algorithm on substitution
------------------------------------------------------------

.. math::

    X[x := x] = X

    x[x := M] = M

    X[x := M] = X  \text{ whenever } x\# X

    X[x := L][y := M] = X[y := M][x := L] \text{ whenever } x\# y, M \text{ and } y\# L


where :math:`x`, :math:`y` are names, :math:`X`, :math:`M`, :math:`L` are terms.


References
----------

* M. Johansson, B. Victor, and J. Parrow. `Computing strong and weak bisimulations for psi-calculi - with proofs <http://www.it.uu.se/research/publications/reports/2011-018/>`_. Technical Report 2011-018, Department of Information Technology, Uppsala University, Aug.  2011.
* J. Bengtson, M. Johansson, J. Parrow, and B. Victor. `Psi-calculi: a framework for mobile processes with nominal data and logic. <http://arxiv.org/abs/1101.3262>`_ Logical Methods in Computer Science, 7(1:11), 01 2011.

