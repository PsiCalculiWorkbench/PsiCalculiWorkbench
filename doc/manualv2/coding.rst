Coding Conventions
==================

Here are some coding conventions used in Pwb.


Function names are *camelCased* with initial lowercase letter.

::

    val thisIsAFunction: type1 -> ... -> type_n -> type
    fun thisIsAFunction x1 ... xn = 


Prefer curried function over tupled: do ``fun add x y = x + y`` instead of
``fun add (x,y) = x + y``.

Signature names are in all capitals and words are separated by underscore "_".

::

    signature SIGNATURE_NAME = sig ... end

* Indent is 2 spaces (no tabs are allowed).
* Structure and functor names are CamelCase with initial capital letter.
* Type names are lowercased and words are seperated by underscore.
* Type constructors are CamelCased.
* Always indent when introducing scope.
* In datatypes align | with the equals sign if the declaration in question
  spans multiple lines.
* Partial functions are modeled with option and either types. Exceptions should
  be only used with imperative code.

