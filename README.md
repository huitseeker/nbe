Normalization by evaluation for simply-typed lambda-calculus, in Coq
================================

This is the Coq formalization featured in the paper I wrote with Benjamin
Werner,

>  B. Werner and F. Garillot, “Simple Types in Type Theory: Deep and
>     Shallow Encodings,” Theorem Proving in Higher Order Logics:
>     20th International Conference, TPHOLs 2007, Kaiserslautern, Germany,
>     September 10-13, 2007, Proceedings, Springer-Verlag New York Inc,
>     2007, p. 368.

How to run
------------------------

* it depends on an **old** (included) version of [Ssreflect][1].
* it assumes, in nbe_fvc.v, a proof of the confluence theorem for the
  simpli-typed lambda-calculus (Church-Rosser). It is true and formalized (in
  e.g. Isabelle, see file comments) but we found no modern Coq formalization at
  the time (though Gerard Huet did one in his time).
* it implements, generically, Stoughton's
  [explicit substitution framework][2] for bindings, (to my knowledge) a
  first for theorem provers.


[1]: http://ssr.msr-inria.inria.fr
[2]: A. Stoughton, “Substitution revisited,” Theoretical Computer Science, vol. 59, 1988, p. 317–325.
