# Determinism Types for Functional Logic Programming

NOTE: due to time constraints, the formalization is not yet fully updated
to the paper. Should be updated by mid June. Differences are:
- A different simplified Curry type system with only types Unit and Pairs.
  Consequently, our expressions have different data constructors as well.
- Compatibility is used differently, in the sense that we constructively
  build compatible types and contexts, rather than using a
  compatibility relation.

For the reason that we still have to update the formalization,
there are currently two small sections where this formalization
is not yet completely machine-checked. We will address this in the near future.
These points are the application of the substitution lemma on determinsm
types in the preservation theorem for case and function application.
At the moment, there is a consistency problem between the way compatibility
is used in the preservation theorem statement and the way it is used in the
substitution lemma.

Other than these differences, you can check that this corresponds to the paper.
Just search in this document for the following important theorems and
definitions:
- "typeOf" corresponds to the simplified Curry type system
- compatibility is as defined in the paper
- "Exp" is the type of expressions
- "DType" is the type of deterministic types
- "TType" is the type of Curry types
- "more_specific" is the subtyping relation
- "Gamma '|-' e ':::' delta" is the Deterministic typing relation
- "step" (or "==>") is the small-step semantics
- "subst" is the substitution function
- "notOr" is the definition for a deterministic result
- Important Theorems are: "completeness", "preservation" and "soundness"

Also, I am a rocq novice, so this is probably not the most elegant
formalization. If you have suggestions for improvements, please let me know.
