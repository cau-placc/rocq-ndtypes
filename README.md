[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20032589.svg)](https://doi.org/10.5281/zenodo.20032589)
# Rocq Formalization for "Determinism Types for Functional Logic Programming"

**Looking for the version linked in my thesis? Go to the [adaptation_ts branch](https://github.com/cau-placc/rocq-ndtypes/tree/adaptation_ts).**

You can check that this formalization corresponds to the paper.
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
