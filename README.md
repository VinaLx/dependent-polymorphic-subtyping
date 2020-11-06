# Dependent Polymorphic Subtyping

## Dependencies

- [The Coq Proof Assistant](https://coq.inria.fr/) (tested with version 8.10.2)
- [ott](https://github.com/ott-lang/ott) (version 0.30, generating locally nameless representation from a language specification)
- [metalib](https://github.com/plclub/metalib) (library supporting the locally nameless representation for ott)

## Build

```
$ make coq
```

`make` should fire up the coq compiler trying to check all the formalization. If anything works fine, there should be no error emitted.

## Theorem Index

The formalizations are all located in directory `./src/proofs/`

| Theorem/Lemma                       | Name Used in Literature                                   | File                 |
| ----------------------------------- | --------------------------------------------------------- | -------------------- |
| `reflexivity_l`                     | Left Reflexivity                                          | BasicProperties.v    |
| `reflexivity_r`                     | Right Reflexivity                                         | BasicProperties.v    |
| `weakening`                         | Weakening                                                 | BasicProperties.v    |
| `ctx_narrowing`                     | Context Narrowing                                         | BasicProperties.v    |
| `reduce_subst`                      | Reduction Substitution                                    | Properties.v         |
| `substitution`                      | Substitution                                              | Properties.v         |
| `type_correctness`                  | Type Correctness                                          | Properties.v         |
| `gen_kind_uniqueness`               | Kind Uniqueness                                           | KindUniqueness.v     |
| `transitivity'`                     | Generalized Transitivity                                  | Transitivity.v       |
| `transitivity`                      | Transitivity                                              | Transitivity.v       |
| `irreducible_value`                 | Reducible Type                                            | Semantics.v          |
| `progress`                          | Progress                                                  | Semantics.v          |
| `extracted_progress`                | Progress on erased expression                             | Semantics.v          |
| `deterministic_type_reduction`      | Deterministic Type Reduction                              | Semantics.v          |
| `type preservation`                 | Subtype Preservation for Types                            | Semantics.v          |
| `dreduce_deterministic`             | Deterministic Reduction                                   | Semantics.v          |
| `deterministic_extracted_reduction` |                                                           | Semantics.v          |
| `expr_of_box_never_be_reduced`      | Expressions of kind $\square$ are never reduced           | Semantics.v          |
| `preservation`                      | Subtype Preservation                                      | Semantics.v          |
| `value_evalue`                      | Value to Erased Value                                     | Extraction.v         |
| `evalue_value`                      | Erased Value to Value                                     | Extraction.v         |
| `soundness`<br />`completeness`     | Equivalence of $\lambda_I^\forall$ and the Simplification | SimplifiedLanguage.v |
| `dk_wftype_welltyped`               | Subsumption of Type Well-formedness                       | DKSubsumption.v      |
| `dk_sub_subsumption`                | Subsumption of Polymorphic Subtyping                      | DKSubsumption.v      |

