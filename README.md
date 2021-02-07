# Dependent Polymorphic Subtyping

## Dependencies

- [The Coq Proof Assistant](https://coq.inria.fr/) (tested with version 8.10.2)
- [ott](https://github.com/ott-lang/ott) (version 0.30, generating locally nameless representation from a language specification)
- [coq-ott](https://github.com/ott-lang/ott/blob/master/coq-ott.opam) (version 0.30, a library required by ott to generate coq definitions)
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
| `context_narrowing`                 | Context Narrowing                                         | BasicProperties.v    |
| `reduction_substitution`            | Reduction Substitution                                    | Properties.v         |
| `substitution`                      | Substitution                                              | Properties.v         |
| `type_correctness`                  | Type Correctness                                          | Properties.v         |
| `gen_kind_uniqueness`               | Kind Uniqueness                                           | KindUniqueness.v     |
| `generalized_transitivity`          | Generalized Transitivity                                  | Transitivity.v       |
| `transitivity`                      | Transitivity                                              | Transitivity.v       |
| `reducible_type`                    | Reducible Type                                            | Semantics.v          |
| `generalized_progress`              | Generalized Progress                                      | Semantics.v          |
| `progress`                          | Progress                                                  | Semantics.v          |
| `generalized_erased_progress`       | Generalized Progress on erased expression                 | Semantics.v          |
| `extracted_progress`                | Progress on erased expression                             | Semantics.v          |
| `deterministic_type_reduction`      | Deterministic Type Reduction                              | Semantics.v          |
| `type_preservation`                 | Subtype Preservation for Types                            | Semantics.v          |
| `deterministic_reduction`           | Deterministic Reduction                                   | Semantics.v          |
| `deterministic_erased_reduction`    |                                                           | Semantics.v          |
| `expr_of_box_never_be_reduced`      | Expressions of kind $\square$ are never reduced           | Semantics.v          |
| `preservation`                      | Subtype Preservation                                      | Semantics.v          |
| `value_evalue`                      | Value to Erased Value                                     | Extraction.v         |
| `evalue_value`                      | Erased Value to Value                                     | Extraction.v         |
| `soundness`<br />`completeness`     | Equivalence of $\lambda_I^\forall$ and the Simplification | SimplifiedLanguage.v |
| `dk_wftype_welltyped`               | Subsumption of Type Well-formedness                       | DKSubsumption.v      |
| `dk_sub_subsumption`                | Subsumption of Polymorphic Subtyping                      | DKSubsumption.v      |

