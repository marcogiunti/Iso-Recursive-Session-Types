# Iso-Recursive Multiparty Session Types


## Software prerequisite

```
opam switch create ISOST 5.2.0
eval $(opam env --switch=ISOST)
opam pin add coq 8.19.2
```

## Compilation

```
make
```

## Re-Compilation

```
make clean
make
```

## Evaluation

```
make validate
```

The output should be:

```
CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms:
    Coq.Logic.ProofIrrelevance.proof_irrelevance
    Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
    Coq.Logic.Classical_Prop.classic
    Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```


## Structure of folder `theories`
* [iso_mpst.v](theories/iso_mpst.v) contains the [Subject Reduction Theorem](theories/iso_mpst.v#L8291-L8323)
* [deadlock_freedom.v](theories/deadlock_freedom.v) contains the [Deadlock Freedom Theorem](theories/deadlock_freedom.v#L1217-L1271)
* [operations.v](theories/operations.v)  contains operations on Lists
* [header.v](theories/header.v) contains case tactics
* [CpdtTactics.v](theories/CpdtTactics.v) contains tactics written by Adam Chlipala
* [LibTactics.v](theories/LibTactics.v) contains tactics written by Arthur Chargueraud

## Main results and their correspondence with the revised paper

| Revised paper | Rocq | Location |
|---|---|---|
| Theorem 5.1 (Standard Subject Reduction) | `subject_reduction_standard` | [iso_mpst.v#L8291-L8323](theories/iso_mpst.v#L8291-L8323) |
| Lemma 5.6 (Compliance Preservation) | `elts_dcompliance` | [iso_mpst.v#L3706-L3785](theories/iso_mpst.v#L3706-L3785) |
| Theorem 6.15 (Deadlock Freedom) | `deadlock_freedom` | [deadlock_freedom.v#L1217-L1271](theories/deadlock_freedom.v#L1217-L1271) |

The revised paper links each mechanised result to its location in this repository.
The labels of the definitions and results of Section 6 of the revised paper (deadlock freedom)
coincide with the names of the corresponding definitions and lemmas in
[deadlock_freedom.v](theories/deadlock_freedom.v).
The mechanisation contains no admitted results; the only axioms are those listed above.
