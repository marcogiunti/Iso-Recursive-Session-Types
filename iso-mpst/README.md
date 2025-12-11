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
    ISOMPST.iso_mpst.elts_compliance
    Coq.Logic.Classical_Prop.classic
    Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
    ISOMPST.iso_mpst.compliance
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```


## Structure of folder `theories`
* [iso-bst.v](theories/iso_mpst.v) contains the [Subject Reduction Theorem](theories/iso_mpst.v#L4361-L4377)
* [operations.v](theories/operations.v)  contains operations on Lists
* [header.v](theories/header.v) contains case tactics
* [CpdtTactics.v](theories/CpdtTactics.v) contains tactics written by Adam Chlipala
* [LibTactics.v](theories/LibTactics.v) contains tactics written by Arthur Chargueraud
