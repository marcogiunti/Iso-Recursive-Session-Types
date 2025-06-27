# Iso-Recursive Binary Session Types


## Software prerequisite

```
opam switch create ISOST 5.2.0
eval $(opam env --switch=ISOST)
opam pin add coq 8.19.1
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
    Coq.Logic.Classical_Prop.classic
    Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```


## Structure of folder `theories`
* [iso-bst.v](theories/iso-bst.v) contains the [Subject Reduction Theorem](theories/iso-bst.v#L4333-L4389)
* [operations.v](theories/operations.v)  contains operations on Lists
* [header.v](theories/header.v) contains case tactics
* [CpdtTactics.v](theories/CpdtTactics.v) contains tactics written by Adam Chlipala
* [LibTactics.v](theories/LibTactics.v) contains tactics written by Arthur Chargueraud
