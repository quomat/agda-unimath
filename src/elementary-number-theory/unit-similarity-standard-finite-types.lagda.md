# Unit similarity on the standard finite types

```agda
module elementary-number-theory.unit-similarity-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.unit-elements-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Two elements `x y : Fin k` are said to be unit similar if there is a unit
element `u : Fin k` such that `mul-Fin u x = {!!}
structure on `Fin k`.

## Definition

### Unit similarity in `Fin k`

```agda
sim-unit-Fin :
  (k : ℕ) → Fin k → Fin k → UU lzero
sim-unit-Fin = {!!}
```

### Unit similarity on `ℕ`

```agda
sim-unit-ℕ :
  (k : ℕ) → ℕ → ℕ → UU lzero
sim-unit-ℕ = {!!}
```

### Congruence to `1`

```agda
sim-unit-one-ℕ : (k x : ℕ) → UU lzero
sim-unit-one-ℕ k x = {!!}
```

## Properties

### Unit similarity is an equivalence relation

```agda
refl-sim-unit-Fin : {k : ℕ} → is-reflexive (sim-unit-Fin k)
pr1 (refl-sim-unit-Fin {succ-ℕ k} x) = {!!}
pr2 (refl-sim-unit-Fin {succ-ℕ k} x) = {!!}

symmetric-sim-unit-Fin : {k : ℕ} → is-symmetric (sim-unit-Fin k)
pr1 (symmetric-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) = {!!}
pr2 (symmetric-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) = {!!}

transitive-sim-unit-Fin : {k : ℕ} → is-transitive (sim-unit-Fin k)
pr1 (transitive-sim-unit-Fin {succ-ℕ k} x y z (pair v q) (pair u p)) = {!!}
pr2 (transitive-sim-unit-Fin {succ-ℕ k} x y z (pair v q) (pair u p)) = {!!}
```

### A natural number `x` is congruent to `1` modulo `k+1` if and only if `[x]_{k+1}` is unit similar to `1`

```agda
is-unit-similar-one-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (succ-ℕ k) (mod-succ-ℕ k x) (one-Fin k) →
  sim-unit-one-ℕ (succ-ℕ k) x
is-unit-similar-one-sim-unit-mod-succ-ℕ = {!!}
```
