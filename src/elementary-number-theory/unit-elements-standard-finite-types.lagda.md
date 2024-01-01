# Unit elements in the standard finite types

```agda
module elementary-number-theory.unit-elements-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-standard-finite-types
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A unit element in a standard finite type is a divisor of one

## Definition

### Units in the standard finite types

```agda
is-unit-Fin : (k : ℕ) → Fin k → UU lzero
is-unit-Fin = {!!}

unit-Fin : ℕ → UU lzero
unit-Fin = {!!}
```

## Properties

### One is a unit

```agda
is-unit-one-Fin : {k : ℕ} → is-unit-Fin (succ-ℕ k) (one-Fin k)
is-unit-one-Fin = {!!}

one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
one-unit-Fin = {!!}
pr2 (one-unit-Fin {k}) = {!!}
```

### Negative one is a unit

```agda
is-unit-neg-one-Fin : {k : ℕ} → is-unit-Fin (succ-ℕ k) (neg-one-Fin k)
is-unit-neg-one-Fin = {!!}
pr1 (is-unit-neg-one-Fin {succ-ℕ k}) = {!!}
pr2 (is-unit-neg-one-Fin {succ-ℕ k}) = {!!}

neg-one-unit-Fin : (k : ℕ) → unit-Fin (succ-ℕ k)
neg-one-unit-Fin = {!!}
pr2 (neg-one-unit-Fin k) = {!!}
```

### Units are closed under multiplication

```agda
is-unit-mul-Fin :
  {k : ℕ} {x y : Fin k} →
  is-unit-Fin k x → is-unit-Fin k y → is-unit-Fin k (mul-Fin k x y)
is-unit-mul-Fin = {!!}

mul-unit-Fin : (k : ℕ) → unit-Fin k → unit-Fin k → unit-Fin k
mul-unit-Fin = {!!}
pr2 (mul-unit-Fin k u v) = {!!}
```

### The multiplicative inverse of a unit

```agda
inv-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k
inv-unit-Fin = {!!}
pr1 (pr2 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p)))) = {!!}
pr2 (pr2 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p)))) = {!!}
```
