# Minimum on the standard finite types

```agda
module elementary-number-theory.minimum-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import order-theory.greatest-lower-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the standard
finite types.

## Definition

```agda
min-Fin : (k : ℕ) → Fin k → Fin k → Fin k
min-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
min-Fin (succ-ℕ k) (inl x) (inr _) = {!!}
min-Fin (succ-ℕ k) (inr _) (inl x) = {!!}
min-Fin (succ-ℕ k) (inr _) (inr _) = {!!}

min-Fin-Fin : (n k : ℕ) → (Fin (succ-ℕ n) → Fin k) → Fin k
min-Fin-Fin zero-ℕ k f = {!!}
min-Fin-Fin (succ-ℕ n) k f = {!!}
```

## Properties

### Minimum is a greatest lower bound

We prove that `min-Fin` is a greatest lower bound of its two arguments by
showing that `min(m,n) ≤ x` is equivalent to `(m ≤ x) ∧ (n ≤ x)`, in components.
By reflexivity of `≤`, we compute that `min(m,n) ≤ m` (and correspondingly for
`n`).

```agda
leq-min-Fin :
  (k : ℕ) (l m n : Fin k) →
  leq-Fin k l m → leq-Fin k l n → leq-Fin k l (min-Fin k m n)
leq-min-Fin = {!!}

leq-left-leq-min-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k l (min-Fin k m n) → leq-Fin k l m
leq-left-leq-min-Fin = {!!}

leq-right-leq-min-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k l (min-Fin k m n) → leq-Fin k l n
leq-right-leq-min-Fin = {!!}

is-greatest-lower-bound-min-Fin :
  (k : ℕ) (l m : Fin k) →
  is-greatest-binary-lower-bound-Poset (Fin-Poset k) l m (min-Fin k l m)
is-greatest-lower-bound-min-Fin = {!!}
```
