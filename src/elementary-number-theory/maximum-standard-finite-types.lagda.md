# Maximum on the standard finite types

```agda
module elementary-number-theory.maximum-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of maximum (least upper bound) for the standard finite
types.

## Definition

```agda
max-Fin : (k : ℕ) → Fin k → Fin k → Fin k
max-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
max-Fin (succ-ℕ k) (inl x) (inr _) = {!!}
max-Fin (succ-ℕ k) (inr _) (inl x) = {!!}
max-Fin (succ-ℕ k) (inr _) (inr _) = {!!}

max-Fin-Fin : (n k : ℕ) → (Fin (succ-ℕ n) → Fin k) → Fin k
max-Fin-Fin zero-ℕ k f = {!!}
max-Fin-Fin (succ-ℕ n) k f = {!!}
```

## Properties

### Maximum is greatest lower bound

```agda
leq-max-Fin :
  (k : ℕ) (l m n : Fin k) →
  leq-Fin k m l → leq-Fin k n l → leq-Fin k (max-Fin k m n) l
leq-max-Fin = {!!}

leq-left-leq-max-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k (max-Fin k m n) l → leq-Fin k m l
leq-left-leq-max-Fin = {!!}

leq-right-leq-max-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k (max-Fin k m n) l → leq-Fin k n l
leq-right-leq-max-Fin = {!!}

is-least-upper-bound-max-Fin :
  (k : ℕ) (m n : Fin k) →
  is-least-binary-upper-bound-Poset (Fin-Poset k) m n (max-Fin k m n)
is-least-upper-bound-max-Fin = {!!}
```
