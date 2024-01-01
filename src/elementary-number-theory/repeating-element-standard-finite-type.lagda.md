# Repeating an element in a standard finite type

```agda
module elementary-number-theory.repeating-element-standard-finite-type where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.unit-type

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

```agda
repeat-Fin :
  (k : ℕ) (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin = {!!}
repeat-Fin (succ-ℕ k) (inl x) (inr _) = {!!}
repeat-Fin (succ-ℕ k) (inr _) (inl y) = {!!}
repeat-Fin (succ-ℕ k) (inr _) (inr _) = {!!}

abstract
  is-almost-injective-repeat-Fin :
    (k : ℕ) (x : Fin k) {y z : Fin (succ-ℕ k)} →
    inl x ≠ y → inl x ≠ z →
    repeat-Fin k x y ＝ repeat-Fin k x z → y ＝ z
  is-almost-injective-repeat-Fin = {!!}
```
