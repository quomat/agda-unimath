# Inequality on the standard finite types

```agda
module elementary-number-theory.inequality-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

```agda
leq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
leq-Fin (succ-ℕ k) x (inr y) = {!!}
leq-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
leq-Fin (succ-ℕ k) (inr x) (inl y) = {!!}

abstract
  is-prop-leq-Fin :
    (k : ℕ) (x y : Fin k) → is-prop (leq-Fin k x y)
  is-prop-leq-Fin = {!!}

leq-Fin-Prop : (k : ℕ) → Fin k → Fin k → Prop lzero
pr1 (leq-Fin-Prop k x y) = {!!}
pr2 (leq-Fin-Prop k x y) = {!!}

leq-neg-one-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → leq-Fin (succ-ℕ k) x (neg-one-Fin k)
leq-neg-one-Fin = {!!}

refl-leq-Fin : (k : ℕ) → is-reflexive (leq-Fin k)
refl-leq-Fin (succ-ℕ k) (inl x) = {!!}
refl-leq-Fin (succ-ℕ k) (inr star) = {!!}

antisymmetric-leq-Fin :
  (k : ℕ) (x y : Fin k) → leq-Fin k x y → leq-Fin k y x → x ＝ y
antisymmetric-leq-Fin = {!!}

transitive-leq-Fin :
  (k : ℕ) → is-transitive (leq-Fin k)
transitive-leq-Fin = {!!}

concatenate-eq-leq-eq-Fin :
  (k : ℕ) {x1 x2 x3 x4 : Fin k} →
  x1 ＝ x2 → leq-Fin k x2 x3 → x3 ＝ x4 → leq-Fin k x1 x4
concatenate-eq-leq-eq-Fin = {!!}

leq-succ-Fin :
  (k : ℕ) (x : Fin k) →
  leq-Fin (succ-ℕ k) (inl-Fin k x) (succ-Fin (succ-ℕ k) (inl-Fin k x))
leq-succ-Fin = {!!}

preserves-leq-nat-Fin :
  (k : ℕ) {x y : Fin k} → leq-Fin k x y → leq-ℕ (nat-Fin k x) (nat-Fin k y)
preserves-leq-nat-Fin = {!!}

reflects-leq-nat-Fin :
  (k : ℕ) {x y : Fin k} → leq-ℕ (nat-Fin k x) (nat-Fin k y) → leq-Fin k x y
reflects-leq-nat-Fin = {!!}
```

### The partial order on the standard finite types

```agda
Fin-Preorder : ℕ → Preorder lzero lzero
pr1 (Fin-Preorder k) = {!!}
pr1 (pr2 (Fin-Preorder k)) = {!!}
pr1 (pr2 (pr2 (Fin-Preorder k))) = {!!}
pr2 (pr2 (pr2 (Fin-Preorder k))) = {!!}

Fin-Poset : ℕ → Poset lzero lzero
pr1 (Fin-Poset k) = {!!}
pr2 (Fin-Poset k) = {!!}
```

## Properties

### Ordering on the standard finite types is decidable

```agda
is-decidable-leq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (leq-Fin k x y)
is-decidable-leq-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
is-decidable-leq-Fin (succ-ℕ k) (inl x) (inr y) = {!!}
is-decidable-leq-Fin (succ-ℕ k) (inr x) (inl y) = {!!}
is-decidable-leq-Fin (succ-ℕ k) (inr x) (inr y) = {!!}

leq-Fin-Decidable-Prop : (k : ℕ) → Fin k → Fin k → Decidable-Prop lzero
pr1 (leq-Fin-Decidable-Prop k x y) = {!!}
pr1 (pr2 (leq-Fin-Decidable-Prop k x y)) = {!!}
pr2 (pr2 (leq-Fin-Decidable-Prop k x y)) = {!!}
```

### Ordering on the standard finite types is linear

```agda
linear-leq-Fin : (k : ℕ) (x y : Fin k) → leq-Fin k x y + leq-Fin k y x
linear-leq-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
linear-leq-Fin (succ-ℕ k) (inl x) (inr y) = {!!}
linear-leq-Fin (succ-ℕ k) (inr x) y = {!!}
```
