# Equality of integers

```agda
module elementary-number-theory.equality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.set-truncations
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An equality predicate is defined by pattern matching on the integers. Then we
show that this predicate characterizes the identit type of the integers

## Definition

```agda
Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = {!!}
Eq-ℤ (inl x) (inr y) = {!!}
Eq-ℤ (inr x) (inl y) = {!!}
Eq-ℤ (inr (inl x)) (inr (inl y)) = {!!}
Eq-ℤ (inr (inl x)) (inr (inr y)) = {!!}
Eq-ℤ (inr (inr x)) (inr (inl y)) = {!!}
Eq-ℤ (inr (inr x)) (inr (inr y)) = {!!}

refl-Eq-ℤ : (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = {!!}
refl-Eq-ℤ (inr (inl x)) = {!!}
refl-Eq-ℤ (inr (inr x)) = {!!}

Eq-eq-ℤ : {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-eq-ℤ {x} {.x} refl = {!!}

eq-Eq-ℤ : (x y : ℤ) → Eq-ℤ x y → x ＝ y
eq-Eq-ℤ (inl x) (inl y) e = {!!}
eq-Eq-ℤ (inr (inl star)) (inr (inl star)) e = {!!}
eq-Eq-ℤ (inr (inr x)) (inr (inr y)) e = {!!}
```

## Properties

### Equality on the integers is decidable

```agda
has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ = {!!}

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = {!!}

is-decidable-is-one-ℤ :
  (x : ℤ) → is-decidable (is-one-ℤ x)
is-decidable-is-one-ℤ x = {!!}

is-decidable-is-neg-one-ℤ :
  (x : ℤ) → is-decidable (is-neg-one-ℤ x)
is-decidable-is-neg-one-ℤ x = {!!}

ℤ-Discrete-Type : Discrete-Type lzero
pr1 ℤ-Discrete-Type = {!!}
pr2 ℤ-Discrete-Type = {!!}
```

### The type of integers is its own set truncation

```agda
equiv-unit-trunc-ℤ-Set : ℤ ≃ type-trunc-Set ℤ
equiv-unit-trunc-ℤ-Set = {!!}
```

### Equality on the integers is a proposition

```agda
is-prop-Eq-ℤ :
  (x y : ℤ) → is-prop (Eq-ℤ x y)
is-prop-Eq-ℤ (inl x) (inl y) = {!!}
is-prop-Eq-ℤ (inl x) (inr y) = {!!}
is-prop-Eq-ℤ (inr x) (inl x₁) = {!!}
is-prop-Eq-ℤ (inr (inl x)) (inr (inl y)) = {!!}
is-prop-Eq-ℤ (inr (inl x)) (inr (inr y)) = {!!}
is-prop-Eq-ℤ (inr (inr x)) (inr (inl y)) = {!!}
is-prop-Eq-ℤ (inr (inr x)) (inr (inr y)) = {!!}

Eq-ℤ-eq :
  {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-ℤ-eq {x} {.x} refl = {!!}

contraction-total-Eq-ℤ :
  (x : ℤ) (y : Σ ℤ (Eq-ℤ x)) → pair x (refl-Eq-ℤ x) ＝ y
contraction-total-Eq-ℤ (inl x) (pair (inl y) e) = {!!}
contraction-total-Eq-ℤ (inr (inl star)) (pair (inr (inl star)) e) = {!!}
contraction-total-Eq-ℤ (inr (inr x)) (pair (inr (inr y)) e) = {!!}

is-torsorial-Eq-ℤ :
  (x : ℤ) → is-torsorial (Eq-ℤ x)
is-torsorial-Eq-ℤ x = {!!}

is-equiv-Eq-ℤ-eq :
  (x y : ℤ) → is-equiv (Eq-ℤ-eq {x} {y})
is-equiv-Eq-ℤ-eq x = {!!}
```
