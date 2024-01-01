# Squares in the integers

```agda
module elementary-number-theory.squares-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
```

</details>

## Definition

```agda
square-ℤ : ℤ → ℤ
square-ℤ a = {!!}

cube-ℤ : ℤ → ℤ
cube-ℤ a = {!!}

is-square-ℤ : ℤ → UU lzero
is-square-ℤ a = {!!}

square-root-ℤ : (a : ℤ) → is-square-ℤ a → ℤ
square-root-ℤ _ (root , _) = {!!}
```

## Properties

### Squares in ℤ are nonnegative

```agda
is-decidable-is-nonnegative-square-ℤ :
  (a : ℤ) →
  (is-nonnegative-ℤ a) + (is-nonnegative-ℤ (neg-ℤ a)) →
  is-nonnegative-ℤ (square-ℤ a)
is-decidable-is-nonnegative-square-ℤ = {!!}

is-nonnegative-square-ℤ : (a : ℤ) → is-nonnegative-ℤ (square-ℤ a)
is-nonnegative-square-ℤ a = {!!}
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℤ (int-ℕ n)
is-square-int-is-square-nat (root , pf-square) = {!!}

is-square-nat-is-square-int : {a : ℤ} → is-square-ℤ a → is-square-ℕ (abs-ℤ a)
is-square-nat-is-square-int (root , pf-square) = {!!}

iff-is-square-int-is-square-nat :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℤ (int-ℕ n)
iff-is-square-int-is-square-nat = {!!}

iff-is-nonneg-square-nat-is-square-int :
  (a : ℤ) → is-square-ℤ a ↔ is-nonnegative-ℤ a × is-square-ℕ (abs-ℤ a)
iff-is-nonneg-square-nat-is-square-int = {!!}
```

### Squareness in ℤ is decidable

```agda
is-decidable-is-square-ℤ : (a : ℤ) → is-decidable (is-square-ℤ a)
is-decidable-is-square-ℤ (inl n) = {!!}
is-decidable-is-square-ℤ (inr (inl n)) = {!!}
is-decidable-is-square-ℤ (inr (inr n)) = {!!}
```
