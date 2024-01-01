# Inequality on the integers

```agda
module elementary-number-theory.inequality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Definition

```agda
leq-ℤ-Prop : ℤ → ℤ → Prop lzero
leq-ℤ-Prop x y = {!!}

leq-ℤ : ℤ → ℤ → UU lzero
leq-ℤ x y = {!!}

is-prop-leq-ℤ : (x y : ℤ) → is-prop (leq-ℤ x y)
is-prop-leq-ℤ x y = {!!}

infix 30 _≤-ℤ_
_≤-ℤ_ = {!!}
```

## Properties

```agda
refl-leq-ℤ : (k : ℤ) → leq-ℤ k k
refl-leq-ℤ k = {!!}

antisymmetric-leq-ℤ : {x y : ℤ} → leq-ℤ x y → leq-ℤ y x → x ＝ y
antisymmetric-leq-ℤ {x} {y} H K = {!!}

transitive-leq-ℤ : (k l m : ℤ) → leq-ℤ k l → leq-ℤ l m → leq-ℤ k m
transitive-leq-ℤ k l m p q = {!!}

decide-leq-ℤ :
  {x y : ℤ} → (leq-ℤ x y) + (leq-ℤ y x)
decide-leq-ℤ {x} {y} = {!!}

succ-leq-ℤ : (k : ℤ) → leq-ℤ k (succ-ℤ k)
succ-leq-ℤ k = {!!}

leq-ℤ-succ-leq-ℤ : (k l : ℤ) → leq-ℤ k l → leq-ℤ k (succ-ℤ l)
leq-ℤ-succ-leq-ℤ k l p = {!!}

concatenate-eq-leq-eq-ℤ :
  {x' x y y' : ℤ} → x' ＝ x → leq-ℤ x y → y ＝ y' → leq-ℤ x' y'
concatenate-eq-leq-eq-ℤ refl H refl = {!!}

concatenate-leq-eq-ℤ :
  (x : ℤ) {y y' : ℤ} → leq-ℤ x y → y ＝ y' → leq-ℤ x y'
concatenate-leq-eq-ℤ x H refl = {!!}

concatenate-eq-leq-ℤ :
  {x x' : ℤ} (y : ℤ) → x' ＝ x → leq-ℤ x y → leq-ℤ x' y
concatenate-eq-leq-ℤ y refl H = {!!}
```

### The strict ordering on ℤ

```agda
le-ℤ-Prop : ℤ → ℤ → Prop lzero
le-ℤ-Prop x y = {!!}

le-ℤ : ℤ → ℤ → UU lzero
le-ℤ x y = {!!}

is-prop-le-ℤ : (x y : ℤ) → is-prop (le-ℤ x y)
is-prop-le-ℤ x y = {!!}
```

### ℤ is an ordered ring

```agda
preserves-order-add-ℤ' :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (x +ℤ z) (y +ℤ z)
preserves-order-add-ℤ' {x} {y} z = {!!}

preserves-order-add-ℤ :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (z +ℤ x) (z +ℤ y)
preserves-order-add-ℤ {x} {y} z = {!!}

preserves-leq-add-ℤ :
  {a b c d : ℤ} → leq-ℤ a b → leq-ℤ c d → leq-ℤ (a +ℤ c) (b +ℤ d)
preserves-leq-add-ℤ {a} {b} {c} {d} H K = {!!}

reflects-order-add-ℤ' :
  {x y z : ℤ} → leq-ℤ (x +ℤ z) (y +ℤ z) → leq-ℤ x y
reflects-order-add-ℤ' {x} {y} {z} = {!!}

reflects-order-add-ℤ :
  {x y z : ℤ} → leq-ℤ (z +ℤ x) (z +ℤ y) → leq-ℤ x y
reflects-order-add-ℤ {x} {y} {z} = {!!}
```

### Inclusion of ℕ into ℤ preserves order

```agda
leq-int-ℕ : (x y : ℕ) → leq-ℕ x y → leq-ℤ (int-ℕ x) (int-ℕ y)
leq-int-ℕ zero-ℕ y H = {!!}
leq-int-ℕ (succ-ℕ x) (succ-ℕ y) H = {!!}
```
