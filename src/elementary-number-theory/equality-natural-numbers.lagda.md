# Equality of natural numbers

```agda
module elementary-number-theory.equality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.torsorial-type-families
```

</details>

## Definitions

### Observational equality on the natural numbers

```agda
Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = {!!}
Eq-ℕ zero-ℕ (succ-ℕ n) = {!!}
Eq-ℕ (succ-ℕ m) zero-ℕ = {!!}
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}
```

## Properties

### The type of natural numbers is a set

```agda
abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = {!!}

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = {!!}
refl-Eq-ℕ (succ-ℕ n) = {!!}

Eq-eq-ℕ : {x y : ℕ} → x ＝ y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = {!!}

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → x ＝ y
eq-Eq-ℕ zero-ℕ zero-ℕ e = {!!}
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = {!!}

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ = {!!}

ℕ-Set : Set lzero
pr1 ℕ-Set = {!!}
pr2 ℕ-Set = {!!}
```

### The property of being zero

```agda
is-prop-is-zero-ℕ : (n : ℕ) → is-prop (is-zero-ℕ n)
is-prop-is-zero-ℕ n = {!!}

is-zero-ℕ-Prop : ℕ → Prop lzero
pr1 (is-zero-ℕ-Prop n) = {!!}
pr2 (is-zero-ℕ-Prop n) = {!!}
```

### The property of being one

```agda
is-prop-is-one-ℕ : (n : ℕ) → is-prop (is-one-ℕ n)
is-prop-is-one-ℕ n = {!!}

is-one-ℕ-Prop : ℕ → Prop lzero
pr1 (is-one-ℕ-Prop n) = {!!}
pr2 (is-one-ℕ-Prop n) = {!!}
```

### The type of natural numbers has decidable equality

```agda
is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = {!!}
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = {!!}
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = {!!}
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y = {!!}

decidable-eq-ℕ : ℕ → ℕ → Decidable-Prop lzero
pr1 (decidable-eq-ℕ m n) = {!!}
pr1 (pr2 (decidable-eq-ℕ m n)) = {!!}
pr2 (pr2 (decidable-eq-ℕ m n)) = {!!}

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = {!!}

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = {!!}

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n = {!!}

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = {!!}

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = {!!}

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x = {!!}
```

## The full characterization of the identity type of `ℕ`

```agda
map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
pr1 (map-total-Eq-ℕ m (n , e)) = {!!}
pr2 (map-total-Eq-ℕ m (n , e)) = {!!}

is-torsorial-Eq-ℕ :
  (m : ℕ) → is-torsorial (Eq-ℕ m)
pr1 (pr1 (is-torsorial-Eq-ℕ m)) = {!!}
pr2 (pr1 (is-torsorial-Eq-ℕ m)) = {!!}
pr2 (is-torsorial-Eq-ℕ zero-ℕ) (pair zero-ℕ star) = {!!}
pr2 (is-torsorial-Eq-ℕ (succ-ℕ m)) (pair (succ-ℕ n) e) = {!!}

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} = {!!}
```

### The type of natural numbers is its own set truncation

```agda
equiv-unit-trunc-ℕ-Set : ℕ ≃ type-trunc-Set ℕ
equiv-unit-trunc-ℕ-Set = {!!}
```
