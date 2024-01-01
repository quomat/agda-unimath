# Type arithmetic with natural numbers

```agda
module elementary-number-theory.type-arithmetic-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.powers-of-two

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.iterating-functions
open import foundation.split-surjective-maps
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We prove arithmetical laws involving the natural numbers

## Laws

### The natural numbers is a fixpoint to the functor `X ↦ 1 + X`

```agda
map-equiv-ℕ : ℕ → unit + ℕ
map-equiv-ℕ zero-ℕ = {!!}
map-equiv-ℕ (succ-ℕ n) = {!!}

map-inv-equiv-ℕ : unit + ℕ → ℕ
map-inv-equiv-ℕ (inl x) = {!!}
map-inv-equiv-ℕ (inr n) = {!!}

is-retraction-map-inv-equiv-ℕ :
  ( map-inv-equiv-ℕ ∘ map-equiv-ℕ) ~ id
is-retraction-map-inv-equiv-ℕ zero-ℕ = {!!}
is-retraction-map-inv-equiv-ℕ (succ-ℕ n) = {!!}

is-section-map-inv-equiv-ℕ :
  ( map-equiv-ℕ ∘ map-inv-equiv-ℕ) ~ id
is-section-map-inv-equiv-ℕ (inl star) = {!!}
is-section-map-inv-equiv-ℕ (inr n) = {!!}

equiv-ℕ : ℕ ≃ (unit + ℕ)
pr1 equiv-ℕ = {!!}
pr2 equiv-ℕ = {!!}
```

### The coproduct `ℕ + ℕ` is equivalent to `ℕ`

```agda
succ-ℕ+ℕ : ℕ + ℕ → ℕ + ℕ
succ-ℕ+ℕ = {!!}

map-ℕ+ℕ-to-ℕ : ℕ + ℕ → ℕ
map-ℕ+ℕ-to-ℕ (inl x) = {!!}
map-ℕ+ℕ-to-ℕ (inr x) = {!!}

action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ :
  (x : ℕ + ℕ) →
    (map-ℕ+ℕ-to-ℕ (succ-ℕ+ℕ x)) ＝
      (succ-ℕ (succ-ℕ (map-ℕ+ℕ-to-ℕ x)))
action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ (inl x) = {!!}
action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ (inr x) = {!!}

is-split-surjective-map-ℕ+ℕ-to-ℕ : is-split-surjective map-ℕ+ℕ-to-ℕ
is-split-surjective-map-ℕ+ℕ-to-ℕ zero-ℕ = {!!}
is-split-surjective-map-ℕ+ℕ-to-ℕ (succ-ℕ zero-ℕ) = {!!}
is-split-surjective-map-ℕ+ℕ-to-ℕ (succ-ℕ (succ-ℕ b)) = {!!}

is-injective-map-ℕ+ℕ-to-ℕ : is-injective map-ℕ+ℕ-to-ℕ
is-injective-map-ℕ+ℕ-to-ℕ {inl x} {inl y} p = {!!}
is-injective-map-ℕ+ℕ-to-ℕ {inl x} {inr y} p = {!!}

  t : ¬ (div-ℕ 2 (succ-ℕ (2 *ℕ y)))
  t = {!!}
is-injective-map-ℕ+ℕ-to-ℕ {inr x} {inl y} p = {!!}

  t : ¬ (div-ℕ 2 (succ-ℕ (2 *ℕ x)))
  t = {!!}
is-injective-map-ℕ+ℕ-to-ℕ {inr x} {inr y} p = {!!}

is-equiv-map-ℕ+ℕ-to-ℕ : is-equiv map-ℕ+ℕ-to-ℕ
is-equiv-map-ℕ+ℕ-to-ℕ = {!!}

ℕ+ℕ≃ℕ : (ℕ + ℕ) ≃ ℕ
ℕ+ℕ≃ℕ = {!!}

map-ℕ-to-ℕ+ℕ : ℕ → ℕ + ℕ
map-ℕ-to-ℕ+ℕ = {!!}

is-equiv-map-ℕ-to-ℕ+ℕ : is-equiv map-ℕ-to-ℕ+ℕ
is-equiv-map-ℕ-to-ℕ+ℕ = {!!}
```

### The iterated coproduct `ℕ + ℕ + ... + ℕ` is equivalent to `ℕ` for any n

```agda
equiv-iterated-coproduct-ℕ :
  (n : ℕ) → (iterate n (_+_ ℕ) ℕ) ≃ ℕ
equiv-iterated-coproduct-ℕ zero-ℕ = {!!}
equiv-iterated-coproduct-ℕ (succ-ℕ n) = {!!}
```

### The product `ℕ × ℕ` is equivalent to `ℕ`

```agda
ℕ×ℕ≃ℕ : (ℕ × ℕ) ≃ ℕ
ℕ×ℕ≃ℕ = {!!}

map-ℕ-to-ℕ×ℕ : ℕ → ℕ × ℕ
map-ℕ-to-ℕ×ℕ = {!!}

is-equiv-map-ℕ-to-ℕ×ℕ : is-equiv map-ℕ-to-ℕ×ℕ
is-equiv-map-ℕ-to-ℕ×ℕ = {!!}
```

### The iterated coproduct `ℕ × ℕ × ... × ℕ` is equivalent to `ℕ` for any n

```agda
equiv-iterated-product-ℕ :
  (n : ℕ) → (iterate n (_×_ ℕ) ℕ) ≃ ℕ
equiv-iterated-product-ℕ zero-ℕ = {!!}
equiv-iterated-product-ℕ (succ-ℕ n) = {!!}
```

### The coproduct `(Fin n) + ℕ` is equivalent to `N` for any standard finite `Fin n`

```agda
equiv-coprod-Fin-ℕ : (n : ℕ) → ((Fin n) + ℕ) ≃ ℕ
equiv-coprod-Fin-ℕ zero-ℕ = {!!}
equiv-coprod-Fin-ℕ (succ-ℕ n) = {!!}
```

### The product `(Fin n) × ℕ` is equivalent to `N` for any standard finite `Fin n` where n is nonzero

```agda
equiv-prod-Fin-ℕ : (n : ℕ) → ((Fin (succ-ℕ n)) × ℕ) ≃ ℕ
equiv-prod-Fin-ℕ zero-ℕ = {!!}
equiv-prod-Fin-ℕ (succ-ℕ n) = {!!}
```

### The integers `ℤ` is equivalent to `ℕ`

```agda
ℤ≃ℕ : ℤ ≃ ℕ
ℤ≃ℕ = {!!}

map-ℕ-to-ℤ : ℕ → ℤ
map-ℕ-to-ℤ = {!!}

is-equiv-map-ℕ-to-ℤ : is-equiv map-ℕ-to-ℤ
is-equiv-map-ℕ-to-ℤ = {!!}
```
