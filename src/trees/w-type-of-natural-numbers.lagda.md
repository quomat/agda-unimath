# The W-type of natural numbers

```agda
module trees.w-type-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import trees.w-types
```

</details>

## Idea

Since the type of natural numbers is an initial algebra for the polynomial
endofunctor

```text
  X ↦ X + 𝟙,
```

there is an equivalent definition of the natural numbers as a W-type.

## Definition

### The type of natural numbers defined as a W-type

```agda
Nat-𝕎 : UU lzero
Nat-𝕎 = {!!}

zero-Nat-𝕎 : Nat-𝕎
zero-Nat-𝕎 = {!!}

succ-Nat-𝕎 : Nat-𝕎 → Nat-𝕎
succ-Nat-𝕎 x = {!!}
```

## Properties

### The type of natural numbers is equivalent to the W-type Nat-𝕎

```agda
Nat-𝕎-ℕ : ℕ → Nat-𝕎
Nat-𝕎-ℕ zero-ℕ = {!!}
Nat-𝕎-ℕ (succ-ℕ x) = {!!}

ℕ-Nat-𝕎 : Nat-𝕎 → ℕ
ℕ-Nat-𝕎 (tree-𝕎 true α) = {!!}
ℕ-Nat-𝕎 (tree-𝕎 false α) = {!!}

is-section-ℕ-Nat-𝕎 : (Nat-𝕎-ℕ ∘ ℕ-Nat-𝕎) ~ id
is-section-ℕ-Nat-𝕎 (tree-𝕎 true α) = {!!}
is-section-ℕ-Nat-𝕎 (tree-𝕎 false α) = {!!}

is-retraction-ℕ-Nat-𝕎 : (ℕ-Nat-𝕎 ∘ Nat-𝕎-ℕ) ~ id
is-retraction-ℕ-Nat-𝕎 zero-ℕ = {!!}
is-retraction-ℕ-Nat-𝕎 (succ-ℕ x) = {!!}

is-equiv-Nat-𝕎-ℕ : is-equiv Nat-𝕎-ℕ
is-equiv-Nat-𝕎-ℕ = {!!}

equiv-Nat-𝕎-ℕ : ℕ ≃ Nat-𝕎
equiv-Nat-𝕎-ℕ = {!!}

is-equiv-ℕ-Nat-𝕎 : is-equiv ℕ-Nat-𝕎
is-equiv-ℕ-Nat-𝕎 = {!!}

equiv-ℕ-Nat-𝕎 : Nat-𝕎 ≃ ℕ
equiv-ℕ-Nat-𝕎 = {!!}
```
