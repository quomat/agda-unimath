# Powers of loops

```agda
module synthetic-homotopy-theory.powers-of-loops where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.iterating-functions
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **`n`-th power of a [loop](synthetic-homotopy-theory.loop-spaces.md)** `ω`
in a type `A` is defined by [iterated](foundation.iterating-functions.md)
[concatenation](foundation.identity-types.md) of `ω` with itself.

## Definitions

### Powers of loops by natural numbers

```agda
power-nat-Ω :
  {l : Level} → ℕ → (A : Pointed-Type l) → type-Ω A → type-Ω A
power-nat-Ω = {!!}
```

### Powers of loops by integers

```agda
equiv-power-int-Ω :
  {l : Level} → ℤ → (A : Pointed-Type l) → type-Ω A → type-Ω A ≃ type-Ω A
equiv-power-int-Ω = {!!}

power-int-Ω :
  {l : Level} → ℤ → (A : Pointed-Type l) → type-Ω A → type-Ω A
power-int-Ω = {!!}
```

## Properties

### `reflⁿ = {!!}

```agda
power-nat-refl-Ω :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  power-nat-Ω n A refl ＝ refl
power-nat-refl-Ω = {!!}
```

### `ωⁿ⁺¹ = {!!}

```agda
power-nat-succ-Ω :
  {l : Level} (n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (succ-ℕ n) A ω ＝ (power-nat-Ω n A ω ∙ ω)
power-nat-succ-Ω = {!!}

power-nat-succ-Ω' :
  {l : Level} (n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (succ-ℕ n) A ω ＝ (ω ∙ power-nat-Ω n A ω)
power-nat-succ-Ω' = {!!}
```

### `ωᵐ⁺ⁿ ＝ ωᵐ ∙ ωⁿ`

```agda
power-nat-add-Ω :
  {l : Level} (m n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (m +ℕ n) A ω ＝ (power-nat-Ω m A ω ∙ power-nat-Ω n A ω)
power-nat-add-Ω = {!!}
```

### `ωᵐⁿ = {!!}

```agda
power-nat-mul-Ω :
  {l : Level} (m n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (m *ℕ n) A ω ＝ power-nat-Ω m A (power-nat-Ω n A ω)
power-nat-mul-Ω = {!!}

power-nat-mul-Ω' :
  {l : Level} (m n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (m *ℕ n) A ω ＝ power-nat-Ω n A (power-nat-Ω m A ω)
power-nat-mul-Ω' = {!!}
```

### The action on identifications of a function preserves powers

```agda
map-power-nat-Ω :
  {l1 l2 : Level} (n : ℕ) {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B) (ω : type-Ω A) →
  map-Ω f (power-nat-Ω n A ω) ＝ power-nat-Ω n B (map-Ω f ω)
map-power-nat-Ω = {!!}
```
