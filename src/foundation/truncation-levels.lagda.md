# Truncation levels

```agda
module foundation.truncation-levels where

open import foundation-core.truncation-levels public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Definitions

### Inclusions of the natural numbers into the truncation levels

```agda
truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = {!!}
truncation-level-minus-two-ℕ (succ-ℕ n) = {!!}

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ = {!!}

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ = {!!}
```

### Inclusion of the truncation levels into the natural numbers

```agda
nat-succ-succ-𝕋 : 𝕋 → ℕ
nat-succ-succ-𝕋 neg-two-𝕋 = {!!}
nat-succ-succ-𝕋 (succ-𝕋 k) = {!!}
```

### Addition of truncation levels

```agda
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = {!!}
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = {!!}
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 l)) = {!!}
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = {!!}
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 l) = {!!}
add-𝕋 (succ-𝕋 (succ-𝕋 k)) neg-two-𝕋 = {!!}
add-𝕋 (succ-𝕋 (succ-𝕋 k)) (succ-𝕋 l) = {!!}

infixl 35 _+𝕋_
_+𝕋_ = {!!}
```

### Iterated successor functions on truncation levels

Although we can define an addition operation on truncation levels, when it comes
to doing induction on them, it is more natural to speak in terms of an iterated
successor:

```agda
iterated-succ-𝕋 : ℕ → 𝕋 → 𝕋
iterated-succ-𝕋 zero-ℕ x = {!!}
iterated-succ-𝕋 (succ-ℕ n) x = {!!}

iterated-succ-𝕋' : 𝕋 → ℕ → 𝕋
iterated-succ-𝕋' x n = {!!}
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-add-𝕋 : (k : 𝕋) → zero-𝕋 +𝕋 k ＝ k
left-unit-law-add-𝕋 neg-two-𝕋 = {!!}
left-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = {!!}
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) = {!!}
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 k))) = {!!}

right-unit-law-add-𝕋 : (k : 𝕋) → k +𝕋 zero-𝕋 ＝ k
right-unit-law-add-𝕋 neg-two-𝕋 = {!!}
right-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = {!!}
right-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) = {!!}
```

### Successor laws for addition of truncation levels

```agda
left-successor-law-add-𝕋 :
  (n k : 𝕋) →
  (succ-𝕋 (succ-𝕋 (succ-𝕋 n))) +𝕋 k ＝
  succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 n)) k)
left-successor-law-add-𝕋 = {!!}

right-successor-law-add-𝕋 :
  (k n : 𝕋) →
  k +𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 n))) ＝
  succ-𝕋 (k +𝕋 (succ-𝕋 (succ-𝕋 n)))
right-successor-law-add-𝕋 = {!!}
```
