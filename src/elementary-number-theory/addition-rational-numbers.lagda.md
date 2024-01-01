# Addition on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.addition-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

We introduce addition on the rationals and derive its basic properties.
Properties of addition with respect to inequality are derived in
`inequality-rationals`.

## Definition

```agda
add-ℚ : ℚ → ℚ → ℚ
add-ℚ = {!!}

add-ℚ' : ℚ → ℚ → ℚ
add-ℚ' = {!!}

infixl 35 _+ℚ_
_+ℚ_ = {!!}

ap-add-ℚ :
  {x y x' y' : ℚ} → x ＝ x' → y ＝ y' → x +ℚ y ＝ x' +ℚ y'
ap-add-ℚ = {!!}
```

## Properties

### Unit laws

```agda
left-unit-law-add-ℚ : (x : ℚ) → zero-ℚ +ℚ x ＝ x
left-unit-law-add-ℚ = {!!}

right-unit-law-add-ℚ : (x : ℚ) → x +ℚ zero-ℚ ＝ x
right-unit-law-add-ℚ = {!!}
```

### Addition is associative

```agda
associative-add-ℚ :
  (x y z : ℚ) →
  (x +ℚ y) +ℚ z ＝ x +ℚ (y +ℚ z)
associative-add-ℚ = {!!}
```

### Addition is commutative

```agda
commutative-add-ℚ :
  (x y : ℚ) →
  x +ℚ y ＝ y +ℚ x
commutative-add-ℚ = {!!}
```
