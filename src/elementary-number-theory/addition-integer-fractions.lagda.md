# Addition on integer fractions

```agda
module elementary-number-theory.addition-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

We introduce addition on integer fractions and derive its basic properties. Note
that the properties only hold up to fraction similarity.

## Definition

```agda
add-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
add-fraction-ℤ = {!!}
pr1 (pr2 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) = {!!}
pr2 (pr2 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) = {!!}

add-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
add-fraction-ℤ' = {!!}

infixl 35 _+fraction-ℤ_
_+fraction-ℤ_ = {!!}

ap-add-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x +fraction-ℤ y ＝ x' +fraction-ℤ y'
ap-add-fraction-ℤ = {!!}
```

## Properties

### Addition respects the similarity relation

```agda
sim-fraction-add-fraction-ℤ :
  {x x' y y' : fraction-ℤ} →
  sim-fraction-ℤ x x' →
  sim-fraction-ℤ y y' →
  sim-fraction-ℤ (x +fraction-ℤ y) (x' +fraction-ℤ y')
sim-fraction-add-fraction-ℤ = {!!}
```

### Unit laws

```agda
left-unit-law-add-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (zero-fraction-ℤ +fraction-ℤ k) k
left-unit-law-add-fraction-ℤ = {!!}

right-unit-law-add-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (k +fraction-ℤ zero-fraction-ℤ) k
right-unit-law-add-fraction-ℤ = {!!}
```

### Addition is associative

```agda
associative-add-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    ((x +fraction-ℤ y) +fraction-ℤ z)
    (x +fraction-ℤ (y +fraction-ℤ z))
associative-add-fraction-ℤ = {!!}
```

### Addition is commutative

```agda
commutative-add-fraction-ℤ :
  (x y : fraction-ℤ) →
  sim-fraction-ℤ
    (x +fraction-ℤ y)
    (y +fraction-ℤ x)
commutative-add-fraction-ℤ = {!!}
```
