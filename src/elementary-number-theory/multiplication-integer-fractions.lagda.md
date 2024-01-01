# Multiplication on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

**Multiplication on integer fractions** is an extension of the
[multiplicative operation](elementary-number-theory.multiplication-integers.md)
on the [integers](elementary-number-theory.integers.md) to
[integer fractions](elementary-number-theory.integer-fractions.md). Note that
the basic properties of multiplication on integer fraction only hold up to
fraction similarity.

## Definition

```agda
mul-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
pr1 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos)) = {!!}
pr1 (pr2 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) = {!!}
pr2 (pr2 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) = {!!}

mul-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
mul-fraction-ℤ' x y = {!!}

infixl 40 _*fraction-ℤ_
_*fraction-ℤ_ = {!!}

ap-mul-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x *fraction-ℤ y ＝ x' *fraction-ℤ y'
ap-mul-fraction-ℤ = {!!}
```

## Properties

### Multiplication respects the similarity relation

```agda
sim-fraction-mul-fraction-ℤ :
  {x x' y y' : fraction-ℤ} →
  sim-fraction-ℤ x x' →
  sim-fraction-ℤ y y' →
  sim-fraction-ℤ (x *fraction-ℤ y) (x' *fraction-ℤ y')
sim-fraction-mul-fraction-ℤ
  {(nx , dx , dxp)} {(nx' , dx' , dx'p)}
  {(ny , dy , dyp)} {(ny' , dy' , dy'p)} p q = {!!}
```

### Unit laws

```agda
left-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ one-fraction-ℤ k) k
left-unit-law-mul-fraction-ℤ = {!!}

right-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ k one-fraction-ℤ) k
right-unit-law-mul-fraction-ℤ = {!!}
```

### Multiplication is associative

```agda
associative-mul-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    (mul-fraction-ℤ (mul-fraction-ℤ x y) z)
    (mul-fraction-ℤ x (mul-fraction-ℤ y z))
associative-mul-fraction-ℤ = {!!}
```

### Multiplication is commutative

```agda
commutative-mul-fraction-ℤ :
  (x y : fraction-ℤ) → sim-fraction-ℤ (x *fraction-ℤ y) (y *fraction-ℤ x)
commutative-mul-fraction-ℤ = {!!}
```
