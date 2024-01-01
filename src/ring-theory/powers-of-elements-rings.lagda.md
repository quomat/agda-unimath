# Powers of elements in rings

```agda
module ring-theory.powers-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.central-elements-rings
open import ring-theory.powers-of-elements-semirings
open import ring-theory.rings
```

</details>

## Idea

The power operation on a ring is the map `n x ↦ xⁿ`, which is defined by
iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Ring : {l : Level} (R : Ring l) → ℕ → type-Ring R → type-Ring R
power-Ring = {!!}
```

## Properties

### `xⁿ⁺¹ = {!!}

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-succ-Ring :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R (succ-ℕ n) x ＝ mul-Ring R (power-Ring R n x) x
  power-succ-Ring = {!!}

  power-succ-Ring' :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R (succ-ℕ n) x ＝ mul-Ring R x (power-Ring R n x)
  power-succ-Ring' = {!!}
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  distributive-power-add-Ring :
    (m n : ℕ) {x : type-Ring R} →
    power-Ring R (m +ℕ n) x ＝
    mul-Ring R (power-Ring R m x) (power-Ring R n x)
  distributive-power-add-Ring = {!!}
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-mul-Ring :
    (m n : ℕ) {x : type-Ring R} →
    power-Ring R (m *ℕ n) x ＝ power-Ring R n (power-Ring R m x)
  power-mul-Ring = {!!}
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-powers-Ring' :
    (n : ℕ) {x y : type-Ring R} →
    ( mul-Ring R x y ＝ mul-Ring R y x) →
    ( mul-Ring R (power-Ring R n x) y) ＝
    ( mul-Ring R y (power-Ring R n x))
  commute-powers-Ring' = {!!}

  commute-powers-Ring :
    (m n : ℕ) {x y : type-Ring R} → mul-Ring R x y ＝ mul-Ring R y x →
    ( mul-Ring R (power-Ring R m x) (power-Ring R n y)) ＝
    ( mul-Ring R (power-Ring R n y) (power-Ring R m x))
  commute-powers-Ring = {!!}
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  distributive-power-mul-Ring :
    (n : ℕ) {x y : type-Ring R} → mul-Ring R x y ＝ mul-Ring R y x →
    power-Ring R n (mul-Ring R x y) ＝
    mul-Ring R (power-Ring R n x) (power-Ring R n y)
  distributive-power-mul-Ring = {!!}
```

### `(-x)ⁿ = {!!}

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-neg-Ring :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R n (neg-Ring R x) ＝
    mul-Ring R (power-Ring R n (neg-one-Ring R)) (power-Ring R n x)
  power-neg-Ring = {!!}

  even-power-neg-Ring :
    (n : ℕ) (x : type-Ring R) →
    is-even-ℕ n → power-Ring R n (neg-Ring R x) ＝ power-Ring R n x
  even-power-neg-Ring = {!!}

  odd-power-neg-Ring :
    (n : ℕ) (x : type-Ring R) →
    is-odd-ℕ n → power-Ring R n (neg-Ring R x) ＝ neg-Ring R (power-Ring R n x)
  odd-power-neg-Ring = {!!}
```
