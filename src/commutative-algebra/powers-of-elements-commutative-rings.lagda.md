# Powers of elements in commutative rings

```agda
module commutative-algebra.powers-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-rings
```

</details>

## Idea

The **power operation** on a commutative ring is the map `n x ↦ xⁿ`, which is
defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  ℕ → type-Commutative-Ring A → type-Commutative-Ring A
power-Commutative-Ring = {!!}
```

## Properties

### `xⁿ⁺¹ = {!!}

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  power-succ-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    power-Commutative-Ring A (succ-ℕ n) x ＝
    mul-Commutative-Ring A (power-Commutative-Ring A n x) x
  power-succ-Commutative-Ring = {!!}

  power-succ-Commutative-Ring' :
    (n : ℕ) (x : type-Commutative-Ring A) →
    power-Commutative-Ring A (succ-ℕ n) x ＝
    mul-Commutative-Ring A x (power-Commutative-Ring A n x)
  power-succ-Commutative-Ring' = {!!}
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  distributive-power-add-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring A} →
    power-Commutative-Ring A (m +ℕ n) x ＝
    mul-Commutative-Ring A
      ( power-Commutative-Ring A m x)
      ( power-Commutative-Ring A n x)
  distributive-power-add-Commutative-Ring = {!!}
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  power-mul-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring A} →
    power-Commutative-Ring A (m *ℕ n) x ＝
    power-Commutative-Ring A n (power-Commutative-Ring A m x)
  power-mul-Commutative-Ring = {!!}
```

### Powers distribute over multiplication

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  distributive-power-mul-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring A) →
    power-Commutative-Ring A n (mul-Commutative-Ring A x y) ＝
    mul-Commutative-Ring A
      ( power-Commutative-Ring A n x)
      ( power-Commutative-Ring A n y)
  distributive-power-mul-Commutative-Ring = {!!}
```

### `(-x)ⁿ = {!!}

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    power-Commutative-Ring A n (neg-Commutative-Ring A x) ＝
    mul-Commutative-Ring A
      ( power-Commutative-Ring A n (neg-one-Commutative-Ring A))
      ( power-Commutative-Ring A n x)
  power-neg-Commutative-Ring = {!!}

  even-power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    is-even-ℕ n →
    power-Commutative-Ring A n (neg-Commutative-Ring A x) ＝
    power-Commutative-Ring A n x
  even-power-neg-Commutative-Ring = {!!}

  odd-power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    is-odd-ℕ n →
    power-Commutative-Ring A n (neg-Commutative-Ring A x) ＝
    neg-Commutative-Ring A (power-Commutative-Ring A n x)
  odd-power-neg-Commutative-Ring = {!!}
```
