# Powers of elements in monoids

```agda
module group-theory.powers-of-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
```

</details>

## Idea

The **power operation** on a [monoid](group-theory.monoids.md) is the map
`n x ↦ xⁿ`, which is defined by [iteratively](foundation.iterating-functions.md)
multiplying `x` with itself `n` times.

## Definitions

### Powers of elements of monoids

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-Monoid : ℕ → type-Monoid M → type-Monoid M
  power-Monoid zero-ℕ x = {!!}
```

### The predicate of being a power of an element of a monoid

We say that an element `y` **is a power** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`xⁿ ＝ y`.

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-power-of-element-prop-Monoid : (x y : type-Monoid M) → Prop l
  is-power-of-element-prop-Monoid x y = {!!}

  is-power-of-element-Monoid : (x y : type-Monoid M) → UU l
  is-power-of-element-Monoid x y = {!!}

  is-prop-is-power-of-element-Monoid :
    (x y : type-Monoid M) → is-prop (is-power-of-element-Monoid x y)
  is-prop-is-power-of-element-Monoid = {!!}
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-unit-Monoid :
    (n : ℕ) →
    power-Monoid M n (unit-Monoid M) ＝ unit-Monoid M
  power-unit-Monoid = {!!}
```

### `xⁿ⁺¹ = {!!}

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-succ-Monoid :
    (n : ℕ) (x : type-Monoid M) →
    power-Monoid M (succ-ℕ n) x ＝ mul-Monoid M (power-Monoid M n x) x
  power-succ-Monoid = {!!}
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-succ-Monoid' :
    (n : ℕ) (x : type-Monoid M) →
    power-Monoid M (succ-ℕ n) x ＝ mul-Monoid M x (power-Monoid M n x)
  power-succ-Monoid' = {!!}
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  distributive-power-add-Monoid :
    (m n : ℕ) {x : type-Monoid M} →
    power-Monoid M (m +ℕ n) x ＝
    mul-Monoid M (power-Monoid M m x) (power-Monoid M n x)
  distributive-power-add-Monoid = {!!}
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-powers-Monoid' :
    (n : ℕ) {x y : type-Monoid M} →
    ( mul-Monoid M x y ＝ mul-Monoid M y x) →
    ( mul-Monoid M (power-Monoid M n x) y) ＝
    ( mul-Monoid M y (power-Monoid M n x))
  commute-powers-Monoid' = {!!}

  commute-powers-Monoid :
    (m n : ℕ) {x y : type-Monoid M} →
    ( mul-Monoid M x y ＝ mul-Monoid M y x) →
    ( mul-Monoid M
      ( power-Monoid M m x)
      ( power-Monoid M n y)) ＝
    ( mul-Monoid M
      ( power-Monoid M n y)
      ( power-Monoid M m x))
  commute-powers-Monoid = {!!}
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  distributive-power-mul-Monoid :
    (n : ℕ) {x y : type-Monoid M} →
    (H : mul-Monoid M x y ＝ mul-Monoid M y x) →
    power-Monoid M n (mul-Monoid M x y) ＝
    mul-Monoid M (power-Monoid M n x) (power-Monoid M n y)
  distributive-power-mul-Monoid = {!!}
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-mul-Monoid :
    (m n : ℕ) {x : type-Monoid M} →
    power-Monoid M (m *ℕ n) x ＝
    power-Monoid M n (power-Monoid M m x)
  power-mul-Monoid = {!!}
```

### Monoid homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  preserves-powers-hom-Monoid :
    (n : ℕ) (x : type-Monoid M) →
    map-hom-Monoid M N f (power-Monoid M n x) ＝
    power-Monoid N n (map-hom-Monoid M N f x)
  preserves-powers-hom-Monoid = {!!}
```
