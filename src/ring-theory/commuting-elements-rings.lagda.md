# Commuting elements of rings

```agda
module ring-theory.commuting-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commuting-elements-monoids

open import ring-theory.rings
```

</details>

## Idea

Two elements `x` and `y` of a [ring](ring-theory.rings.md) `R` are said to
**commute** if `xy ＝ yx`.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-prop-Ring : (x y : type-Ring R) → Prop l
  commute-prop-Ring = {!!}

  commute-Ring : (x y : type-Ring R) → UU l
  commute-Ring = {!!}

  commute-Ring' : (x y : type-Ring R) → UU l
  commute-Ring' = {!!}

  is-prop-commute-Ring : (x y : type-Ring R) → is-prop (commute-Ring x y)
  is-prop-commute-Ring = {!!}
```

## Properties

### The relation `commute-Ring` is reflexive

```agda
module _
  {l : Level} (R : Ring l)
  where

  refl-commute-Ring : (x : type-Ring R) → commute-Ring R x x
  refl-commute-Ring = {!!}
```

### The relation `commute-Ring` is symmetric

```agda
module _
  {l : Level} (R : Ring l)
  where

  symmetric-commute-Ring :
    (x y : type-Ring R) → commute-Ring R x y → commute-Ring R y x
  symmetric-commute-Ring = {!!}
```

### The zero element commutes with every element of the ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-zero-Ring : (x : type-Ring R) → commute-Ring R (zero-Ring R) x
  commute-zero-Ring x = {!!}
```

### The multiplicative unit element commutes with every element of the ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-one-Ring : (x : type-Ring R) → commute-Ring R x (one-Ring R)
  commute-one-Ring = {!!}
```

### If `y` and `z` commute with `x`, then `y + z` commutes with `x`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-add-Ring :
    {x y z : type-Ring R} → commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (add-Ring R y z)
  commute-add-Ring H K = {!!}
```

### If `x` commutes with `y`, then `x` commutes with `-y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-neg-Ring :
    {x y : type-Ring R} → commute-Ring R x y → commute-Ring R x (neg-Ring R y)
  commute-neg-Ring H = {!!}
```

### If `x` commutes with `y`, then `-x` commutes with `-y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-neg-neg-Ring :
    {x y : type-Ring R} → commute-Ring R x y →
    commute-Ring R (neg-Ring R x) (neg-Ring R y)
  commute-neg-neg-Ring H = {!!}
```

### If `x` commutes with `y` and `z`, then `x` commutes with `-y + z` and with `y - z`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-left-subtraction-Ring :
    {x y z : type-Ring R} → commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (left-subtraction-Ring R y z)
  commute-left-subtraction-Ring H K = {!!}

  commute-right-subtraction-Ring :
    {x y z : type-Ring R} → commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (right-subtraction-Ring R y z)
  commute-right-subtraction-Ring H K = {!!}
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (R : Ring l)
  where

  private
    infix 50 _*_
    _*_ = {!!}

  left-swap-commute-Ring :
    (x y z : type-Ring R) → commute-Ring R x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Ring = {!!}

  right-swap-commute-Ring :
    (x y z : type-Ring R) → commute-Ring R y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Ring = {!!}
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-mul-Ring :
    (x y z : type-Ring R) →
    commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (mul-Ring R y z)
  commute-mul-Ring = {!!}
```
