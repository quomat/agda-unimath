# Commuting elements of semigroups

```agda
module group-theory.commuting-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

Two elements `x` and `y` of a [semigroup](group-theory.semigroups.md) are said
to **commute** if `xy ＝ yx`.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  commute-prop-Semigroup : (x y : type-Semigroup G) → Prop l
  commute-prop-Semigroup = {!!}

  commute-Semigroup : (x y : type-Semigroup G) → UU l
  commute-Semigroup = {!!}

  commute-Semigroup' : (x y : type-Semigroup G) → UU l
  commute-Semigroup' = {!!}

  is-prop-commute-Semigroup :
    (x y : type-Semigroup G) → is-prop (commute-Semigroup x y)
  is-prop-commute-Semigroup = {!!}
```

## Properties

### The relation `commute-Semigroup` is reflexive

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  refl-commute-Semigroup : (x : type-Semigroup G) → commute-Semigroup G x x
  refl-commute-Semigroup = {!!}
```

### The relation `commute-Semigroup` is symmetric

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  symmetric-commute-Semigroup :
    (x y : type-Semigroup G) → commute-Semigroup G x y → commute-Semigroup G y x
  symmetric-commute-Semigroup = {!!}
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  private
    infix 45 _*_
    _*_ = {!!}

  left-swap-commute-Semigroup :
    (x y z : type-Semigroup G) → commute-Semigroup G x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Semigroup = {!!}

  right-swap-commute-Semigroup :
    (x y z : type-Semigroup G) → commute-Semigroup G y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Semigroup = {!!}
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  private
    infix 45 _*_
    _*_ = {!!}

  commute-mul-Semigroup :
    (x y z : type-Semigroup G) →
    commute-Semigroup G x y → commute-Semigroup G x z →
    commute-Semigroup G x (mul-Semigroup G y z)
  commute-mul-Semigroup = {!!}
```
