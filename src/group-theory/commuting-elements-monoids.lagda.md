# Commuting elements of monoids

```agda
module group-theory.commuting-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commuting-elements-semigroups
open import group-theory.monoids
```

</details>

## Idea

Two elements `x` and `y` of a [monoid](group-theory.monoids.md) `G` are said to
**commute** if the equality `xy ＝ yx` holds.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-prop-Monoid : (x y : type-Monoid M) → Prop l
  commute-prop-Monoid = {!!}

  commute-Monoid : (x y : type-Monoid M) → UU l
  commute-Monoid = {!!}

  commute-Monoid' : (x y : type-Monoid M) → UU l
  commute-Monoid' = {!!}

  is-prop-commute-Monoid : (x y : type-Monoid M) → is-prop (commute-Monoid x y)
  is-prop-commute-Monoid = {!!}
```

## Properties

### The relation `commute-Monoid` is reflexive

```agda
module _
  {l : Level} (M : Monoid l)
  where

  refl-commute-Monoid : (x : type-Monoid M) → commute-Monoid M x x
  refl-commute-Monoid = {!!}
```

### The relation `commute-Monoid` is symmetric

```agda
module _
  {l : Level} (M : Monoid l)
  where

  symmetric-commute-Monoid :
    (x y : type-Monoid M) → commute-Monoid M x y → commute-Monoid M y x
  symmetric-commute-Monoid = {!!}
```

### The unit element commutes with every element of the monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-unit-Monoid : (x : type-Monoid M) → commute-Monoid M x (unit-Monoid M)
  commute-unit-Monoid x = {!!}
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  private
    infix 45 _*_
    _*_ = {!!}

  left-swap-commute-Monoid :
    (x y z : type-Monoid M) → commute-Monoid M x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Monoid = {!!}

  right-swap-commute-Monoid :
    (x y z : type-Monoid M) → commute-Monoid M y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Monoid = {!!}
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-mul-Monoid :
    (x y z : type-Monoid M) →
    commute-Monoid M x y → commute-Monoid M x z →
    commute-Monoid M x (mul-Monoid M y z)
  commute-mul-Monoid = {!!}
```
