# Intersections of ideals of rings

```agda
module ring-theory.intersections-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets

open import ring-theory.ideals-rings
open import ring-theory.poset-of-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

The **intersection** of two [ideals](ring-theory.ideals-rings.md) of a
[ring](ring-theory.rings.md) `R` consists of the elements contained in both of
them.

## Definitions

### The universal property of intersections of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (A : Ring l1)
  (I : ideal-Ring l2 A)
  (J : ideal-Ring l3 A)
  where

  is-intersection-ideal-Ring :
    {l4 : Level} (K : ideal-Ring l4 A) → UUω
  is-intersection-ideal-Ring = {!!}
```

### Intersections of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : ideal-Ring l2 R) (J : ideal-Ring l3 R)
  where

  subset-intersection-ideal-Ring : subset-Ring (l2 ⊔ l3) R
  subset-intersection-ideal-Ring = {!!}

  contains-zero-intersection-ideal-Ring :
    contains-zero-subset-Ring R subset-intersection-ideal-Ring
  contains-zero-intersection-ideal-Ring = {!!}

  is-closed-under-addition-intersection-ideal-Ring :
    is-closed-under-addition-subset-Ring R
      subset-intersection-ideal-Ring
  is-closed-under-addition-intersection-ideal-Ring = {!!}

  is-closed-under-negatives-intersection-ideal-Ring :
    is-closed-under-negatives-subset-Ring R
      subset-intersection-ideal-Ring
  is-closed-under-negatives-intersection-ideal-Ring = {!!}

  is-closed-under-left-multiplication-intersection-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R
      subset-intersection-ideal-Ring
  is-closed-under-left-multiplication-intersection-ideal-Ring = {!!}

  is-closed-under-right-multiplication-intersection-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R
      subset-intersection-ideal-Ring
  is-closed-under-right-multiplication-intersection-ideal-Ring = {!!}

  is-additive-subgroup-intersection-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-intersection-ideal-Ring
  is-additive-subgroup-intersection-ideal-Ring = {!!}

  is-ideal-intersection-ideal-Ring :
    is-ideal-subset-Ring R subset-intersection-ideal-Ring
  is-ideal-intersection-ideal-Ring = {!!}

  intersection-ideal-Ring : ideal-Ring (l2 ⊔ l3) R
  intersection-ideal-Ring = {!!}

  is-intersection-intersection-ideal-Ring :
    is-intersection-ideal-Ring R I J intersection-ideal-Ring
  is-intersection-intersection-ideal-Ring = {!!}
```
