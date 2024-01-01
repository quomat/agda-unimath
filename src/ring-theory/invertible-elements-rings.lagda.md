# Invertible elements in rings

```agda
module ring-theory.invertible-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids

open import ring-theory.rings
```

</details>

## Idea

**Invertible elements** in a [ring](ring-theory.rings.md) are elements that have
a two-sided multiplicative inverse. Such elements are also called the
**(multiplicative) units** of the ring.

The [set](foundation.sets.md) of units of any ring forms a
[group](group-theory.groups.md), called the
[group of units](ring-theory.groups-of-units-rings.md). The group of units of a
ring is constructed in
[`ring-theory.groups-of-units-rings`](ring-theory.groups-of-units-rings.md).

## Definitions

### Left invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-inverse-element-Ring : (x y : type-Ring R) → UU l
  is-left-inverse-element-Ring = {!!}

  is-left-invertible-element-Ring : type-Ring R → UU l
  is-left-invertible-element-Ring = {!!}

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  retraction-is-left-invertible-element-Ring :
    is-left-invertible-element-Ring R x → type-Ring R
  retraction-is-left-invertible-element-Ring = {!!}

  is-left-inverse-retraction-is-left-invertible-element-Ring :
    (H : is-left-invertible-element-Ring R x) →
    is-left-inverse-element-Ring R x
      ( retraction-is-left-invertible-element-Ring H)
  is-left-inverse-retraction-is-left-invertible-element-Ring = {!!}
```

### Right invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-right-inverse-element-Ring : (x y : type-Ring R) → UU l
  is-right-inverse-element-Ring = {!!}

  is-right-invertible-element-Ring : type-Ring R → UU l
  is-right-invertible-element-Ring = {!!}

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  section-is-right-invertible-element-Ring :
    is-right-invertible-element-Ring R x → type-Ring R
  section-is-right-invertible-element-Ring = {!!}

  is-right-inverse-section-is-right-invertible-element-Ring :
    (H : is-right-invertible-element-Ring R x) →
    is-right-inverse-element-Ring R x
      ( section-is-right-invertible-element-Ring H)
  is-right-inverse-section-is-right-invertible-element-Ring = {!!}
```

### Invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l) (x : type-Ring R)
  where

  is-inverse-element-Ring : type-Ring R → UU l
  is-inverse-element-Ring = {!!}

  is-invertible-element-Ring : UU l
  is-invertible-element-Ring = {!!}

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  inv-is-invertible-element-Ring :
    is-invertible-element-Ring R x → type-Ring R
  inv-is-invertible-element-Ring = {!!}

  is-right-inverse-inv-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    is-right-inverse-element-Ring R x (inv-is-invertible-element-Ring H)
  is-right-inverse-inv-is-invertible-element-Ring = {!!}

  is-left-inverse-inv-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    is-left-inverse-element-Ring R x (inv-is-invertible-element-Ring H)
  is-left-inverse-inv-is-invertible-element-Ring = {!!}
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-prop-is-invertible-element-Ring :
    (x : type-Ring R) → is-prop (is-invertible-element-Ring R x)
  is-prop-is-invertible-element-Ring = {!!}

  is-invertible-element-prop-Ring : type-Ring R → Prop l
  is-invertible-element-prop-Ring = {!!}
```

### Inverses are left/right inverses

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-invertible-is-invertible-element-Ring :
    (x : type-Ring R) →
    is-invertible-element-Ring R x → is-left-invertible-element-Ring R x
  is-left-invertible-is-invertible-element-Ring = {!!}

  is-right-invertible-is-invertible-element-Ring :
    (x : type-Ring R) →
    is-invertible-element-Ring R x → is-right-invertible-element-Ring R x
  is-right-invertible-is-invertible-element-Ring = {!!}
```

### The inverse invertible element

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-right-invertible-left-inverse-Ring :
    (x : type-Ring R) (H : is-left-invertible-element-Ring R x) →
    is-right-invertible-element-Ring R
      ( retraction-is-left-invertible-element-Ring R H)
  is-right-invertible-left-inverse-Ring = {!!}

  is-left-invertible-right-inverse-Ring :
    (x : type-Ring R) (H : is-right-invertible-element-Ring R x) →
    is-left-invertible-element-Ring R
      ( section-is-right-invertible-element-Ring R H)
  is-left-invertible-right-inverse-Ring = {!!}

  is-invertible-element-inverse-Ring :
    (x : type-Ring R) (H : is-invertible-element-Ring R x) →
    is-invertible-element-Ring R
      ( inv-is-invertible-element-Ring R H)
  is-invertible-element-inverse-Ring = {!!}
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-contr-is-right-invertible-element-Ring :
    (x : type-Ring R) → is-invertible-element-Ring R x →
    is-contr (is-right-invertible-element-Ring R x)
  is-contr-is-right-invertible-element-Ring = {!!}
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-contr-is-left-invertible-Ring :
    (x : type-Ring R) → is-invertible-element-Ring R x →
    is-contr (is-left-invertible-element-Ring R x)
  is-contr-is-left-invertible-Ring = {!!}
```

### The unit of a monoid is invertible

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-invertible-element-one-Ring :
    is-left-invertible-element-Ring R (one-Ring R)
  is-left-invertible-element-one-Ring = {!!}

  is-right-invertible-element-one-Ring :
    is-right-invertible-element-Ring R (one-Ring R)
  is-right-invertible-element-one-Ring = {!!}

  is-invertible-element-one-Ring :
    is-invertible-element-Ring R (one-Ring R)
  is-invertible-element-one-Ring = {!!}
```

### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-invertible-element-mul-Ring :
    (x y : type-Ring R) →
    is-left-invertible-element-Ring R x →
    is-left-invertible-element-Ring R y →
    is-left-invertible-element-Ring R (mul-Ring R x y)
  is-left-invertible-element-mul-Ring = {!!}

  is-right-invertible-element-mul-Ring :
    (x y : type-Ring R) →
    is-right-invertible-element-Ring R x →
    is-right-invertible-element-Ring R y →
    is-right-invertible-element-Ring R (mul-Ring R x y)
  is-right-invertible-element-mul-Ring = {!!}

  is-invertible-element-mul-Ring :
    (x y : type-Ring R) →
    is-invertible-element-Ring R x →
    is-invertible-element-Ring R y →
    is-invertible-element-Ring R (mul-Ring R x y)
  is-invertible-element-mul-Ring = {!!}
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-invertible-element-inv-is-invertible-element-Ring :
    {x : type-Ring R} (H : is-invertible-element-Ring R x) →
    is-invertible-element-Ring R (inv-is-invertible-element-Ring R H)
  is-invertible-element-inv-is-invertible-element-Ring = {!!}
```

### An element is invertible if and only if multiplying by it is an equivalence

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  inv-is-invertible-element-is-equiv-mul-Ring :
    is-equiv (mul-Ring R x) → type-Ring R
  inv-is-invertible-element-is-equiv-mul-Ring = {!!}

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring :
    (H : is-equiv (mul-Ring R x)) →
    mul-Ring R x (inv-is-invertible-element-is-equiv-mul-Ring H) ＝
    one-Ring R
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring = {!!}

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring :
    (H : is-equiv (mul-Ring R x)) →
    mul-Ring R (inv-is-invertible-element-is-equiv-mul-Ring H) x ＝
    one-Ring R
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring = {!!}

  is-invertible-element-is-equiv-mul-Ring :
    is-equiv (mul-Ring R x) → is-invertible-element-Ring R x
  is-invertible-element-is-equiv-mul-Ring = {!!}

  left-div-is-invertible-element-Ring :
    is-invertible-element-Ring R x → type-Ring R → type-Ring R
  left-div-is-invertible-element-Ring = {!!}

  is-section-left-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    mul-Ring R x ∘ left-div-is-invertible-element-Ring H ~ id
  is-section-left-div-is-invertible-element-Ring = {!!}

  is-retraction-left-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    left-div-is-invertible-element-Ring H ∘ mul-Ring R x ~ id
  is-retraction-left-div-is-invertible-element-Ring = {!!}

  is-equiv-mul-is-invertible-element-Ring :
    is-invertible-element-Ring R x → is-equiv (mul-Ring R x)
  is-equiv-mul-is-invertible-element-Ring = {!!}
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  inv-is-invertible-element-is-equiv-mul-Ring' :
    is-equiv (mul-Ring' R x) → type-Ring R
  inv-is-invertible-element-is-equiv-mul-Ring' = {!!}

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring' :
    (H : is-equiv (mul-Ring' R x)) →
    mul-Ring R (inv-is-invertible-element-is-equiv-mul-Ring' H) x ＝
    one-Ring R
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring' = {!!}

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring' :
    (H : is-equiv (mul-Ring' R x)) →
    mul-Ring R x (inv-is-invertible-element-is-equiv-mul-Ring' H) ＝
    one-Ring R
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring' = {!!}

  is-invertible-element-is-equiv-mul-Ring' :
    is-equiv (mul-Ring' R x) → is-invertible-element-Ring R x
  is-invertible-element-is-equiv-mul-Ring' = {!!}

  right-div-is-invertible-element-Ring :
    is-invertible-element-Ring R x → type-Ring R → type-Ring R
  right-div-is-invertible-element-Ring = {!!}

  is-section-right-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    mul-Ring' R x ∘ right-div-is-invertible-element-Ring H ~ id
  is-section-right-div-is-invertible-element-Ring = {!!}

  is-retraction-right-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    right-div-is-invertible-element-Ring H ∘ mul-Ring' R x ~ id
  is-retraction-right-div-is-invertible-element-Ring = {!!}

  is-equiv-mul-is-invertible-element-Ring' :
    is-invertible-element-Ring R x → is-equiv (mul-Ring' R x)
  is-equiv-mul-is-invertible-element-Ring' = {!!}
```

## See also

- The group of multiplicative units of a ring is defined in
  [`ring-theory.groups-of-units-rings`](ring-theory.groups-of-units-rings.md).
