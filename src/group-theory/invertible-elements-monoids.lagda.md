# Invertible elements in monoids

```agda
module group-theory.invertible-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Idea

An element `x : M` in a [monoid](group-theory.monoids.md) `M` is said to be
**left invertible** if there is an element `y : M` such that `yx ＝ e`, and it
is said to be **right invertible** if there is an element `y : M` such that
`xy ＝ e`. The element `x` is said to be **invertible** if it has a **two-sided
inverse**, i.e., if if there is an element `y : M` such that `xy = {!!}
`yx = {!!}
inverses are also called **sections**.

## Definitions

### Right invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-right-inverse-element-Monoid : type-Monoid M → UU l
  is-right-inverse-element-Monoid y = {!!}

  is-right-invertible-element-Monoid : UU l
  is-right-invertible-element-Monoid = {!!}

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  section-is-right-invertible-element-Monoid :
    is-right-invertible-element-Monoid M x → type-Monoid M
  section-is-right-invertible-element-Monoid = {!!}

  is-right-inverse-section-is-right-invertible-element-Monoid :
    (H : is-right-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x
      ( section-is-right-invertible-element-Monoid H)
  is-right-inverse-section-is-right-invertible-element-Monoid = {!!}
```

### Left invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-left-inverse-element-Monoid : type-Monoid M → UU l
  is-left-inverse-element-Monoid y = {!!}

  is-left-invertible-element-Monoid : UU l
  is-left-invertible-element-Monoid = {!!}

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  retraction-is-left-invertible-element-Monoid :
    is-left-invertible-element-Monoid M x → type-Monoid M
  retraction-is-left-invertible-element-Monoid = {!!}

  is-left-inverse-retraction-is-left-invertible-element-Monoid :
    (H : is-left-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x
      ( retraction-is-left-invertible-element-Monoid H)
  is-left-inverse-retraction-is-left-invertible-element-Monoid = {!!}
```

### Invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-inverse-element-Monoid : type-Monoid M → UU l
  is-inverse-element-Monoid y = {!!}

  is-invertible-element-Monoid : UU l
  is-invertible-element-Monoid = {!!}

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M
  inv-is-invertible-element-Monoid = {!!}

  is-right-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-right-inverse-inv-is-invertible-element-Monoid = {!!}

  is-left-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-left-inverse-inv-is-invertible-element-Monoid = {!!}
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (M : Monoid l)
  where

  all-elements-equal-is-invertible-element-Monoid :
    (x : type-Monoid M) → all-elements-equal (is-invertible-element-Monoid M x)
  all-elements-equal-is-invertible-element-Monoid = {!!}

  is-prop-is-invertible-element-Monoid :
    (x : type-Monoid M) → is-prop (is-invertible-element-Monoid M x)
  is-prop-is-invertible-element-Monoid = {!!}

  is-invertible-element-prop-Monoid : type-Monoid M → Prop l
  pr1 (is-invertible-element-prop-Monoid x) = {!!}
```

### Inverses are left/right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-left-invertible-is-invertible-element-Monoid :
    (x : type-Monoid M) →
    is-invertible-element-Monoid M x → is-left-invertible-element-Monoid M x
  is-left-invertible-is-invertible-element-Monoid = {!!}

  is-right-invertible-is-invertible-element-Monoid :
    (x : type-Monoid M) →
    is-invertible-element-Monoid M x → is-right-invertible-element-Monoid M x
  is-right-invertible-is-invertible-element-Monoid = {!!}
```

### The inverse invertible element

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-right-invertible-left-inverse-Monoid :
    (x : type-Monoid M) (lx : is-left-invertible-element-Monoid M x) →
    is-right-invertible-element-Monoid M (pr1 lx)
  is-right-invertible-left-inverse-Monoid = {!!}

  is-left-invertible-right-inverse-Monoid :
    (x : type-Monoid M) (rx : is-right-invertible-element-Monoid M x) →
    is-left-invertible-element-Monoid M (pr1 rx)
  is-left-invertible-right-inverse-Monoid = {!!}

  is-invertible-element-inverse-Monoid :
    (x : type-Monoid M) (x' : is-invertible-element-Monoid M x) →
    is-invertible-element-Monoid M (pr1 x')
  is-invertible-element-inverse-Monoid = {!!}
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-is-right-invertible-element-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (is-right-invertible-element-Monoid M x)
  is-contr-is-right-invertible-element-Monoid = {!!}
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-is-left-invertible-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (is-left-invertible-element-Monoid M x)
  is-contr-is-left-invertible-Monoid = {!!}
```

### The unit of a monoid is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-left-invertible-element-unit-Monoid :
    is-left-invertible-element-Monoid M (unit-Monoid M)
  is-left-invertible-element-unit-Monoid = {!!}

  is-right-invertible-element-unit-Monoid :
    is-right-invertible-element-Monoid M (unit-Monoid M)
  is-right-invertible-element-unit-Monoid = {!!}

  is-invertible-element-unit-Monoid :
    is-invertible-element-Monoid M (unit-Monoid M)
  is-invertible-element-unit-Monoid = {!!}
```

### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-left-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-left-invertible-element-Monoid M x →
    is-left-invertible-element-Monoid M y →
    is-left-invertible-element-Monoid M (mul-Monoid M x y)
  is-left-invertible-element-mul-Monoid = {!!}

  is-right-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-right-invertible-element-Monoid M x →
    is-right-invertible-element-Monoid M y →
    is-right-invertible-element-Monoid M (mul-Monoid M x y)
  is-right-invertible-element-mul-Monoid = {!!}

  is-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid M y →
    is-invertible-element-Monoid M (mul-Monoid M x y)
  is-invertible-element-mul-Monoid = {!!}
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-invertible-element-inv-is-invertible-element-Monoid :
    {x : type-Monoid M} (H : is-invertible-element-Monoid M x) →
    is-invertible-element-Monoid M (inv-is-invertible-element-Monoid M H)
  is-invertible-element-inv-is-invertible-element-Monoid = {!!}
```

### An element is invertible if and only if multiplying by it is an equivalence

**Proof:** Suppose that the map `z ↦ xz` is an equivalence. Then there is a
unique element `y` such that `xy ＝ 1`. Thus we have a right inverse of `x`. To
see that `y` is also a left inverse of `x`, note that the map `z ↦ xz` is
injective by the assumption that it is an equivalence. Therefore it suffices to
show that `x(yx) ＝ x1`. This follows from the following calculation:

```text
  x(yx) ＝ (xy)x ＝ 1x ＝ x ＝ x1.
```

This completes the proof that if `z ↦ xz` is an equivalence, then `x` is
invertible. The converse is straightfoward.

In the following code we give the above proof, as well as the analogous proof
that `x` is invertible if `z ↦ zx` is an equivalence, and the converse of both
statements.

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid :
    is-equiv (mul-Monoid M x) → type-Monoid M
  inv-is-invertible-element-is-equiv-mul-Monoid = {!!}

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid :
    (H : is-equiv (mul-Monoid M x)) →
    mul-Monoid M x (inv-is-invertible-element-is-equiv-mul-Monoid H) ＝
    unit-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid = {!!}

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid :
    (H : is-equiv (mul-Monoid M x)) →
    mul-Monoid M (inv-is-invertible-element-is-equiv-mul-Monoid H) x ＝
    unit-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid = {!!}

  is-invertible-element-is-equiv-mul-Monoid :
    is-equiv (mul-Monoid M x) → is-invertible-element-Monoid M x
  is-invertible-element-is-equiv-mul-Monoid = {!!}

  left-div-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M → type-Monoid M
  left-div-is-invertible-element-Monoid = {!!}

  is-section-left-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    mul-Monoid M x ∘ left-div-is-invertible-element-Monoid H ~ id
  is-section-left-div-is-invertible-element-Monoid = {!!}

  is-retraction-left-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    left-div-is-invertible-element-Monoid H ∘ mul-Monoid M x ~ id
  is-retraction-left-div-is-invertible-element-Monoid = {!!}

  is-equiv-mul-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → is-equiv (mul-Monoid M x)
  is-equiv-mul-is-invertible-element-Monoid = {!!}
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid' :
    is-equiv (mul-Monoid' M x) → type-Monoid M
  inv-is-invertible-element-is-equiv-mul-Monoid' = {!!}

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' :
    (H : is-equiv (mul-Monoid' M x)) →
    mul-Monoid M (inv-is-invertible-element-is-equiv-mul-Monoid' H) x ＝
    unit-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' = {!!}

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' :
    (H : is-equiv (mul-Monoid' M x)) →
    mul-Monoid M x (inv-is-invertible-element-is-equiv-mul-Monoid' H) ＝
    unit-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' = {!!}

  is-invertible-element-is-equiv-mul-Monoid' :
    is-equiv (mul-Monoid' M x) → is-invertible-element-Monoid M x
  is-invertible-element-is-equiv-mul-Monoid' = {!!}

  right-div-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M → type-Monoid M
  right-div-is-invertible-element-Monoid = {!!}

  is-section-right-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    mul-Monoid' M x ∘ right-div-is-invertible-element-Monoid H ~ id
  is-section-right-div-is-invertible-element-Monoid = {!!}

  is-retraction-right-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    right-div-is-invertible-element-Monoid H ∘ mul-Monoid' M x ~ id
  is-retraction-right-div-is-invertible-element-Monoid = {!!}

  is-equiv-mul-is-invertible-element-Monoid' :
    is-invertible-element-Monoid M x → is-equiv (mul-Monoid' M x)
  is-equiv-mul-is-invertible-element-Monoid' = {!!}
```

## See also

- The core of a monoid is defined in
  [`group-theory.cores-monoids`](group-theory.cores-monoids.md).
