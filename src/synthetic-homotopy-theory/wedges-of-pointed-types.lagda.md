# Wedges of pointed types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
```

</details>

## Idea

The **wedge** or **wedge sum** of two
[pointed types](structured-types.pointed-types.md) `a : A` and `b : B` is
defined by the following
[pointed pushout](synthetic-homotopy-theory.pushouts-of-pointed-types.md):

```text
  unit ------> A
    |          |
    |          |
    v        ⌜ v
    B -----> A ∨∗ B,
```

and is thus canonically pointed at the identified image of `a` and `b`.

## Definition

```agda
wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
wedge-Pointed-Type = {!!}

infixr 10 _∨∗_
_∨∗_ = {!!}

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-wedge-Pointed-Type : A →∗ (A ∨∗ B)
  inl-wedge-Pointed-Type = {!!}

  map-inl-wedge-Pointed-Type :
    type-Pointed-Type A → type-Pointed-Type (A ∨∗ B)
  map-inl-wedge-Pointed-Type = {!!}

  inr-wedge-Pointed-Type : B →∗ A ∨∗ B
  inr-wedge-Pointed-Type = {!!}

  map-inr-wedge-Pointed-Type :
    type-Pointed-Type B → type-Pointed-Type (A ∨∗ B)
  map-inr-wedge-Pointed-Type = {!!}

indexed-wedge-Pointed-Type :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
indexed-wedge-Pointed-Type = {!!}

⋁∗ = {!!}
```

**Note**: the symbols used for the wedge sum `_∨∗_` are the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`) and
the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`),
not the [latin small letter v](https://codepoints.net/U+0076) `v` or the
[asterisk](https://codepoints.net/U+002A) `*`. The `⋁` symbol used for the
indexed wedge sum, `⋁∗`, is the
[N-ary logical or](https://codepoints.net/U+22C1) (agda-input: `\bigvee`).

## Properties

### The images of the base points `a : A` and `b : B` are identified in `A ∨∗ B`

```agda
glue-wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  map-inl-wedge-Pointed-Type A B (point-Pointed-Type A) ＝
  map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)
glue-wedge-Pointed-Type = {!!}
```

### The inclusion of the wedge sum `A ∨∗ B` into the pointed product `A ×∗ B`

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map induced by the canonical inclusions `A → A ×∗ B ← B`.

Elements of the form `(x, b)` and `(a, y)`, where `b` and `a` are basepoints,
lie in the image of the inclusion of the wedge sum into the pointed product.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  cocone-prod-wedge-Pointed-Type :
    type-cocone-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( A ×∗ B)
  cocone-prod-wedge-Pointed-Type = {!!}

  pointed-map-prod-wedge-Pointed-Type :
    (A ∨∗ B) →∗ (A ×∗ B)
  pointed-map-prod-wedge-Pointed-Type = {!!}

  map-prod-wedge-Pointed-Type :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ×∗ B)
  map-prod-wedge-Pointed-Type = {!!}

  compute-inl-prod-wedge-Pointed-Type :
    ( x : type-Pointed-Type A) →
    ( map-prod-wedge-Pointed-Type (map-inl-wedge-Pointed-Type A B x)) ＝
    ( x , point-Pointed-Type B)
  compute-inl-prod-wedge-Pointed-Type = {!!}

  compute-inr-prod-wedge-Pointed-Type :
    ( y : type-Pointed-Type B) →
    ( map-prod-wedge-Pointed-Type (map-inr-wedge-Pointed-Type A B y)) ＝
    ( point-Pointed-Type A , y)
  compute-inr-prod-wedge-Pointed-Type = {!!}
```

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
  for a related construction.
