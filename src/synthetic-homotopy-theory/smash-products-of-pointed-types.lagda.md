# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
open import synthetic-homotopy-theory.wedges-of-pointed-types
```

</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `a : A` and `b : B`
we may form their **smash product** as the following
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
 A ∨∗ B ----> A ×∗ B
    |           |
    |           |
    v        ⌜  v
  unit -----> A ∧∗ B
```

where the map `A ∨∗ B → A ×∗ B` is the canonical inclusion
`map-wedge-prod-Pointed-Type` from the
[wedge](synthetic-homotopy-theory.wedges-of-pointed-types.md) into the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

## Definition

```agda
smash-prod-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
smash-prod-Pointed-Type A B = {!!}

infixr 15 _∧∗_
_∧∗_ = {!!}
```

**Note**: The symbols used for the smash product `_∧∗_` are the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`),
and the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input:
`\ast`), not the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
cogap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  type-cocone-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B)) X →
  (A ∧∗ B) →∗ X
cogap-smash-prod-Pointed-Type {A = A} {B} = {!!}

map-cogap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  type-cocone-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))
    ( X) →
  type-Pointed-Type (A ∧∗ B) → type-Pointed-Type X
map-cogap-smash-prod-Pointed-Type c = {!!}
```

## Properties

### The canonical pointed map from the cartesian product to the smash product

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-prod-prod-Pointed-Type : (A ×∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-prod-prod-Pointed-Type = {!!}

  map-smash-prod-prod-Pointed-Type :
    type-Pointed-Type (A ×∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-prod-prod-Pointed-Type = {!!}
```

### Pointed maps into pointed types `A` and `B` induce a pointed map into `A ∧∗ B`

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {S : Pointed-Type l3}
  where

  gap-smash-prod-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ∧∗ B)
  gap-smash-prod-Pointed-Type f g = {!!}

  map-gap-smash-prod-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → type-Pointed-Type S → type-Pointed-Type (A ∧∗ B)
  map-gap-smash-prod-Pointed-Type f g = {!!}
```

### The canonical map from the wedge sum to the smash product identifies all points

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-prod-wedge-Pointed-Type : (A ∨∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-prod-wedge-Pointed-Type = {!!}

  map-smash-prod-wedge-Pointed-Type :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-prod-wedge-Pointed-Type = {!!}

  contraction-map-smash-prod-wedge-Pointed-Type :
    ( x : type-Pointed-Type (A ∨∗ B)) →
    map-smash-prod-wedge-Pointed-Type x ＝
    point-Pointed-Type (A ∧∗ B)
  contraction-map-smash-prod-wedge-Pointed-Type x = {!!}

  coh-contraction-map-smash-prod-wedge-Pointed-Type :
    ( ap
      ( map-smash-prod-wedge-Pointed-Type)
      ( glue-wedge-Pointed-Type A B)) ∙
    ( contraction-map-smash-prod-wedge-Pointed-Type
        ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B))) ＝
    ( contraction-map-smash-prod-wedge-Pointed-Type
      ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
  coh-contraction-map-smash-prod-wedge-Pointed-Type = {!!}
```

### The map from the pointed product to the smash product identifies elements

of the form `(x, b)` and `(a, y)`, where `b` and `a` are the base points of `B`
and `A` respectively.

```agda
module _
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-glue-smash-prod-Pointed-Type :
    ( x : type-Pointed-Type A) →
    map-smash-prod-prod-Pointed-Type A B
      ( x , point-Pointed-Type B) ＝
    map-smash-prod-prod-Pointed-Type A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inl-glue-smash-prod-Pointed-Type x = {!!}

  inr-glue-smash-prod-Pointed-Type :
    ( y : type-Pointed-Type B) →
    map-smash-prod-prod-Pointed-Type A B
      ( point-Pointed-Type A , y) ＝
    map-smash-prod-prod-Pointed-Type A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inr-glue-smash-prod-Pointed-Type y = {!!}

  coh-glue-smash-prod-Pointed-Type :
    inl-glue-smash-prod-Pointed-Type (point-Pointed-Type A) ＝
    inr-glue-smash-prod-Pointed-Type (point-Pointed-Type B)
  coh-glue-smash-prod-Pointed-Type = {!!}
```

### The universal property of the smash product

Fixing a pointed type `B`, the _universal property of the smash product_ states
that the functor `- ∧∗ B` forms the left-adjoint to the functor `B →∗ -` of
[pointed maps](structured-types.pointed-maps.md) with source `B`. In the
language of type theory, this means that we have a pointed equivalence:

```text
  ((A ∧∗ B) →∗ C) ≃∗ (A →∗ B →∗ C).
```

**Note:** The categorical product in the category of pointed types is the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

```agda
map-universal-property-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3) →
  ((A ∧∗ B) →∗ C) → (type-Pointed-Type A) → (B →∗ C)
pr1 (map-universal-property-smash-prod-Pointed-Type A B C f x) y = {!!}
pr2 (map-universal-property-smash-prod-Pointed-Type A B C f x) = {!!}

universal-property-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3) →
  ((A ∧∗ B) →∗ C) → (A →∗ (pointed-map-Pointed-Type B C))
pr1 (universal-property-smash-prod-Pointed-Type A B C f) = {!!}
pr2 (universal-property-smash-prod-Pointed-Type A B C f) = {!!}
```

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
