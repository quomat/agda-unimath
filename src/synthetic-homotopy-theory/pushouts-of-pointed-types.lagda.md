# Pushouts of pointed types

```agda
module synthetic-homotopy-theory.pushouts-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a span of [pointed maps](structured-types.pointed-maps.md), then the
[pushout](synthetic-homotopy-theory.pushouts.md) is in fact a pushout diagram in
the (wild) category of [pointed types](structured-types.pointed-types.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  pushout-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → Pointed-Type (l1 ⊔ l2 ⊔ l3)
  pr1 (pushout-Pointed-Type f g) = {!!}
```

## Properties

### The pushout of a pointed map along a pointed map is pointed

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  inl-pushout-Pointed-Type :
      (f : S →∗ A) (g : S →∗ B) → A →∗ pushout-Pointed-Type f g
  pr1 (inl-pushout-Pointed-Type f g) = {!!}

  inr-pushout-Pointed-Type :
      (f : S →∗ A) (g : S →∗ B) → B →∗ pushout-Pointed-Type f g
  pr1 (inr-pushout-Pointed-Type f g) = {!!}
```

### The cogap map for pushouts of pointed types

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  map-cogap-Pointed-Type :
    {l4 : Level}
    (f : S →∗ A) (g : S →∗ B) →
    {X : Pointed-Type l4} →
    type-cocone-Pointed-Type f g X →
    type-Pointed-Type (pushout-Pointed-Type f g) → type-Pointed-Type X
  map-cogap-Pointed-Type f g c = {!!}

  cogap-Pointed-Type :
    {l4 : Level}
    (f : S →∗ A) (g : S →∗ B) →
    {X : Pointed-Type l4} →
    type-cocone-Pointed-Type f g X → pushout-Pointed-Type f g →∗ X
  pr1 (cogap-Pointed-Type f g c) = {!!}
```

### Computation with the cogap map for pointed types

```agda
module _
  { l1 l2 l3 l4 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  ( f : S →∗ A) (g : S →∗ B)
  { X : Pointed-Type l4} (c : type-cocone-Pointed-Type f g X)
  where

  compute-inl-cogap-Pointed-Type :
    ( x : type-Pointed-Type A) →
    ( map-cogap-Pointed-Type
      ( f)
      ( g)
      ( c)
      ( map-pointed-map (inl-pushout-Pointed-Type f g) x)) ＝
    ( horizontal-map-cocone-Pointed-Type f g c x)
  compute-inl-cogap-Pointed-Type = {!!}

  compute-inr-cogap-Pointed-Type :
    ( y : type-Pointed-Type B) →
    ( map-cogap-Pointed-Type
      ( f)
      ( g)
      ( c)
      ( map-pointed-map (inr-pushout-Pointed-Type f g) y)) ＝
    ( vertical-map-cocone-Pointed-Type f g c y)
  compute-inr-cogap-Pointed-Type = {!!}
```
