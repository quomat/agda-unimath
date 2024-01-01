# Cocones under spans of pointed types

```agda
module synthetic-homotopy-theory.cocones-under-spans-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

A [cocone under a span](synthetic-homotopy-theory.cocones-under-spans.md) of
[pointed types](structured-types.pointed-types.md) is a **pointed cocone** if it
consists of [pointed maps](structured-types.pointed-maps.md) equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) witnessing that the
naturality square
[commutes](structured-types.commuting-squares-of-pointed-maps.md).

The type of pointed cocones under a span of pointed types is again canonically
pointed at the constant cocone, with `refl` as coherence proof.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2}
  {B : Pointed-Type l3}
  (f : S →∗ A) (g : S →∗ B)
  where

  type-cocone-Pointed-Type :
    {l4 : Level} → Pointed-Type l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-cocone-Pointed-Type = {!!}

  cocone-Pointed-Type :
    {l4 : Level} → Pointed-Type l4 → Pointed-Type (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-Pointed-Type = {!!}
```

### Components of a cocone of pointed types

```agda
module _
  {l1 l2 l3 l4 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2}
  {B : Pointed-Type l3} {X : Pointed-Type l4}
  (f : S →∗ A) (g : S →∗ B) (c : type-cocone-Pointed-Type f g X)
  where

  horizontal-pointed-map-cocone-Pointed-Type : A →∗ X
  horizontal-pointed-map-cocone-Pointed-Type = {!!}

  horizontal-map-cocone-Pointed-Type :
    type-Pointed-Type A → type-Pointed-Type X
  horizontal-map-cocone-Pointed-Type = {!!}

  vertical-pointed-map-cocone-Pointed-Type : B →∗ X
  vertical-pointed-map-cocone-Pointed-Type = {!!}

  vertical-map-cocone-Pointed-Type :
    type-Pointed-Type B → type-Pointed-Type X
  vertical-map-cocone-Pointed-Type = {!!}

  coherence-square-cocone-Pointed-Type :
    coherence-square-pointed-maps
      ( g)
      ( f)
      ( vertical-pointed-map-cocone-Pointed-Type)
      ( horizontal-pointed-map-cocone-Pointed-Type)
  coherence-square-cocone-Pointed-Type = {!!}

  cocone-type-cocone-Pointed-Type : cocone (pr1 f) (pr1 g) (pr1 X)
  pr1 cocone-type-cocone-Pointed-Type = {!!}
```

## See also

- [Pushouts of pointed types](synthetic-homotopy-theory.pushouts-of-pointed-types.md)
