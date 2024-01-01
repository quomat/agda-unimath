# Descent data for families of function types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.morphisms-descent-data-circle
open import synthetic-homotopy-theory.sections-descent-circle
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

Given two families `A, B : 𝕊¹ → U` over the
[circle](synthetic-homotopy-theory.circle.md), the
[descent data](synthetic-homotopy-theory.descent-circle.md) for the family of
function types `λ t → (A t → B t)` is `(X → Y, λ h → f ∘ h ∘ e⁻¹)`, where
`(X, e)` is descent data for `A` and `(Y, f)` is descent data for `B`.

This correspondence allows us to characterize sections of this family as
homomorphisms from `(X, e)` to `(Y, f)`.

## Definitions

### Descent data for families of function types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-descent-data-circle-function-type : S → UU (l2 ⊔ l3)
  family-descent-data-circle-function-type = {!!}

  descent-data-circle-function-type : descent-data-circle (l2 ⊔ l3)
  descent-data-circle-function-type = {!!}
```

## Properties

### Characterization of descent data for families of function types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  eq-descent-data-circle-function-type :
    equiv-descent-data-circle
      ( descent-data-circle-function-type l A B)
      ( descent-data-family-circle
        ( l)
        ( family-descent-data-circle-function-type l A B))
  eq-descent-data-circle-function-type = {!!}

  family-with-descent-data-circle-function-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  family-with-descent-data-circle-function-type = {!!}
```

### Maps between families over the circle are equivalent to homomorphisms between the families' descent data

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  equiv-fixpoint-descent-data-circle-function-type-hom :
    fixpoint-descent-data-circle (descent-data-circle-function-type l A B) ≃
    hom-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B)
  equiv-fixpoint-descent-data-circle-function-type-hom = {!!}

  equiv-descent-data-family-circle-function-type-hom :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ( (x : S) → family-descent-data-circle-function-type l A B x) ≃
    hom-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B)
  equiv-descent-data-family-circle-function-type-hom = {!!}
```
