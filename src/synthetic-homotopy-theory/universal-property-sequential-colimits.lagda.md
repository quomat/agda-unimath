# The universal property of sequential colimits

```agda
module synthetic-homotopy-theory.universal-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, consider a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c` with vertex `X`. The **universal property of sequential colimits** is the
statement that the cocone postcomposition map

```text
cocone-map-sequential-diagram : (X → Y) → cocone-sequential-diagram Y
```

is an [equivalence](foundation.equivalences.md).

A sequential colimit `X` may be visualized as a "point in infinity" in the
diagram

```text
     a₀      a₁      a₂     i
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X.
```

## Definitions

### The universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit : UUω
  universal-property-sequential-colimit = {!!}
```

### The map induced by the universal property of sequential colimits

The universal property allows us to construct a map from the colimit by
providing a cocone under the sequential diagram.

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit A c)
  where

  map-universal-property-sequential-colimit :
    cocone-sequential-diagram A Y → (X → Y)
  map-universal-property-sequential-colimit = {!!}
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit A c)
  ( c' : cocone-sequential-diagram A Y)
  where

  htpy-cocone-universal-property-sequential-colimit :
    htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A c
        ( map-universal-property-sequential-colimit A c
          ( up-sequential-colimit)
          ( c')))
      ( c')
  htpy-cocone-universal-property-sequential-colimit = {!!}

  abstract
    uniqueness-map-universal-property-sequential-colimit :
      is-contr
        ( Σ ( X → Y)
            ( λ h →
              htpy-cocone-sequential-diagram A
                ( cocone-map-sequential-diagram A c h)
                ( c')))
    uniqueness-map-universal-property-sequential-colimit = {!!}
```

### Correspondence between universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the universal property of sequential
colimits if and only if the
[corresponding cofork](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
has the universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit-universal-property-coequalizer :
    ( {l : Level} →
      universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)) →
    universal-property-sequential-colimit A c
  universal-property-sequential-colimit-universal-property-coequalizer
    ( up-cofork)
    ( Y) = {!!}

  universal-property-coequalizer-universal-property-sequential-colimit :
    universal-property-sequential-colimit A c →
    ( {l : Level} →
      universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
  universal-property-coequalizer-universal-property-sequential-colimit
    ( up-sequential-colimit)
    ( Y) = {!!}
```

### The 3-for-2 property of the universal property of sequential colimits

Given two cocones under a sequential diagram, one of which has the universal
property of sequential colimits, and a map between their vertices, we prove that
the other has the universal property if and only if the map is an
[equivalence](foundation.equivalences.md).

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( h : X → Y)
  ( H :
    htpy-cocone-sequential-diagram A (cocone-map-sequential-diagram A c h) c')
  where

  inv-triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps'
      ( cocone-map-sequential-diagram A c')
      ( cocone-map-sequential-diagram A c)
      ( precomp h Z)
  inv-triangle-cocone-map-precomp-sequential-diagram Z k = {!!}

  triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram A c')
      ( cocone-map-sequential-diagram A c)
      ( precomp h Z)
  triangle-cocone-map-precomp-sequential-diagram Z = {!!}

  abstract
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit :
      universal-property-sequential-colimit A c →
      universal-property-sequential-colimit A c' →
      is-equiv h
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( up-sequential-colimit') = {!!}

    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit :
      universal-property-sequential-colimit A c →
      is-equiv h →
      universal-property-sequential-colimit A c'
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( is-equiv-h)
      ( Z) = {!!}

    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv :
      is-equiv h →
      universal-property-sequential-colimit A c' →
      universal-property-sequential-colimit A c
    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv
      ( is-equiv-h)
      ( up-sequential-colimit)
      ( Z) = {!!}
```

### Unique uniqueness of of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( up-c : universal-property-sequential-colimit A c)
  ( up-c' : universal-property-sequential-colimit A c')
  where

  abstract
    uniquely-unique-sequential-colimit :
      is-contr
        ( Σ ( X ≃ Y)
            ( λ e →
              htpy-cocone-sequential-diagram A
                ( cocone-map-sequential-diagram A c (map-equiv e))
                ( c')))
    uniquely-unique-sequential-colimit = {!!}
```
