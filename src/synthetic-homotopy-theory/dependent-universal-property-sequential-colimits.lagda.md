# The dependent universal property of sequential colimits

```agda
module synthetic-homotopy-theory.dependent-universal-property-sequential-colimits where
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
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, consider a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c` with vertex `X`. The **dependent universal property of sequential colimits**
is the statement that the dependent cocone postcomposition map

```text
dependent-cocone-map-sequential-diagram :
  ((x : X) → P x) → dependent-cocone-sequential-diagram P
```

is an [equivalence](foundation.equivalences.md).

## Definitions

### The dependent universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-universal-property-sequential-colimit : UUω
  dependent-universal-property-sequential-colimit = {!!}
```

### The map induced by the dependent universal property of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) {P : X → UU l3}
  ( dup-c :
    dependent-universal-property-sequential-colimit A c)
  where

  map-dependent-universal-property-sequential-colimit :
    dependent-cocone-sequential-diagram A c P →
    ( x : X) → P x
  map-dependent-universal-property-sequential-colimit = {!!}
```

## Properties

### The mediating map obtained by the dependent universal property is unique

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) {P : X → UU l3}
  ( dup-c :
    dependent-universal-property-sequential-colimit A c)
  ( d : dependent-cocone-sequential-diagram A c P)
  where

  htpy-dependent-cocone-dependent-universal-property-sequential-colimit :
    htpy-dependent-cocone-sequential-diagram A P
      ( dependent-cocone-map-sequential-diagram A c P
        ( map-dependent-universal-property-sequential-colimit A c
          ( dup-c)
          ( d)))
      ( d)
  htpy-dependent-cocone-dependent-universal-property-sequential-colimit = {!!}

  abstract
    uniqueness-dependent-universal-property-sequential-colimit :
      is-contr
        ( Σ ( ( x : X) → P x)
            ( λ h →
              htpy-dependent-cocone-sequential-diagram A P
                ( dependent-cocone-map-sequential-diagram A c P h)
                ( d)))
    uniqueness-dependent-universal-property-sequential-colimit = {!!}
```

### Correspondence between dependent universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the dependent universal property of
sequential colimits if and only if the corresponding cofork has the dependent
universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer :
    ( {l : Level} →
      dependent-universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)) →
    dependent-universal-property-sequential-colimit A c
  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer = {!!}

  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit :
    dependent-universal-property-sequential-colimit A c →
    ( {l : Level} →
      dependent-universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit = {!!}
```

### The non-dependent and dependent universal properties of sequential colimits are logically equivalent

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-dependent-universal-property-sequential-colimit :
    dependent-universal-property-sequential-colimit A c →
    universal-property-sequential-colimit A c
  universal-property-dependent-universal-property-sequential-colimit = {!!}

  dependent-universal-property-universal-property-sequential-colimit :
    universal-property-sequential-colimit A c →
    dependent-universal-property-sequential-colimit A c
  dependent-universal-property-universal-property-sequential-colimit = {!!}
```

### The 3-for-2 property of the dependent universal property of sequential colimits

Given two cocones under a sequential diagram, one of which has the dependent
universal property of sequential colimits, and a map between their vertices, we
prove that the other has the dependent universal property if and only if the map
is an [equivalence](foundation.equivalences.md).

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( h : X → Y)
  ( H :
    htpy-cocone-sequential-diagram A (cocone-map-sequential-diagram A c h) c')
  where

  abstract
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit :
      dependent-universal-property-sequential-colimit A c →
      dependent-universal-property-sequential-colimit A c' →
      is-equiv h
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit = {!!}

    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimit :
      dependent-universal-property-sequential-colimit A c →
      is-equiv h →
      dependent-universal-property-sequential-colimit A c'
    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimit = {!!}

    dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit-is-equiv :
      is-equiv h →
      dependent-universal-property-sequential-colimit A c' →
      dependent-universal-property-sequential-colimit A c
    dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit-is-equiv = {!!}
```
