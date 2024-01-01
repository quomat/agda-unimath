# Isomorphisms of group actions

```agda
module group-theory.isomorphisms-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.equivalences-group-actions
open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.precategory-of-group-actions
```

</details>

## Definitions

### The predicate of being an isomorphism of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  is-iso-action-Group :
    (f : hom-action-Group G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-action-Group = {!!}

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : hom-action-Group G X Y) (is-iso-f : is-iso-action-Group G X Y f)
  where

  hom-inv-is-iso-action-Group : hom-action-Group G Y X
  hom-inv-is-iso-action-Group = {!!}

  map-hom-inv-is-iso-action-Group :
    type-action-Group G Y → type-action-Group G X
  map-hom-inv-is-iso-action-Group = {!!}

  is-section-hom-inv-is-iso-action-Group :
    ( comp-hom-action-Group G Y X Y f hom-inv-is-iso-action-Group) ＝
    ( id-hom-action-Group G Y)
  is-section-hom-inv-is-iso-action-Group = {!!}

  is-retraction-hom-inv-is-iso-action-Group :
    ( comp-hom-action-Group G X Y X hom-inv-is-iso-action-Group f) ＝
    ( id-hom-action-Group G X)
  is-retraction-hom-inv-is-iso-action-Group = {!!}
```

### The type of isomorphisms of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3)
  where

  iso-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  iso-action-Group = {!!}

  hom-iso-action-Group :
    iso-action-Group → hom-action-Group G X Y
  hom-iso-action-Group = {!!}

  map-iso-action-Group :
    iso-action-Group →
    type-action-Group G X → type-action-Group G Y
  map-iso-action-Group = {!!}

  preserves-action-iso-action-Group :
    (f : iso-action-Group) (g : type-Group G) →
    coherence-square-maps
      ( map-iso-action-Group f)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( map-iso-action-Group f)
  preserves-action-iso-action-Group = {!!}

  hom-inv-iso-action-Group :
    iso-action-Group → hom-action-Group G Y X
  hom-inv-iso-action-Group = {!!}

  map-hom-inv-iso-action-Group :
    iso-action-Group →
    type-action-Group G Y → type-action-Group G X
  map-hom-inv-iso-action-Group = {!!}

  is-section-hom-inv-iso-action-Group :
    (f : iso-action-Group) →
    ( comp-hom-action-Group G Y X Y
      ( hom-iso-action-Group f)
      ( hom-inv-iso-action-Group f)) ＝
    ( id-hom-action-Group G Y)
  is-section-hom-inv-iso-action-Group = {!!}

  is-retraction-hom-inv-iso-action-Group :
    (f : iso-action-Group) →
    ( comp-hom-action-Group G X Y X
      ( hom-inv-iso-action-Group f)
      ( hom-iso-action-Group f)) ＝
    ( id-hom-action-Group G X)
  is-retraction-hom-inv-iso-action-Group = {!!}

  is-iso-iso-action-Group :
    (f : iso-action-Group) → is-iso-action-Group G X Y (hom-iso-action-Group f)
  is-iso-iso-action-Group = {!!}
```

## Properties

### Isomorphisms of group actions are equivalent to equivalences of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : hom-action-Group G X Y)
  where

  is-equiv-hom-is-iso-action-Group :
    is-iso-action-Group G X Y f → is-equiv-hom-action-Group G X Y f
  is-equiv-hom-is-iso-action-Group = {!!}

  is-iso-is-equiv-hom-action-Group :
    is-equiv-hom-action-Group G X Y f → is-iso-action-Group G X Y f
  is-iso-is-equiv-hom-action-Group = {!!}

  is-equiv-is-equiv-hom-is-iso-action-Group :
    is-equiv is-equiv-hom-is-iso-action-Group
  is-equiv-is-equiv-hom-is-iso-action-Group = {!!}

  is-equiv-is-iso-is-equiv-hom-action-Group :
    is-equiv is-iso-is-equiv-hom-action-Group
  is-equiv-is-iso-is-equiv-hom-action-Group = {!!}

  equiv-is-equiv-hom-is-iso-action-Group :
    is-iso-action-Group G X Y f ≃ is-equiv-hom-action-Group G X Y f
  equiv-is-equiv-hom-is-iso-action-Group = {!!}

  equiv-is-iso-is-equiv-hom-action-Group :
    is-equiv-hom-action-Group G X Y f ≃ is-iso-action-Group G X Y f
  equiv-is-iso-is-equiv-hom-action-Group = {!!}

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : iso-action-Group G X Y)
  where

  is-equiv-map-iso-action-Group : is-equiv (map-iso-action-Group G X Y f)
  is-equiv-map-iso-action-Group = {!!}

  equiv-iso-action-Group : equiv-action-Group G X Y
  pr1 (pr1 equiv-iso-action-Group) = {!!}

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  equiv-equiv-iso-action-Group :
    iso-action-Group G X Y ≃ equiv-action-Group G X Y
  equiv-equiv-iso-action-Group = {!!}

  equiv-iso-equiv-action-Group :
    equiv-action-Group G X Y ≃ iso-action-Group G X Y
  equiv-iso-equiv-action-Group = {!!}
```

### Isomorphisms characterize equality of `G`-sets

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  is-torsorial-iso-action-Group : is-torsorial (iso-action-Group {l3 = l2} G X)
  is-torsorial-iso-action-Group = {!!}
```
