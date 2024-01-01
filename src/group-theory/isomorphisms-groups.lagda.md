# Isomorphisms of groups

```agda
module group-theory.isomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.category-of-semigroups
open import group-theory.equivalences-semigroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-semigroups
open import group-theory.precategory-of-groups
```

</details>

## Definitions

### The predicate of being an isomorphism of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-iso-Group : UU (l1 ⊔ l2)
  is-iso-Group = {!!}

  is-prop-is-iso-Group : is-prop is-iso-Group
  is-prop-is-iso-Group = {!!}

  is-iso-prop-Group : Prop (l1 ⊔ l2)
  is-iso-prop-Group = {!!}

  hom-inv-is-iso-Group :
    is-iso-Group → hom-Group H G
  hom-inv-is-iso-Group = {!!}

  map-inv-is-iso-Group :
    is-iso-Group → type-Group H → type-Group G
  map-inv-is-iso-Group = {!!}

  is-section-hom-inv-is-iso-Group :
    (U : is-iso-Group) →
    comp-hom-Group H G H f (hom-inv-is-iso-Group U) ＝
    id-hom-Group H
  is-section-hom-inv-is-iso-Group = {!!}

  is-section-map-inv-is-iso-Group :
    (U : is-iso-Group) →
    ( map-hom-Group G H f ∘ map-inv-is-iso-Group U) ~ id
  is-section-map-inv-is-iso-Group = {!!}

  is-retraction-hom-inv-is-iso-Group :
    (U : is-iso-Group) →
    comp-hom-Group G H G (hom-inv-is-iso-Group U) f ＝
    id-hom-Group G
  is-retraction-hom-inv-is-iso-Group = {!!}

  is-retraction-map-inv-is-iso-Group :
    (U : is-iso-Group) →
    ( map-inv-is-iso-Group U ∘ map-hom-Group G H f) ~ id
  is-retraction-map-inv-is-iso-Group = {!!}
```

### The predicate of being an equivalence of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  is-equiv-hom-Group : hom-Group G H → UU (l1 ⊔ l2)
  is-equiv-hom-Group = {!!}

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = {!!}
```

### Group isomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  iso-Group : UU (l1 ⊔ l2)
  iso-Group = {!!}

  hom-iso-Group : iso-Group → hom-Group G H
  hom-iso-Group = {!!}

  map-iso-Group : iso-Group → type-Group G → type-Group H
  map-iso-Group = {!!}

  preserves-mul-iso-Group :
    (f : iso-Group) {x y : type-Group G} →
    map-iso-Group f (mul-Group G x y) ＝
    mul-Group H (map-iso-Group f x) (map-iso-Group f y)
  preserves-mul-iso-Group = {!!}

  is-iso-iso-Group :
    (f : iso-Group) → is-iso-Group G H (hom-iso-Group f)
  is-iso-iso-Group = {!!}

  hom-inv-iso-Group : iso-Group → hom-Group H G
  hom-inv-iso-Group = {!!}

  map-inv-iso-Group : iso-Group → type-Group H → type-Group G
  map-inv-iso-Group = {!!}

  preserves-mul-inv-iso-Group :
    (f : iso-Group) {x y : type-Group H} →
    map-inv-iso-Group f (mul-Group H x y) ＝
    mul-Group G (map-inv-iso-Group f x) (map-inv-iso-Group f y)
  preserves-mul-inv-iso-Group = {!!}

  is-section-hom-inv-iso-Group :
    (f : iso-Group) →
    comp-hom-Group H G H (hom-iso-Group f) (hom-inv-iso-Group f) ＝
    id-hom-Group H
  is-section-hom-inv-iso-Group = {!!}

  is-section-map-inv-iso-Group :
    (f : iso-Group) →
    ( map-iso-Group f ∘ map-inv-iso-Group f) ~ id
  is-section-map-inv-iso-Group = {!!}

  is-retraction-hom-inv-iso-Group :
    (f : iso-Group) →
    comp-hom-Group G H G (hom-inv-iso-Group f) (hom-iso-Group f) ＝
    id-hom-Group G
  is-retraction-hom-inv-iso-Group = {!!}

  is-retraction-map-inv-iso-Group :
    (f : iso-Group) →
    ( map-inv-iso-Group f ∘ map-iso-Group f) ~ id
  is-retraction-map-inv-iso-Group = {!!}

  is-iso-is-equiv-hom-Group :
    (f : hom-Group G H) → is-equiv-hom-Group G H f → is-iso-Group G H f
  is-iso-is-equiv-hom-Group = {!!}

  is-equiv-is-iso-Group :
    (f : hom-Group G H) → is-iso-Group G H f → is-equiv-hom-Group G H f
  is-equiv-is-iso-Group = {!!}

  equiv-iso-equiv-Group : equiv-Group G H ≃ iso-Group
  equiv-iso-equiv-Group = {!!}

  iso-equiv-Group : equiv-Group G H → iso-Group
  iso-equiv-Group = {!!}
```

### The identity isomorphism

```agda
module _
  {l : Level} (G : Group l)
  where

  id-iso-Group : iso-Group G G
  id-iso-Group = {!!}
```

## Properties

### The total space of group isomorphisms from a given group `G` is contractible

```agda
module _
  {l : Level} (G : Group l)
  where

  iso-eq-Group : (H : Group l) → Id G H → iso-Group G H
  iso-eq-Group = {!!}

  abstract
    extensionality-Group' : (H : Group l) → Id G H ≃ iso-Group G H
    extensionality-Group' = {!!}

  abstract
    is-torsorial-iso-Group : is-torsorial (λ (H : Group l) → iso-Group G H)
    is-torsorial-iso-Group = {!!}
```

### Group isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  where

  comp-iso-Group : iso-Group H K → iso-Group G H → iso-Group G K
  comp-iso-Group = {!!}
```

### Group isomorphisms are stable by inversion

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  inv-iso-Group : iso-Group G H → iso-Group H G
  inv-iso-Group = {!!}
```
