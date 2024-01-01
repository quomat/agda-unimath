# Homomorphisms of concrete groups

```agda
module group-theory.homomorphisms-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-groups

open import higher-group-theory.homomorphisms-higher-groups
```

</details>

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  where

  hom-Concrete-Group : UU (l1 ⊔ l2)
  hom-Concrete-Group = {!!}

  is-set-hom-Concrete-Group : is-set hom-Concrete-Group
  is-set-hom-Concrete-Group = {!!}

  hom-set-Concrete-Group : Set (l1 ⊔ l2)
  hom-set-Concrete-Group = {!!}

  classifying-map-hom-Concrete-Group :
    hom-Concrete-Group →
    classifying-type-Concrete-Group G → classifying-type-Concrete-Group H
  classifying-map-hom-Concrete-Group = {!!}

  preserves-point-classifying-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    Id
      ( classifying-map-hom-Concrete-Group f (shape-Concrete-Group G))
      ( shape-Concrete-Group H)
  preserves-point-classifying-map-hom-Concrete-Group = {!!}

  map-hom-Concrete-Group :
    hom-Concrete-Group → type-Concrete-Group G → type-Concrete-Group H
  map-hom-Concrete-Group = {!!}

  preserves-unit-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    Id
      ( map-hom-Concrete-Group f (unit-Concrete-Group G))
      ( unit-Concrete-Group H)
  preserves-unit-map-hom-Concrete-Group = {!!}

  preserves-mul-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) {x y : type-Concrete-Group G} →
    Id
      ( map-hom-Concrete-Group f (mul-Concrete-Group G x y))
      ( mul-Concrete-Group H
        ( map-hom-Concrete-Group f x)
        ( map-hom-Concrete-Group f y))
  preserves-mul-map-hom-Concrete-Group = {!!}

  preserves-inv-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) (x : type-Concrete-Group G) →
    Id
      ( map-hom-Concrete-Group f (inv-Concrete-Group G x))
      ( inv-Concrete-Group H (map-hom-Concrete-Group f x))
  preserves-inv-map-hom-Concrete-Group = {!!}

  hom-group-hom-Concrete-Group :
    hom-Concrete-Group →
    hom-Group
      ( group-Concrete-Group G)
      ( group-Concrete-Group H)
  hom-group-hom-Concrete-Group = {!!}
```

### Homotopies of morphisms of concrete groups

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  htpy-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-Concrete-Group = {!!}

  extensionality-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → Id f g ≃ htpy-hom-Concrete-Group g
  extensionality-hom-Concrete-Group = {!!}

  eq-htpy-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → (htpy-hom-Concrete-Group g) → Id f g
  eq-htpy-hom-Concrete-Group = {!!}
```

```agda
id-hom-Concrete-Group :
  {l : Level} (G : Concrete-Group l) → hom-Concrete-Group G G
id-hom-Concrete-Group = {!!}

comp-hom-Concrete-Group :
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3) →
  hom-Concrete-Group H K → hom-Concrete-Group G H → hom-Concrete-Group G K
comp-hom-Concrete-Group = {!!}

associative-comp-hom-Concrete-Group :
  {l1 l2 l3 l4 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (K : Concrete-Group l3) (L : Concrete-Group l4)
  (h : hom-Concrete-Group K L) (g : hom-Concrete-Group H K)
  (f : hom-Concrete-Group G H) →
  htpy-hom-Concrete-Group G L
    ( comp-hom-Concrete-Group G H L (comp-hom-Concrete-Group H K L h g) f)
    ( comp-hom-Concrete-Group G K L h (comp-hom-Concrete-Group G H K g f))
associative-comp-hom-Concrete-Group = {!!}

inv-associative-comp-hom-Concrete-Group :
  {l1 l2 l3 l4 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (K : Concrete-Group l3) (L : Concrete-Group l4)
  (h : hom-Concrete-Group K L) (g : hom-Concrete-Group H K)
  (f : hom-Concrete-Group G H) →
  htpy-hom-Concrete-Group G L
    ( comp-hom-Concrete-Group G K L h (comp-hom-Concrete-Group G H K g f))
    ( comp-hom-Concrete-Group G H L (comp-hom-Concrete-Group H K L h g) f)
inv-associative-comp-hom-Concrete-Group = {!!}

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  where

  left-unit-law-comp-hom-Concrete-Group :
    (f : hom-Concrete-Group G H) →
    htpy-hom-Concrete-Group G H
      ( comp-hom-Concrete-Group G H H (id-hom-Concrete-Group H) f)
      ( f)
  left-unit-law-comp-hom-Concrete-Group = {!!}

  right-unit-law-comp-hom-Concrete-Group :
    (f : hom-Concrete-Group G H) →
    htpy-hom-Concrete-Group G H
      ( comp-hom-Concrete-Group G G H f (id-hom-Concrete-Group G))
      ( f)
  right-unit-law-comp-hom-Concrete-Group = {!!}
```
