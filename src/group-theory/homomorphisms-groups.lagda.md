# Homomorphisms of groups

```agda
module group-theory.homomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
```

</details>

## Idea

A **group homomorphism** from one [group](group-theory.groups.md) to another is
a [semigroup homomorphism](group-theory.homomorphisms-semigroups.md) between
their underlying [semigroups](group-theory.semigroups.md).

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-mul-Group : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group = {!!}

  preserves-mul-Group' : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group' = {!!}

  is-prop-preserves-mul-Group :
    (f : type-Group G → type-Group H) → is-prop (preserves-mul-Group f)
  is-prop-preserves-mul-Group = {!!}

  preserves-mul-prop-Group : (type-Group G → type-Group H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Group = {!!}

  hom-Group : UU (l1 ⊔ l2)
  hom-Group = {!!}

  map-hom-Group : hom-Group → type-Group G → type-Group H
  map-hom-Group = {!!}

  preserves-mul-hom-Group :
    (f : hom-Group) →
    preserves-mul-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( map-hom-Group f)
  preserves-mul-hom-Group = {!!}
```

### The identity group homomorphism

```agda
id-hom-Group : {l : Level} (G : Group l) → hom-Group G G
id-hom-Group = {!!}
```

### Composition of group homomorphisms

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  (g : hom-Group H K) (f : hom-Group G H)
  where

  comp-hom-Group : hom-Group G K
  comp-hom-Group = {!!}

  map-comp-hom-Group : type-Group G → type-Group K
  map-comp-hom-Group = {!!}

  preserves-mul-comp-hom-Group :
    preserves-mul-Group G K map-comp-hom-Group
  preserves-mul-comp-hom-Group = {!!}
```

## Properties

### Characterization of the identity type of group homomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  htpy-hom-Group : (f g : hom-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-Group = {!!}

  refl-htpy-hom-Group : (f : hom-Group G H) → htpy-hom-Group f f
  refl-htpy-hom-Group = {!!}

  htpy-eq-hom-Group : (f g : hom-Group G H) → Id f g → htpy-hom-Group f g
  htpy-eq-hom-Group = {!!}

  abstract
    is-torsorial-htpy-hom-Group :
      ( f : hom-Group G H) → is-torsorial (htpy-hom-Group f)
    is-torsorial-htpy-hom-Group = {!!}

  abstract
    is-equiv-htpy-eq-hom-Group :
      (f g : hom-Group G H) → is-equiv (htpy-eq-hom-Group f g)
    is-equiv-htpy-eq-hom-Group = {!!}

  extensionality-hom-Group :
    (f g : hom-Group G H) → Id f g ≃ htpy-hom-Group f g
  extensionality-hom-Group = {!!}

  eq-htpy-hom-Group : {f g : hom-Group G H} → htpy-hom-Group f g → Id f g
  eq-htpy-hom-Group = {!!}

  is-set-hom-Group : is-set (hom-Group G H)
  is-set-hom-Group = {!!}

  hom-set-Group : Set (l1 ⊔ l2)
  hom-set-Group = {!!}
```

### Associativity of composition of group homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  where

  associative-comp-hom-Group :
    (h : hom-Group K L) (g : hom-Group H K) (f : hom-Group G H) →
    comp-hom-Group G H L (comp-hom-Group H K L h g) f ＝
    comp-hom-Group G K L h (comp-hom-Group G H K g f)
  associative-comp-hom-Group = {!!}

  inv-associative-comp-hom-Group :
    (h : hom-Group K L) (g : hom-Group H K) (f : hom-Group G H) →
    comp-hom-Group G K L h (comp-hom-Group G H K g f) ＝
    comp-hom-Group G H L (comp-hom-Group H K L h g) f
  inv-associative-comp-hom-Group = {!!}
```

### The left and right unit laws for composition of group homomorphisms

```agda
left-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  Id (comp-hom-Group G H H (id-hom-Group H) f) f
left-unit-law-comp-hom-Group = {!!}

right-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  Id (comp-hom-Group G G H f (id-hom-Group G)) f
right-unit-law-comp-hom-Group = {!!}
```

### Group homomorphisms preserve the unit element

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-unit-Group : (type-Group G → type-Group H) → UU l2
  preserves-unit-Group = {!!}

  abstract
    preserves-unit-hom-Group :
      ( f : hom-Group G H) → preserves-unit-Group (map-hom-Group G H f)
    preserves-unit-hom-Group = {!!}
```

### Group homomorphisms preserve inverses

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-inverses-Group :
    (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-inverses-Group = {!!}

  abstract
    preserves-inv-hom-Group :
      (f : hom-Group G H) → preserves-inverses-Group (map-hom-Group G H f)
    preserves-inv-hom-Group = {!!}
```

### Group homomorphisms preserve all group structure

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  hom-Group' : UU (l1 ⊔ l2)
  hom-Group' = {!!}

  preserves-group-structure-hom-Group :
    hom-Group G H → hom-Group'
  preserves-group-structure-hom-Group = {!!}
```

### Group homomorphisms induce monoid homomorphisms between the underlying monoids

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  hom-monoid-hom-Group : hom-Monoid (monoid-Group G) (monoid-Group H)
  hom-monoid-hom-Group = {!!}
```

### Group homomorphisms preserve left and right division

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-left-div-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (left-div-Group G x y) ＝
    left-div-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-left-div-hom-Group = {!!}

  preserves-right-div-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (right-div-Group G x y) ＝
    right-div-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-right-div-hom-Group = {!!}
```
