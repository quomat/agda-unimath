# Isomorphisms of semigroups

```agda
module group-theory.isomorphisms-semigroups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.equivalences-semigroups
open import group-theory.homomorphisms-semigroups
open import group-theory.precategory-of-semigroups
open import group-theory.semigroups
```

</details>

## Idea

Isomorphisms of semigroups are homomorphisms that have a two-sided inverse.

## Definition

### The predicate of being an isomorphism of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H)
  where

  is-iso-Semigroup : UU (l1 ⊔ l2)
  is-iso-Semigroup = {!!}

  hom-inv-is-iso-Semigroup :
    is-iso-Semigroup → hom-Semigroup H G
  hom-inv-is-iso-Semigroup = {!!}

  map-inv-is-iso-Semigroup :
    is-iso-Semigroup → type-Semigroup H → type-Semigroup G
  map-inv-is-iso-Semigroup = {!!}

  is-section-hom-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    comp-hom-Semigroup H G H f (hom-inv-is-iso-Semigroup U) ＝
    id-hom-Semigroup H
  is-section-hom-inv-is-iso-Semigroup = {!!}

  is-section-map-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    ( map-hom-Semigroup G H f ∘ map-inv-is-iso-Semigroup U) ~ id
  is-section-map-inv-is-iso-Semigroup = {!!}

  is-retraction-hom-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    comp-hom-Semigroup G H G (hom-inv-is-iso-Semigroup U) f ＝
    id-hom-Semigroup G
  is-retraction-hom-inv-is-iso-Semigroup = {!!}

  is-retraction-map-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    ( map-inv-is-iso-Semigroup U ∘ map-hom-Semigroup G H f) ~ id
  is-retraction-map-inv-is-iso-Semigroup = {!!}
```

### Isomorphisms of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  iso-Semigroup : UU (l1 ⊔ l2)
  iso-Semigroup = {!!}

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : iso-Semigroup G H)
  where

  hom-iso-Semigroup : hom-Semigroup G H
  hom-iso-Semigroup = {!!}

  map-iso-Semigroup : type-Semigroup G → type-Semigroup H
  map-iso-Semigroup = {!!}

  preserves-mul-iso-Semigroup :
    {x y : type-Semigroup G} →
    map-iso-Semigroup (mul-Semigroup G x y) ＝
    mul-Semigroup H (map-iso-Semigroup x) (map-iso-Semigroup y)
  preserves-mul-iso-Semigroup = {!!}

  is-iso-iso-Semigroup : is-iso-Semigroup G H hom-iso-Semigroup
  is-iso-iso-Semigroup = {!!}

  inv-iso-Semigroup : iso-Semigroup H G
  inv-iso-Semigroup = {!!}

  hom-inv-iso-Semigroup : hom-Semigroup H G
  hom-inv-iso-Semigroup = {!!}

  map-inv-iso-Semigroup : type-Semigroup H → type-Semigroup G
  map-inv-iso-Semigroup = {!!}

  preserves-mul-inv-iso-Semigroup :
    {x y : type-Semigroup H} →
    map-inv-iso-Semigroup (mul-Semigroup H x y) ＝
    mul-Semigroup G (map-inv-iso-Semigroup x) (map-inv-iso-Semigroup y)
  preserves-mul-inv-iso-Semigroup = {!!}

  is-section-hom-inv-iso-Semigroup :
    comp-hom-Semigroup H G H hom-iso-Semigroup hom-inv-iso-Semigroup ＝
    id-hom-Semigroup H
  is-section-hom-inv-iso-Semigroup = {!!}

  is-section-map-inv-iso-Semigroup :
    map-iso-Semigroup ∘ map-inv-iso-Semigroup ~ id
  is-section-map-inv-iso-Semigroup = {!!}

  is-retraction-hom-inv-iso-Semigroup :
    comp-hom-Semigroup G H G hom-inv-iso-Semigroup hom-iso-Semigroup ＝
    id-hom-Semigroup G
  is-retraction-hom-inv-iso-Semigroup = {!!}

  is-retraction-map-inv-iso-Semigroup :
    map-inv-iso-Semigroup ∘ map-iso-Semigroup ~ id
  is-retraction-map-inv-iso-Semigroup = {!!}
```

## Properties

### Being an isomorphism is a property

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-prop-is-iso-Semigroup :
      (f : hom-Semigroup G H) → is-prop (is-iso-Semigroup G H f)
    is-prop-is-iso-Semigroup = {!!}

  is-iso-prop-Semigroup :
    hom-Semigroup G H → Prop (l1 ⊔ l2)
  is-iso-prop-Semigroup = {!!}
```

### The inverse of an equivalence of semigroups preserves the binary operation

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : hom-Semigroup G H)
      ( U : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv U)
    preserves-mul-map-inv-is-equiv-Semigroup = {!!}
```

### A homomorphism of semigroups is an equivalence of semigroups if and only if it is an isomorphism

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-iso-is-equiv-hom-Semigroup :
      (f : hom-Semigroup G H) →
      is-equiv-hom-Semigroup G H f → is-iso-Semigroup G H f
    is-iso-is-equiv-hom-Semigroup = {!!}

  abstract
    is-equiv-is-iso-Semigroup :
      (f : hom-Semigroup G H) →
      is-iso-Semigroup G H f → is-equiv-hom-Semigroup G H f
    is-equiv-is-iso-Semigroup = {!!}

  equiv-iso-equiv-Semigroup : equiv-Semigroup G H ≃ iso-Semigroup G H
  equiv-iso-equiv-Semigroup = {!!}

  iso-equiv-Semigroup : equiv-Semigroup G H → iso-Semigroup G H
  iso-equiv-Semigroup = {!!}
```

### Two semigroups are equal if and only if they are isomorphic

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  is-torsorial-iso-Semigroup :
    is-torsorial (iso-Semigroup G)
  is-torsorial-iso-Semigroup = {!!}

  id-iso-Semigroup : iso-Semigroup G G
  id-iso-Semigroup = {!!}

  iso-eq-Semigroup : (H : Semigroup l) → Id G H → iso-Semigroup G H
  iso-eq-Semigroup = {!!}
```
