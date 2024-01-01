# Symmetric groups

```agda
module group-theory.symmetric-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.monoids
open import group-theory.opposite-groups
open import group-theory.semigroups
open import group-theory.symmetric-concrete-groups
```

</details>

## Definitions

```agda
set-symmetric-Group : {l : Level} (X : Set l) → Set l
set-symmetric-Group X = {!!}

type-symmetric-Group : {l : Level} (X : Set l) → UU l
type-symmetric-Group X = {!!}

is-set-type-symmetric-Group :
  {l : Level} (X : Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group = {!!}

has-associative-mul-aut-Set :
  {l : Level} (X : Set l) → has-associative-mul-Set (Aut-Set X)
has-associative-mul-aut-Set = {!!}

symmetric-Semigroup :
  {l : Level} (X : Set l) → Semigroup l
symmetric-Semigroup = {!!}

is-unital-Semigroup-symmetric-Semigroup :
  {l : Level} (X : Set l) → is-unital-Semigroup (symmetric-Semigroup X)
is-unital-Semigroup-symmetric-Semigroup = {!!}

is-group-symmetric-Semigroup' :
  {l : Level} (X : Set l) →
  is-group' (symmetric-Semigroup X) (is-unital-Semigroup-symmetric-Semigroup X)
is-group-symmetric-Semigroup' = {!!}

symmetric-Group :
  {l : Level} → Set l → Group l
symmetric-Group = {!!}
```

## Properties

### If two sets are equivalent, then their symmetric groups are isomorphic

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) (e : type-Set X ≃ type-Set Y)
  where

  hom-symmetric-group-equiv-Set :
    hom-Group (symmetric-Group X) (symmetric-Group Y)
  hom-symmetric-group-equiv-Set = {!!}

  hom-inv-symmetric-group-equiv-Set :
    hom-Group (symmetric-Group Y) (symmetric-Group X)
  hom-inv-symmetric-group-equiv-Set = {!!}

  is-section-hom-inv-symmetric-group-equiv-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group Y)
        ( symmetric-Group X)
        ( symmetric-Group Y)
        ( hom-symmetric-group-equiv-Set)
        ( hom-inv-symmetric-group-equiv-Set))
      ( id-hom-Group (symmetric-Group Y))
  is-section-hom-inv-symmetric-group-equiv-Set = {!!}

  is-retraction-hom-inv-symmetric-group-equiv-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group X)
        ( symmetric-Group Y)
        ( symmetric-Group X)
        ( hom-inv-symmetric-group-equiv-Set)
        ( hom-symmetric-group-equiv-Set))
      ( id-hom-Group (symmetric-Group X))
  is-retraction-hom-inv-symmetric-group-equiv-Set = {!!}

  iso-symmetric-group-equiv-Set :
    iso-Group (symmetric-Group X) (symmetric-Group Y)
  iso-symmetric-group-equiv-Set = {!!}
```

### The symmetric group and the abstract automorphism group of a set are isomorphic

```agda
module _
  {l1 : Level} (A : Set l1)
  where

  equiv-compute-symmetric-Concrete-Group :
    type-Concrete-Group (symmetric-Concrete-Group A) ≃ type-symmetric-Group A
  equiv-compute-symmetric-Concrete-Group = {!!}

  map-compute-symmetric-Concrete-Group :
    type-Concrete-Group (symmetric-Concrete-Group A) → type-symmetric-Group A
  map-compute-symmetric-Concrete-Group = {!!}

  preserves-mul-compute-symmetric-Concrete-Group :
    preserves-mul-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
      ( map-compute-symmetric-Concrete-Group)
  preserves-mul-compute-symmetric-Concrete-Group = {!!}

  equiv-group-compute-symmetric-Concrete-Group :
    equiv-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
  equiv-group-compute-symmetric-Concrete-Group = {!!}

  compute-symmetric-Concrete-Group' :
    iso-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
  compute-symmetric-Concrete-Group' = {!!}

  compute-symmetric-Concrete-Group :
    iso-Group
      ( group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
  compute-symmetric-Concrete-Group = {!!}
```
