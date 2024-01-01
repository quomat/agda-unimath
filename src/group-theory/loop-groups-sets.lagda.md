# Concrete automorphism groups on sets

```agda
module group-theory.loop-groups-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-truncated-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.symmetric-groups
```

</details>

## Definitions

```agda
module _
  {l : Level} (X : Set l)
  where

  type-loop-Set : UU (lsuc l)
  type-loop-Set = {!!}

  is-set-type-loop-Set : is-set type-loop-Set
  is-set-type-loop-Set = {!!}

  set-loop-Set : Set (lsuc l)
  set-loop-Set = {!!}

  has-associative-mul-loop-Set : has-associative-mul-Set (set-loop-Set)
  has-associative-mul-loop-Set = {!!}

  loop-semigroup-Set : Semigroup (lsuc l)
  loop-semigroup-Set = {!!}

  is-unital-Semigroup-loop-semigroup-Set :
    is-unital-Semigroup loop-semigroup-Set
  is-unital-Semigroup-loop-semigroup-Set = {!!}

  is-group-loop-semigroup-Set' :
    is-group' loop-semigroup-Set is-unital-Semigroup-loop-semigroup-Set
  is-group-loop-semigroup-Set' = {!!}

  loop-group-Set : Group (lsuc l)
  loop-group-Set = {!!}
```

## Properties

### The symmetry group and the loop group of a set are isomorphic

```agda
module _
  {l : Level}
  where

  map-hom-symmetric-group-loop-group-Set :
    (X Y : Set l) →
    Id (type-Set X) (type-Set Y) → (type-Set Y) ≃ (type-Set X)
  map-hom-symmetric-group-loop-group-Set = {!!}

  map-hom-inv-symmetric-group-loop-group-Set :
    (X Y : Set l) →
    (type-Set X) ≃ (type-Set Y) → Id (type-Set Y) (type-Set X)
  map-hom-inv-symmetric-group-loop-group-Set = {!!}

  commutative-inv-map-hom-symmetric-group-loop-group-Set :
    (X Y : UU l) (p : Id X Y) (sX : is-set X) (sY : is-set Y) →
    Id
      ( map-hom-symmetric-group-loop-group-Set (Y , sY) (X , sX) (inv p))
      ( inv-equiv
        ( map-hom-symmetric-group-loop-group-Set (X , sX) (Y , sY) p))
  commutative-inv-map-hom-symmetric-group-loop-group-Set = {!!}

module _
  {l : Level} (X : Set l)
  where

  hom-symmetric-group-loop-group-Set :
    hom-Group (loop-group-Set X) (symmetric-Group X)
  hom-symmetric-group-loop-group-Set = {!!}

  hom-inv-symmetric-group-loop-group-Set :
    hom-Group (symmetric-Group X) (loop-group-Set X)
  hom-inv-symmetric-group-loop-group-Set = {!!}

  is-section-hom-inv-symmetric-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group X)
        ( loop-group-Set X)
        ( symmetric-Group X)
        ( hom-symmetric-group-loop-group-Set)
        ( hom-inv-symmetric-group-loop-group-Set))
      ( id-hom-Group (symmetric-Group X))
  is-section-hom-inv-symmetric-group-loop-group-Set = {!!}

  is-retraction-hom-inv-symmetric-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( loop-group-Set X)
        ( symmetric-Group X)
        ( loop-group-Set X)
        ( hom-inv-symmetric-group-loop-group-Set)
        ( hom-symmetric-group-loop-group-Set))
      ( id-hom-Group (loop-group-Set X))
  is-retraction-hom-inv-symmetric-group-loop-group-Set = {!!}

  iso-symmetric-group-loop-group-Set :
    iso-Group (loop-group-Set X) (symmetric-Group X)
  iso-symmetric-group-loop-group-Set = {!!}
```

### The abstacted automorphism group and the loop group of a set are isomorphic

```agda
module _
  {l : Level} (X : Set l)
  where

  hom-abstract-automorphism-group-loop-group-Set :
    hom-Group
      ( loop-group-Set X)
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
  hom-abstract-automorphism-group-loop-group-Set = {!!}

  hom-inv-abstract-automorphism-group-loop-group-Set :
    hom-Group
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
      ( loop-group-Set X)
  hom-inv-abstract-automorphism-group-loop-group-Set = {!!}

  is-section-hom-inv-abstract-automorphism-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( group-Concrete-Group
          ( Automorphism-Group (Set-1-Type l) X))
        ( loop-group-Set X)
        ( group-Concrete-Group
          ( Automorphism-Group (Set-1-Type l) X))
        ( hom-abstract-automorphism-group-loop-group-Set)
        ( hom-inv-abstract-automorphism-group-loop-group-Set))
      ( id-hom-Group
        ( group-Concrete-Group
          ( Automorphism-Group (Set-1-Type l) X)))
  is-section-hom-inv-abstract-automorphism-group-loop-group-Set = {!!}

  is-retraction-hom-inv-abstract-automorphism-group-loop-group-Set :
    comp-hom-Group
      ( loop-group-Set X)
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
      ( loop-group-Set X)
      ( hom-inv-abstract-automorphism-group-loop-group-Set)
      ( hom-abstract-automorphism-group-loop-group-Set) ＝
    id-hom-Group (loop-group-Set X)
  is-retraction-hom-inv-abstract-automorphism-group-loop-group-Set = {!!}

  iso-abstract-automorphism-group-loop-group-Set :
    iso-Group
      ( loop-group-Set X)
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
  iso-abstract-automorphism-group-loop-group-Set = {!!}
```

### The loop groups of two equivalent sets are isomorphic

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) (e : type-Set X ≃ type-Set Y)
  where

  iso-loop-group-equiv-Set :
    iso-Group
      ( loop-group-Set X)
      ( loop-group-Set Y)
  iso-loop-group-equiv-Set = {!!}
```
