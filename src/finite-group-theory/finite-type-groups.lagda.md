# The group of n-element types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.finite-type-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.truncated-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

### Definition

```agda
UU-Fin-Group : (l : Level) (n : ℕ) → Concrete-Group (lsuc l)
pr1 (pr1 (pr1 (UU-Fin-Group l n))) = {!!}
pr2 (pr1 (pr1 (UU-Fin-Group l n))) = {!!}
pr2 (pr1 (UU-Fin-Group l n)) = {!!}
pr2 (UU-Fin-Group l n) = {!!}
```

### Properties

```agda
module _
  (l : Level) (n : ℕ)
  where

  hom-loop-group-fin-UU-Fin-Group :
    hom-Group
      ( group-Concrete-Group (UU-Fin-Group l n))
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 hom-loop-group-fin-UU-Fin-Group p = {!!}

  hom-inv-loop-group-fin-UU-Fin-Group :
    hom-Group
      ( loop-group-Set (raise-Set l (Fin-Set n)))
      ( group-Concrete-Group (UU-Fin-Group l n))
  pr1 hom-inv-loop-group-fin-UU-Fin-Group p = {!!}

  is-section-hom-inv-loop-group-fin-UU-Fin-Group :
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( group-Concrete-Group (UU-Fin-Group l n))
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( hom-loop-group-fin-UU-Fin-Group)
        ( hom-inv-loop-group-fin-UU-Fin-Group))
      ( id-hom-Group (loop-group-Set (raise-Set l (Fin-Set n))))
  is-section-hom-inv-loop-group-fin-UU-Fin-Group = {!!}

  is-retraction-hom-inv-loop-group-fin-UU-Fin-Group :
    Id
      ( comp-hom-Group
        ( group-Concrete-Group (UU-Fin-Group l n))
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( group-Concrete-Group (UU-Fin-Group l n))
        ( hom-inv-loop-group-fin-UU-Fin-Group)
        ( hom-loop-group-fin-UU-Fin-Group))
      ( id-hom-Group (group-Concrete-Group (UU-Fin-Group l n)))
  is-retraction-hom-inv-loop-group-fin-UU-Fin-Group = {!!}

  iso-loop-group-fin-UU-Fin-Group :
    iso-Group
      ( group-Concrete-Group (UU-Fin-Group l n))
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 iso-loop-group-fin-UU-Fin-Group = {!!}
```
