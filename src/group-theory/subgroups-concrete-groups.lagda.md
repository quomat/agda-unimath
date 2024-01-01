# Subgroups of concrete groups

```agda
module group-theory.subgroups-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.0-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.faithful-maps
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-group-actions
open import group-theory.homomorphisms-concrete-groups
open import group-theory.orbits-concrete-group-actions
open import group-theory.transitive-concrete-group-actions

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A subgroup of a concrete group `G` is a pointed transitive `G`-set.

## Definition

```agda
subgroup-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) →
  classifying-type-Concrete-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-Concrete-Group = {!!}

subgroup-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-Concrete-Group = {!!}

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : subgroup-Concrete-Group l2 G)
  where

  transitive-action-subgroup-Concrete-Group :
    transitive-action-Concrete-Group l2 G
  transitive-action-subgroup-Concrete-Group = {!!}

  action-subgroup-Concrete-Group : action-Concrete-Group l2 G
  action-subgroup-Concrete-Group = {!!}

  coset-subgroup-Concrete-Group : Set l2
  coset-subgroup-Concrete-Group = {!!}

  type-coset-subgroup-Concrete-Group : UU l2
  type-coset-subgroup-Concrete-Group = {!!}

  is-transitive-action-subgroup-Concrete-Group :
    is-transitive-action-Concrete-Group G action-subgroup-Concrete-Group
  is-transitive-action-subgroup-Concrete-Group = {!!}

  mul-transitive-action-subgroup-Concrete-Group :
    type-Concrete-Group G → type-coset-subgroup-Concrete-Group →
    type-coset-subgroup-Concrete-Group
  mul-transitive-action-subgroup-Concrete-Group = {!!}

  is-abstractly-transitive-transitive-action-subgroup-Concrete-Group :
    is-abstractly-transitive-action-Concrete-Group G
      action-subgroup-Concrete-Group
  is-abstractly-transitive-transitive-action-subgroup-Concrete-Group = {!!}

  classifying-type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-Concrete-Group = {!!}

  unit-coset-subgroup-Concrete-Group : type-coset-subgroup-Concrete-Group
  unit-coset-subgroup-Concrete-Group = {!!}

  shape-subgroup-Concrete-Group : classifying-type-subgroup-Concrete-Group
  pr1 shape-subgroup-Concrete-Group = {!!}

  classifying-pointed-type-subgroup-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-Concrete-Group = {!!}

  is-connected-classifying-type-subgroup-Concrete-Group :
    is-0-connected classifying-type-subgroup-Concrete-Group
  is-connected-classifying-type-subgroup-Concrete-Group = {!!}

  classifying-inclusion-subgroup-Concrete-Group :
    classifying-type-subgroup-Concrete-Group →
    classifying-type-Concrete-Group G
  classifying-inclusion-subgroup-Concrete-Group = {!!}

  preserves-shape-classifying-inclusion-subgroup-Concrete-Group :
    classifying-inclusion-subgroup-Concrete-Group
      shape-subgroup-Concrete-Group ＝
    shape-Concrete-Group G
  preserves-shape-classifying-inclusion-subgroup-Concrete-Group = {!!}

  classifying-pointed-inclusion-subgroup-Concrete-Group :
    classifying-pointed-type-subgroup-Concrete-Group →∗
    classifying-pointed-type-Concrete-Group G
  classifying-pointed-inclusion-subgroup-Concrete-Group = {!!}

  is-0-map-classifying-inclusion-subgroup-Concrete-Group :
    is-0-map classifying-inclusion-subgroup-Concrete-Group
  is-0-map-classifying-inclusion-subgroup-Concrete-Group = {!!}

  is-faithful-classifying-inclusion-subgroup-Concrete-Group :
    is-faithful classifying-inclusion-subgroup-Concrete-Group
  is-faithful-classifying-inclusion-subgroup-Concrete-Group = {!!}

  type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  type-subgroup-Concrete-Group = {!!}

  concrete-group-subgroup-Concrete-Group :
    Concrete-Group (l1 ⊔ l2)
  pr1 (pr1 concrete-group-subgroup-Concrete-Group) = {!!}

  hom-inclusion-subgroup-Concrete-Group :
    hom-Concrete-Group concrete-group-subgroup-Concrete-Group G
  hom-inclusion-subgroup-Concrete-Group = {!!}
```

## Properties

### The type of subgroups of a group is a set

```agda
subtype-preserves-unit-coset-equiv-action-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : subgroup-Concrete-Group l2 G)
  (Y : subgroup-Concrete-Group l3 G) →
  subtype l3
    ( equiv-action-Concrete-Group G
      ( action-subgroup-Concrete-Group G X)
      ( action-subgroup-Concrete-Group G Y))
subtype-preserves-unit-coset-equiv-action-Concrete-Group = {!!}

equiv-subgroup-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1) → subgroup-Concrete-Group l2 G →
  subgroup-Concrete-Group l3 G → UU (l1 ⊔ l2 ⊔ l3)
equiv-subgroup-Concrete-Group = {!!}

extensionality-subgroup-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X Y : subgroup-Concrete-Group l2 G) →
  (X ＝ Y) ≃ equiv-subgroup-Concrete-Group G X Y
extensionality-subgroup-Concrete-Group = {!!}

is-set-subgroup-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) →
  is-set (subgroup-Concrete-Group l2 G)
is-set-subgroup-Concrete-Group = {!!}
```
