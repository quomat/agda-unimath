# Subgroups of higher groups

```agda
module higher-group-theory.subgroups-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sets
open import foundation.universe-levels

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

A subgroup of a higher group is a pointed set bundle over its classifying type
with connected total space.

## Definition

```agda
subgroup-action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) →
  classifying-type-∞-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-∞-Group = {!!}

subgroup-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-∞-Group = {!!}

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : subgroup-∞-Group l2 G)
  where

  set-action-subgroup-∞-Group :
    classifying-type-∞-Group G → Set l2
  set-action-subgroup-∞-Group = {!!}

  action-subgroup-∞-Group : classifying-type-∞-Group G → UU l2
  action-subgroup-∞-Group = {!!}

  classifying-type-subgroup-∞-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-∞-Group = {!!}

  shape-subgroup-∞-Group : classifying-type-subgroup-∞-Group
  pr1 shape-subgroup-∞-Group = {!!}

  classifying-pointed-type-subgroup-∞-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-∞-Group = {!!}

  is-connected-classifying-type-subgroup-∞-Group :
    is-0-connected classifying-type-subgroup-∞-Group
  is-connected-classifying-type-subgroup-∞-Group = {!!}

  ∞-group-subgroup-∞-Group : ∞-Group (l1 ⊔ l2)
  pr1 ∞-group-subgroup-∞-Group = {!!}
```
