# The center of a group

```agda
module group-theory.centers-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.central-elements-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.subgroups
```

</details>

## Idea

The **center** of a group consists of those elements that are central.

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  subtype-center-Group : type-Group G → Prop l
  subtype-center-Group = {!!}

  subgroup-center-Group : Subgroup l G
  pr1 subgroup-center-Group = {!!}
  pr1 (pr2 subgroup-center-Group) = {!!}
  pr1 (pr2 (pr2 subgroup-center-Group)) = {!!}
  pr2 (pr2 (pr2 subgroup-center-Group)) = {!!}

  group-center-Group : Group l
  group-center-Group = {!!}

  type-center-Group : UU l
  type-center-Group = {!!}

  mul-center-Group :
    (x y : type-center-Group) → type-center-Group
  mul-center-Group = {!!}

  associative-mul-center-Group :
    (x y z : type-center-Group) →
    mul-center-Group (mul-center-Group x y) z ＝
    mul-center-Group x (mul-center-Group y z)
  associative-mul-center-Group = {!!}

  inclusion-center-Group :
    type-center-Group → type-Group G
  inclusion-center-Group = {!!}

  is-central-element-inclusion-center-Group :
    (x : type-center-Group) →
    is-central-element-Group G (inclusion-center-Group x)
  is-central-element-inclusion-center-Group x = {!!}

  preserves-mul-inclusion-center-Group :
    {x y : type-center-Group} →
    inclusion-center-Group (mul-center-Group x y) ＝
    mul-Group G
      ( inclusion-center-Group x)
      ( inclusion-center-Group y)
  preserves-mul-inclusion-center-Group {x} {y} = {!!}

  hom-inclusion-center-Group :
    hom-Group group-center-Group G
  hom-inclusion-center-Group = {!!}

  is-normal-subgroup-center-Group :
    is-normal-Subgroup G subgroup-center-Group
  is-normal-subgroup-center-Group x y = {!!}

  center-Group : Normal-Subgroup l G
  pr1 center-Group = {!!}
```
