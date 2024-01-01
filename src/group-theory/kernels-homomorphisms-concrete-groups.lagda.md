# Kernels of homomorphisms of concrete groups

```agda
module group-theory.kernels-homomorphisms-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.sets
open import foundation.truncated-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The kernel of a concrete group homomorphsim `Bf : BG →∗ BH` is the connected
component at the base point of the fiber of `Bf`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  classifying-type-kernel-hom-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-kernel-hom-Concrete-Group = {!!}

  shape-kernel-hom-Concrete-Group :
    classifying-type-kernel-hom-Concrete-Group
  shape-kernel-hom-Concrete-Group = {!!}

  classifying-pointed-type-kernel-hom-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-kernel-hom-Concrete-Group = {!!}
  pr2 classifying-pointed-type-kernel-hom-Concrete-Group = {!!}

  is-0-connected-classifying-type-kernel-hom-Concrete-Group :
    is-0-connected classifying-type-kernel-hom-Concrete-Group
  is-0-connected-classifying-type-kernel-hom-Concrete-Group = {!!}

  is-1-type-classifying-type-kernel-hom-Concrete-Group :
    is-1-type classifying-type-kernel-hom-Concrete-Group
  is-1-type-classifying-type-kernel-hom-Concrete-Group = {!!}

  ∞-group-kernel-hom-Concrete-Group : ∞-Group (l1 ⊔ l2)
  pr1 ∞-group-kernel-hom-Concrete-Group = {!!}
  pr2 ∞-group-kernel-hom-Concrete-Group = {!!}

  type-kernel-hom-Concrete-Group : UU (l1 ⊔ l2)
  type-kernel-hom-Concrete-Group = {!!}

  is-set-type-kernel-hom-Concrete-Group :
    is-set type-kernel-hom-Concrete-Group
  is-set-type-kernel-hom-Concrete-Group = {!!}

  concrete-group-kernel-hom-Concrete-Group : Concrete-Group (l1 ⊔ l2)
  pr1 concrete-group-kernel-hom-Concrete-Group = {!!}
  pr2 concrete-group-kernel-hom-Concrete-Group = {!!}
```
