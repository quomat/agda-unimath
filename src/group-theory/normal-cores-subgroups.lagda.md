# Normal cores of subgroups

```agda
module group-theory.normal-cores-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.conjugation
open import group-theory.groups
open import group-theory.normal-subgroups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
```

</details>

## Idea

Consider a [subgroup](group-theory.subgroups.md) `H` of a
[group](group-theory.groups.md) `G`. The **normal core** of `H` is the largest
[normal subgroup](group-theory.normal-subgroups.md) of `G` that is contained in
`H`. It is equivalently described as the intersection of all
[conjugates](group-theory.conjugation.md) of `H`.

In other words, the normal core operation is the upper adjoint in a
[Galois connection](order-theory.galois-connections-large-posets.md) between the
[large poset](order-theory.large-posets.md) of subgroups of `G` and normal
subgroups of `G`. The lower adjoint of this Galois connection is the inclusion
function from normal subgroups to subgroups of `G`.

Note: The normal core should not be confused with the
[normalizer](group-theory.normalizer-subgroups.md) of a subgroup, or with the
[normal closure](group-theory.normal-closures-subgroups.md) of a subgroup.

## Definitions

### The universal property of the normal core

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-normal-core-Subgroup :
    {l3 : Level} (N : Normal-Subgroup l3 G) → UUω
  is-normal-core-Subgroup = {!!}
```

### The construction of the normal core

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-normal-core-Subgroup : subset-Group (l1 ⊔ l2) G
  subset-normal-core-Subgroup = {!!}

  is-in-normal-core-Subgroup : type-Group G → UU (l1 ⊔ l2)
  is-in-normal-core-Subgroup = {!!}

  is-closed-under-eq-normal-core-Subgroup :
    {x y : type-Group G} → is-in-normal-core-Subgroup x →
    x ＝ y → is-in-normal-core-Subgroup y
  is-closed-under-eq-normal-core-Subgroup = {!!}

  is-closed-under-eq-normal-core-Subgroup' :
    {x y : type-Group G} → is-in-normal-core-Subgroup y →
    x ＝ y → is-in-normal-core-Subgroup x
  is-closed-under-eq-normal-core-Subgroup' = {!!}

  contains-unit-normal-core-Subgroup :
    contains-unit-subset-Group G subset-normal-core-Subgroup
  contains-unit-normal-core-Subgroup = {!!}

  is-closed-under-multiplication-normal-core-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-normal-core-Subgroup
  is-closed-under-multiplication-normal-core-Subgroup = {!!}

  is-closed-under-inverses-normal-core-Subgroup :
    is-closed-under-inverses-subset-Group G subset-normal-core-Subgroup
  is-closed-under-inverses-normal-core-Subgroup = {!!}

  subgroup-normal-core-Subgroup : Subgroup (l1 ⊔ l2) G
  subgroup-normal-core-Subgroup = {!!}

  is-normal-normal-core-Subgroup :
    is-normal-Subgroup G subgroup-normal-core-Subgroup
  is-normal-normal-core-Subgroup = {!!}

  normal-core-Subgroup : Normal-Subgroup (l1 ⊔ l2) G
  normal-core-Subgroup = {!!}

  is-contained-in-subgroup-normal-core-Subgroup :
    leq-Subgroup G subgroup-normal-core-Subgroup H
  is-contained-in-subgroup-normal-core-Subgroup = {!!}

  forward-implication-is-normal-core-normal-core-Subgroup :
    {l : Level} (N : Normal-Subgroup l G) →
    leq-Subgroup G (subgroup-Normal-Subgroup G N) H →
    leq-Normal-Subgroup G N normal-core-Subgroup
  forward-implication-is-normal-core-normal-core-Subgroup = {!!}

  backward-implication-is-normal-core-normal-core-Subgroup :
    {l : Level} (N : Normal-Subgroup l G) →
    leq-Normal-Subgroup G N normal-core-Subgroup →
    leq-Subgroup G (subgroup-Normal-Subgroup G N) H
  backward-implication-is-normal-core-normal-core-Subgroup = {!!}

  is-normal-core-normal-core-Subgroup :
    is-normal-core-Subgroup G H normal-core-Subgroup
  is-normal-core-normal-core-Subgroup = {!!}
```

### The normal core Galois connection

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  preserves-order-normal-core-Subgroup :
    {l2 l3 : Level} (H : Subgroup l2 G) (K : Subgroup l3 G) →
    leq-Subgroup G H K →
    leq-Normal-Subgroup G
      ( normal-core-Subgroup G H)
      ( normal-core-Subgroup G K)
  preserves-order-normal-core-Subgroup = {!!}

  normal-core-subgroup-hom-Large-Poset :
    hom-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( Subgroup-Large-Poset G)
      ( Normal-Subgroup-Large-Poset G)
  normal-core-subgroup-hom-Large-Poset = {!!}

  normal-core-subgroup-Galois-Connection :
    galois-connection-Large-Poset
      ( λ l → l)
      ( λ l2 → l1 ⊔ l2)
      ( Normal-Subgroup-Large-Poset G)
      ( Subgroup-Large-Poset G)
  normal-core-subgroup-Galois-Connection = {!!}
```

## See also

- [Centralizer subgroups](group-theory.centralizer-subgroups.md)
- [Normal closures of subgroups](group-theory.normal-closures-subgroups.md)
- [Normalizers of subgroups](group-theory.normalizer-subgroups.md)
