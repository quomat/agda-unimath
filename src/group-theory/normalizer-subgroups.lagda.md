# Normalizer subgroups

```agda
module group-theory.normalizer-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.conjugation
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.subgroups
open import group-theory.subsets-groups
```

</details>

## Idea

Consider a [subgroup](group-theory.subgroups.md) `H` of a
[group](group-theory.groups.md) `G`. The **normalizer subgroup** `Nᴳ(H)` of `G`
is the largest subgroup of `G` of which `H` is a
[normal subgroup](group-theory.normal-subgroups.md). The normalizer subgroup
consists of all elements `g : G` such that `h ∈ H ⇔ (gh)g⁻¹ ∈ H` for all
`h ∈ G`. In other words, the normalizer subgroup consists of all elements `g`
such that `(gH)g⁻¹ ＝ H`.

The weaker condition that `(gH)g⁻¹ ⊆ H` is
[not sufficient](https://math.stackexchange.com/q/107862) in the case of
infinite groups. In this case, the group elements satisfying this weaker
condition may not be closed under inverses.

Note: The normalizer subgroup should not be confused with the
[normal closure](group-theory.normal-closures-subgroups.md) of a subgroup, or
with the [normal core](group-theory.normal-cores-subgroups.md) of a subgroup.

## Definitions

### The universal property of the normalizer subgroup

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G)
  (N : Subgroup l3 G)
  where

  is-normalizer-Subgroup : UUω
  is-normalizer-Subgroup = {!!}
```

### The construction of the normalizer subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-normalizer-Subgroup : subset-Group (l1 ⊔ l2) G
  subset-normalizer-Subgroup x = {!!}

  is-in-normalizer-Subgroup : type-Group G → UU (l1 ⊔ l2)
  is-in-normalizer-Subgroup = {!!}

  is-closed-under-eq-normalizer-Subgroup :
    {x y : type-Group G} →
    is-in-normalizer-Subgroup x → x ＝ y → is-in-normalizer-Subgroup y
  is-closed-under-eq-normalizer-Subgroup = {!!}

  restrict-conjugation-Subgroup :
    (x : type-Group G) → is-in-normalizer-Subgroup x →
    type-Subgroup G H → type-Subgroup G H
  pr1 (restrict-conjugation-Subgroup x u (y , h)) = {!!}

  contains-unit-normalizer-Subgroup :
    contains-unit-subset-Group G subset-normalizer-Subgroup
  pr1 contains-unit-normalizer-Subgroup u = {!!}

  is-closed-under-multiplication-normalizer-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-normalizer-Subgroup
  pr1 (is-closed-under-multiplication-normalizer-Subgroup {x} {y} u v) w = {!!}

  is-closed-under-inverses-normalizer-Subgroup :
    is-closed-under-inverses-subset-Group G subset-normalizer-Subgroup
  pr1 (is-closed-under-inverses-normalizer-Subgroup {x} u {y}) h = {!!}

  normalizer-Subgroup : Subgroup (l1 ⊔ l2) G
  pr1 normalizer-Subgroup = {!!}

  forward-implication-is-normalizer-normalizer-Subgroup :
    {l : Level} (K : Subgroup l G) →
    ( {x y : type-Group G} → is-in-Subgroup G K x →
      is-in-Subgroup G H y →
      is-in-Subgroup G H (conjugation-Group G x y)) →
    leq-Subgroup G K normalizer-Subgroup
  pr1 (forward-implication-is-normalizer-normalizer-Subgroup K u x k {y}) h = {!!}

  backward-implication-is-normalizer-normalizer-Subgroup :
    {l : Level} (K : Subgroup l G) → leq-Subgroup G K normalizer-Subgroup →
    {x y : type-Group G} → is-in-Subgroup G K x →
    is-in-Subgroup G H y →
    is-in-Subgroup G H (conjugation-Group G x y)
  backward-implication-is-normalizer-normalizer-Subgroup K u {x} {y} k h = {!!}

  is-normalizer-normalizer-Subgroup :
    is-normalizer-Subgroup G H normalizer-Subgroup
  pr1 (is-normalizer-normalizer-Subgroup K) = {!!}
```

### The inclusion of `H` into its normalizer `Nᴳ(H)`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (N : Subgroup l3 G)
  (is-normalizer-G-H-N : is-normalizer-Subgroup G H N)
  where

  is-in-normalizer-is-in-type-Subgroup :
    (x : type-Group G) → is-in-Subgroup G H x → is-in-Subgroup G N x
  is-in-normalizer-is-in-type-Subgroup = {!!}

  inclusion-is-normalizer-Subgroup : type-Subgroup G H → type-Subgroup G N
  inclusion-is-normalizer-Subgroup = {!!}

  hom-inclusion-is-normalizer-Subgroup :
    hom-Group (group-Subgroup G H) (group-Subgroup G N)
  pr1 hom-inclusion-is-normalizer-Subgroup = {!!}
```

## See also

- [Centralizer subgroups](group-theory.centralizer-subgroups.md)
- [Normal closures of subgroups](group-theory.normal-closures-subgroups.md)
- [Normal cores of subgroups](group-theory.normal-cores-subgroups.md)

## External links

- [normalizer](https://ncatlab.org/nlab/show/normalizer) at $n$Lab
- [Centralizer and normalizer](https://en.wikipedia.org/wiki/Centralizer_and_normalizer)
  at Wikipedia
- [Normalizer of a subgroup](https://groupprops.subwiki.org/wiki/Normalizer_of_a_subgroup)
  at Groupprops
