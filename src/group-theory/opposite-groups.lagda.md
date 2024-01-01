# The opposite of a group

```agda
module group-theory.opposite-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.isomorphisms-groups
open import group-theory.monoids
open import group-theory.opposite-semigroups
```

</details>

## Idea

The **opposite of a [group](group-theory.groups.md)** `G` with multiplication
`μ` is a group with the same underlying [set](foundation-core.sets.md) as `G`
and multiplication given by `x y ↦ μ y x`.

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  is-unital-op-Group : is-unital-Semigroup (op-Semigroup (semigroup-Group G))
  pr1 is-unital-op-Group = {!!}

  is-group-op-Group : is-group (op-Semigroup (semigroup-Group G))
  pr1 is-group-op-Group = {!!}

  op-Group : Group l
  pr1 op-Group = {!!}
```

## Properties

### The opposite group of `G` is isomorphic to `G`

```agda
module _
  {l : Level} (G : Group l)
  where

  equiv-inv-Group : equiv-Group G (op-Group G)
  pr1 equiv-inv-Group = {!!}

  iso-inv-Group : iso-Group G (op-Group G)
  iso-inv-Group = {!!}
```
