# Trivial subgroups

```agda
module group-theory.trivial-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.subgroups
```

</details>

## Idea

A [subgroup](group-theory.subgroups.md) `H` of `G` is said to be **trivial** if
it only contains the unit element of `G`.

## Definitions

### The trivial subgroup

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  trivial-Subgroup : Subgroup l1 G
  pr1 trivial-Subgroup x = {!!}
```

### The predicate of being a trivial subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-trivial-Subgroup : UU (l1 ⊔ l2)
  is-trivial-Subgroup = {!!}
```
