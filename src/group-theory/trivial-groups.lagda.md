# Trivial groups

```agda
module group-theory.trivial-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.subgroups
open import group-theory.trivial-subgroups
```

</details>

## Idea

A [group](group-theory.groups.md) is said to be **trivial** if its underlying
type is [contractible](foundation-core.contractible-types.md). In other words, a
group is trivial if it consists only of the unit element.

## Definitions

### The predicate of being a trivial group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-trivial-prop-Group : Prop l1
  is-trivial-prop-Group = {!!}

  is-trivial-Group : UU l1
  is-trivial-Group = {!!}

  is-prop-is-trivial-Group : is-prop is-trivial-Group
  is-prop-is-trivial-Group = {!!}
```

## Properties

### The type of subgroups of a trivial group is contractible

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  abstract
    is-contr-subgroup-is-trivial-Group :
      is-trivial-Group G → is-contr (Subgroup l1 G)
    is-contr-subgroup-is-trivial-Group = {!!}
```
