# Groups of loops in `1`-types

```agda
module synthetic-homotopy-theory.groups-of-loops-in-1-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.semigroups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The [loop space](synthetic-homotopy-theory.loop-spaces.md) of any
[pointed](structured-types.pointed-types.md) [1-type](foundation.1-types.md) is
a [group](group-theory.groups.md).

## Definitions

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  loop-space-Set : is-set (type-Ω A) → Set l
  loop-space-Set = {!!}

  loop-space-Semigroup : is-set (type-Ω A) → Semigroup l
  loop-space-Semigroup = {!!}

  loop-space-Group : is-set (type-Ω A) → Group l
  loop-space-Group = {!!}

loop-space-1-type-Set :
  {l : Level} (A : 1-Type l) (a : type-1-Type A) → Set l
loop-space-1-type-Set = {!!}

loop-space-1-type-Semigroup :
  {l : Level} (A : 1-Type l) (a : type-1-Type A) → Semigroup l
loop-space-1-type-Semigroup = {!!}

loop-space-1-type-Group :
  {l : Level} (A : 1-Type l) (a : type-1-Type A) → Group l
loop-space-1-type-Group = {!!}
```
