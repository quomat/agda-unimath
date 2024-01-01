# Concrete groups

```agda
module group-theory.concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.monoids
open import group-theory.opposite-groups
open import group-theory.opposite-semigroups
open import group-theory.semigroups

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

A **concrete group** is a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md)
[1-type](foundation-core.1-types.md).

## Definitions

### Concrete groups

```agda
Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group = {!!}

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = {!!}

  classifying-pointed-type-Concrete-Group : Pointed-Type l
  classifying-pointed-type-Concrete-Group = {!!}

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group = {!!}

  shape-Concrete-Group : classifying-type-Concrete-Group
  shape-Concrete-Group = {!!}

  is-0-connected-classifying-type-Concrete-Group :
    is-0-connected classifying-type-Concrete-Group
  is-0-connected-classifying-type-Concrete-Group = {!!}

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group = {!!}

  elim-prop-classifying-type-Concrete-Group :
    {l2 : Level} (P : classifying-type-Concrete-Group → Prop l2) →
    type-Prop (P shape-Concrete-Group) →
    ((X : classifying-type-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-Concrete-Group = {!!}

  type-Concrete-Group : UU l
  type-Concrete-Group = {!!}

  is-set-type-Concrete-Group : is-set type-Concrete-Group
  is-set-type-Concrete-Group = {!!}

  set-Concrete-Group : Set l
  set-Concrete-Group = {!!}

  abstract
    is-1-type-classifying-type-Concrete-Group :
      is-trunc one-𝕋 classifying-type-Concrete-Group
    is-1-type-classifying-type-Concrete-Group = {!!}

  classifying-1-type-Concrete-Group : Truncated-Type l one-𝕋
  classifying-1-type-Concrete-Group = {!!}

  Id-BG-Set :
    (X Y : classifying-type-Concrete-Group) → Set l
  Id-BG-Set = {!!}
```

### The abstract group associated to a concrete group

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  unit-Concrete-Group : type-Concrete-Group G
  unit-Concrete-Group = {!!}

  mul-Concrete-Group : (x y : type-Concrete-Group G) → type-Concrete-Group G
  mul-Concrete-Group = {!!}

  mul-Concrete-Group' : (x y : type-Concrete-Group G) → type-Concrete-Group G
  mul-Concrete-Group' = {!!}

  associative-mul-Concrete-Group :
    (x y z : type-Concrete-Group G) →
    ( mul-Concrete-Group (mul-Concrete-Group x y) z) ＝
    ( mul-Concrete-Group x (mul-Concrete-Group y z))
  associative-mul-Concrete-Group = {!!}

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) → mul-Concrete-Group unit-Concrete-Group x ＝ x
  left-unit-law-mul-Concrete-Group = {!!}

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group G) → mul-Concrete-Group y unit-Concrete-Group ＝ y
  right-unit-law-mul-Concrete-Group = {!!}

  coherence-unit-laws-mul-Concrete-Group :
    left-unit-law-mul-Concrete-Group unit-Concrete-Group ＝
    right-unit-law-mul-Concrete-Group unit-Concrete-Group
  coherence-unit-laws-mul-Concrete-Group = {!!}

  inv-Concrete-Group : type-Concrete-Group G → type-Concrete-Group G
  inv-Concrete-Group = {!!}

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) →
    mul-Concrete-Group (inv-Concrete-Group x) x ＝ unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group = {!!}

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) →
    mul-Concrete-Group x (inv-Concrete-Group x) ＝ unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group = {!!}

  semigroup-Concrete-Group : Semigroup l
  semigroup-Concrete-Group = {!!}

  is-unital-semigroup-Concrete-Group :
    is-unital-Semigroup semigroup-Concrete-Group
  is-unital-semigroup-Concrete-Group = {!!}

  is-group-Concrete-Group' :
    is-group' semigroup-Concrete-Group is-unital-semigroup-Concrete-Group
  is-group-Concrete-Group' = {!!}

  is-group-Concrete-Group : is-group semigroup-Concrete-Group
  is-group-Concrete-Group = {!!}

  group-Concrete-Group : Group l
  group-Concrete-Group = {!!}
```

### The opposite abstract group associated to a concrete group

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  op-semigroup-Concrete-Group : Semigroup l
  op-semigroup-Concrete-Group = {!!}

  is-unital-op-semigroup-Concrete-Group :
    is-unital-Semigroup op-semigroup-Concrete-Group
  is-unital-op-semigroup-Concrete-Group = {!!}

  is-group-op-Concrete-Group : is-group op-semigroup-Concrete-Group
  is-group-op-Concrete-Group = {!!}

  op-group-Concrete-Group : Group l
  op-group-Concrete-Group = {!!}
```
