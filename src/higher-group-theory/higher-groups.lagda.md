# Higher groups

```agda
module higher-group-theory.higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

An **∞-group** is just a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md) type. Its underlying type is its
[loop space](synthetic-homotopy-theory.loop-spaces.md), and the classifying type
is the pointed connected type itself.

## Definition

```agda
∞-Group : (l : Level) → UU (lsuc l)
∞-Group = {!!}

module _
  {l : Level} (G : ∞-Group l)
  where

  classifying-pointed-type-∞-Group : Pointed-Type l
  classifying-pointed-type-∞-Group = {!!}

  classifying-type-∞-Group : UU l
  classifying-type-∞-Group = {!!}

  shape-∞-Group : classifying-type-∞-Group
  shape-∞-Group = {!!}

  is-0-connected-classifying-type-∞-Group :
    is-0-connected classifying-type-∞-Group
  is-0-connected-classifying-type-∞-Group = {!!}

  mere-eq-classifying-type-∞-Group :
    (X Y : classifying-type-∞-Group) → mere-eq X Y
  mere-eq-classifying-type-∞-Group = {!!}

  elim-prop-classifying-type-∞-Group :
    {l2 : Level} (P : classifying-type-∞-Group → Prop l2) →
    type-Prop (P shape-∞-Group) →
    ((X : classifying-type-∞-Group) → type-Prop (P X))
  elim-prop-classifying-type-∞-Group = {!!}

  type-∞-Group : UU l
  type-∞-Group = {!!}

  unit-∞-Group : type-∞-Group
  unit-∞-Group = {!!}

  mul-∞-Group : (x y : type-∞-Group) → type-∞-Group
  mul-∞-Group = {!!}

  associative-mul-∞-Group :
    (x y z : type-∞-Group) →
    Id
      ( mul-∞-Group (mul-∞-Group x y) z)
      ( mul-∞-Group x (mul-∞-Group y z))
  associative-mul-∞-Group = {!!}

  left-unit-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group unit-∞-Group x) x
  left-unit-law-mul-∞-Group = {!!}

  right-unit-law-mul-∞-Group :
    (y : type-∞-Group) → Id (mul-∞-Group y unit-∞-Group) y
  right-unit-law-mul-∞-Group = {!!}

  coherence-unit-laws-mul-∞-Group :
    Id
      ( left-unit-law-mul-∞-Group unit-∞-Group)
      ( right-unit-law-mul-∞-Group unit-∞-Group)
  coherence-unit-laws-mul-∞-Group = {!!}

  inv-∞-Group : type-∞-Group → type-∞-Group
  inv-∞-Group = {!!}

  left-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group (inv-∞-Group x) x) unit-∞-Group
  left-inverse-law-mul-∞-Group = {!!}

  right-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group x (inv-∞-Group x)) unit-∞-Group
  right-inverse-law-mul-∞-Group = {!!}
```
