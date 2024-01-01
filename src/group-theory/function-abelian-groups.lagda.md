# Function groups of abelian groups

```agda
module group-theory.function-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.dependent-products-abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

Given an abelian group `G` and a type `X`, the function group `G^X` consists of
functions from `X` to the underlying type of `G`. The group operations are given
pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (X : UU l2)
  where

  function-Ab : Ab (l1 ⊔ l2)
  function-Ab = {!!}

  group-function-Ab : Group (l1 ⊔ l2)
  group-function-Ab = {!!}

  semigroup-function-Ab : Semigroup (l1 ⊔ l2)
  semigroup-function-Ab = {!!}

  set-function-Ab : Set (l1 ⊔ l2)
  set-function-Ab = {!!}

  type-function-Ab : UU (l1 ⊔ l2)
  type-function-Ab = {!!}

  add-function-Ab :
    (f g : type-function-Ab) → type-function-Ab
  add-function-Ab = {!!}

  associative-add-function-Ab :
    (f g h : type-function-Ab) →
    add-function-Ab (add-function-Ab f g) h ＝
    add-function-Ab f (add-function-Ab g h)
  associative-add-function-Ab = {!!}

  zero-function-Ab : type-function-Ab
  zero-function-Ab = {!!}

  left-unit-law-add-function-Ab :
    (f : type-function-Ab) → add-function-Ab zero-function-Ab f ＝ f
  left-unit-law-add-function-Ab = {!!}

  right-unit-law-add-function-Ab :
    (f : type-function-Ab) → add-function-Ab f zero-function-Ab ＝ f
  right-unit-law-add-function-Ab = {!!}

  monoid-function-Ab : Monoid (l1 ⊔ l2)
  monoid-function-Ab = {!!}

  neg-function-Ab : type-function-Ab → type-function-Ab
  neg-function-Ab = {!!}

  left-inverse-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab (neg-function-Ab f) f ＝ zero-function-Ab
  left-inverse-law-add-function-Ab = {!!}

  right-inverse-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab f (neg-function-Ab f) ＝ zero-function-Ab
  right-inverse-law-add-function-Ab = {!!}

  commutative-add-function-Ab :
    (f g : type-function-Ab) →
    add-function-Ab f g ＝ add-function-Ab g f
  commutative-add-function-Ab = {!!}
```
