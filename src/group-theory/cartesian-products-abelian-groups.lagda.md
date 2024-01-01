# Cartesian products of abelian groups

```agda
module group-theory.cartesian-products-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.cartesian-products-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The cartesian product of two abelian groups `A` and `B` is an abelian group
structure on the cartesian product of the underlying sets.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  group-prod-Ab : Group (l1 ⊔ l2)
  group-prod-Ab = {!!}

  monoid-prod-Ab : Monoid (l1 ⊔ l2)
  monoid-prod-Ab = {!!}

  semigroup-prod-Ab : Semigroup (l1 ⊔ l2)
  semigroup-prod-Ab = {!!}

  set-prod-Ab : Set (l1 ⊔ l2)
  set-prod-Ab = {!!}

  type-prod-Ab : UU (l1 ⊔ l2)
  type-prod-Ab = {!!}

  is-set-type-prod-Ab : is-set type-prod-Ab
  is-set-type-prod-Ab = {!!}

  add-prod-Ab : (x y : type-prod-Ab) → type-prod-Ab
  add-prod-Ab = {!!}

  zero-prod-Ab : type-prod-Ab
  zero-prod-Ab = {!!}

  neg-prod-Ab : type-prod-Ab → type-prod-Ab
  neg-prod-Ab = {!!}

  associative-add-prod-Ab :
    (x y z : type-prod-Ab) →
    Id (add-prod-Ab (add-prod-Ab x y) z) (add-prod-Ab x (add-prod-Ab y z))
  associative-add-prod-Ab = {!!}

  left-unit-law-add-prod-Ab :
    (x : type-prod-Ab) → Id (add-prod-Ab zero-prod-Ab x) x
  left-unit-law-add-prod-Ab = {!!}

  right-unit-law-add-prod-Ab :
    (x : type-prod-Ab) → Id (add-prod-Ab x zero-prod-Ab) x
  right-unit-law-add-prod-Ab = {!!}

  left-inverse-law-add-prod-Ab :
    (x : type-prod-Ab) → Id (add-prod-Ab (neg-prod-Ab x) x) zero-prod-Ab
  left-inverse-law-add-prod-Ab = {!!}

  right-inverse-law-add-prod-Ab :
    (x : type-prod-Ab) → Id (add-prod-Ab x (neg-prod-Ab x)) zero-prod-Ab
  right-inverse-law-add-prod-Ab = {!!}

  commutative-add-prod-Ab :
    (x y : type-prod-Ab) → Id (add-prod-Ab x y) (add-prod-Ab y x)
  commutative-add-prod-Ab = {!!}

  prod-Ab : Ab (l1 ⊔ l2)
  prod-Ab = {!!}
```
