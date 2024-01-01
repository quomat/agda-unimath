# Cartesian products of monoids

```agda
module group-theory.cartesian-products-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.cartesian-products-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The cartesian product of two monoids `M` and `N` consists of the product `M × N`
of the underlying sets and the componentwise operation on it.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  semigroup-prod-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-prod-Monoid = {!!}

  set-prod-Monoid : Set (l1 ⊔ l2)
  set-prod-Monoid = {!!}

  type-prod-Monoid : UU (l1 ⊔ l2)
  type-prod-Monoid = {!!}

  is-set-type-prod-Monoid : is-set type-prod-Monoid
  is-set-type-prod-Monoid = {!!}

  mul-prod-Monoid : (x y : type-prod-Monoid) → type-prod-Monoid
  mul-prod-Monoid = {!!}

  associative-mul-prod-Monoid :
    (x y z : type-prod-Monoid) →
    Id
      ( mul-prod-Monoid (mul-prod-Monoid x y) z)
      ( mul-prod-Monoid x (mul-prod-Monoid y z))
  associative-mul-prod-Monoid = {!!}

  unit-prod-Monoid : type-prod-Monoid
  unit-prod-Monoid = {!!}

  left-unit-law-mul-prod-Monoid :
    (x : type-prod-Monoid) → Id (mul-prod-Monoid unit-prod-Monoid x) x
  left-unit-law-mul-prod-Monoid = {!!}

  right-unit-law-mul-prod-Monoid :
    (x : type-prod-Monoid) → Id (mul-prod-Monoid x unit-prod-Monoid) x
  right-unit-law-mul-prod-Monoid = {!!}

  prod-Monoid : Monoid (l1 ⊔ l2)
  prod-Monoid = {!!}
```
