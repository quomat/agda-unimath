# Products of rings

```agda
module ring-theory.products-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

Given two ringrs R1 and R2, we define a ring structure on the product of R1 and
R2.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  where

  set-prod-Ring : Set (l1 ⊔ l2)
  set-prod-Ring = {!!}

  type-prod-Ring : UU (l1 ⊔ l2)
  type-prod-Ring = {!!}

  is-set-type-prod-Ring : is-set type-prod-Ring
  is-set-type-prod-Ring = {!!}

  add-prod-Ring : type-prod-Ring → type-prod-Ring → type-prod-Ring
  pr1 (add-prod-Ring (pair x1 y1) (pair x2 y2)) = {!!}

  zero-prod-Ring : type-prod-Ring
  pr1 zero-prod-Ring = {!!}

  neg-prod-Ring : type-prod-Ring → type-prod-Ring
  pr1 (neg-prod-Ring (pair x y)) = {!!}

  left-unit-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring zero-prod-Ring x) x
  left-unit-law-add-prod-Ring = {!!}

  right-unit-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring x zero-prod-Ring) x
  right-unit-law-add-prod-Ring = {!!}

  left-inverse-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring (neg-prod-Ring x) x) zero-prod-Ring
  left-inverse-law-add-prod-Ring = {!!}

  right-inverse-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring x (neg-prod-Ring x)) zero-prod-Ring
  right-inverse-law-add-prod-Ring = {!!}

  associative-add-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( add-prod-Ring (add-prod-Ring x y) z)
      ( add-prod-Ring x (add-prod-Ring y z))
  associative-add-prod-Ring = {!!}

  commutative-add-prod-Ring :
    (x y : type-prod-Ring) → Id (add-prod-Ring x y) (add-prod-Ring y x)
  commutative-add-prod-Ring = {!!}

  mul-prod-Ring : type-prod-Ring → type-prod-Ring → type-prod-Ring
  pr1 (mul-prod-Ring (pair x1 y1) (pair x2 y2)) = {!!}

  one-prod-Ring : type-prod-Ring
  pr1 one-prod-Ring = {!!}

  associative-mul-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( mul-prod-Ring (mul-prod-Ring x y) z)
      ( mul-prod-Ring x (mul-prod-Ring y z))
  associative-mul-prod-Ring = {!!}

  left-unit-law-mul-prod-Ring :
    (x : type-prod-Ring) → Id (mul-prod-Ring one-prod-Ring x) x
  left-unit-law-mul-prod-Ring = {!!}

  right-unit-law-mul-prod-Ring :
    (x : type-prod-Ring) → Id (mul-prod-Ring x one-prod-Ring) x
  right-unit-law-mul-prod-Ring = {!!}

  left-distributive-mul-add-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( mul-prod-Ring x (add-prod-Ring y z))
      ( add-prod-Ring (mul-prod-Ring x y) (mul-prod-Ring x z))
  left-distributive-mul-add-prod-Ring = {!!}

  right-distributive-mul-add-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( mul-prod-Ring (add-prod-Ring x y) z)
      ( add-prod-Ring (mul-prod-Ring x z) (mul-prod-Ring y z))
  right-distributive-mul-add-prod-Ring = {!!}

  semigroup-prod-Ring : Semigroup (l1 ⊔ l2)
  pr1 semigroup-prod-Ring = {!!}

  group-prod-Ring : Group (l1 ⊔ l2)
  pr1 group-prod-Ring = {!!}

  ab-prod-Ring : Ab (l1 ⊔ l2)
  pr1 ab-prod-Ring = {!!}

  prod-Ring : Ring (l1 ⊔ l2)
  pr1 prod-Ring = {!!}
```
