# Products of commutative rings

```agda
module commutative-algebra.products-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.products-rings
open import ring-theory.rings
```

</details>

## Idea

Given two commutative rings R1 and R2, we define a commutative ring structure on
the product of R1 and R2.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Commutative-Ring l1) (R2 : Commutative-Ring l2)
  where

  set-prod-Commutative-Ring : Set (l1 ⊔ l2)
  set-prod-Commutative-Ring = {!!}

  type-prod-Commutative-Ring : UU (l1 ⊔ l2)
  type-prod-Commutative-Ring = {!!}

  is-set-type-prod-Commutative-Ring : is-set type-prod-Commutative-Ring
  is-set-type-prod-Commutative-Ring = {!!}

  add-prod-Commutative-Ring :
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring
  add-prod-Commutative-Ring = {!!}

  zero-prod-Commutative-Ring : type-prod-Commutative-Ring
  zero-prod-Commutative-Ring = {!!}

  neg-prod-Commutative-Ring :
    type-prod-Commutative-Ring → type-prod-Commutative-Ring
  neg-prod-Commutative-Ring = {!!}

  left-unit-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    add-prod-Commutative-Ring zero-prod-Commutative-Ring x ＝ x
  left-unit-law-add-prod-Commutative-Ring = {!!}

  right-unit-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    add-prod-Commutative-Ring x zero-prod-Commutative-Ring ＝ x
  right-unit-law-add-prod-Commutative-Ring = {!!}

  left-inverse-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id
      ( add-prod-Commutative-Ring (neg-prod-Commutative-Ring x) x)
      zero-prod-Commutative-Ring
  left-inverse-law-add-prod-Commutative-Ring = {!!}

  right-inverse-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id
      ( add-prod-Commutative-Ring x (neg-prod-Commutative-Ring x))
      ( zero-prod-Commutative-Ring)
  right-inverse-law-add-prod-Commutative-Ring = {!!}

  associative-add-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( add-prod-Commutative-Ring (add-prod-Commutative-Ring x y) z)
      ( add-prod-Commutative-Ring x (add-prod-Commutative-Ring y z))
  associative-add-prod-Commutative-Ring = {!!}

  commutative-add-prod-Commutative-Ring :
    (x y : type-prod-Commutative-Ring) →
    Id (add-prod-Commutative-Ring x y) (add-prod-Commutative-Ring y x)
  commutative-add-prod-Commutative-Ring = {!!}

  mul-prod-Commutative-Ring :
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring
  mul-prod-Commutative-Ring = {!!}

  one-prod-Commutative-Ring : type-prod-Commutative-Ring
  one-prod-Commutative-Ring = {!!}

  associative-mul-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( mul-prod-Commutative-Ring (mul-prod-Commutative-Ring x y) z)
      ( mul-prod-Commutative-Ring x (mul-prod-Commutative-Ring y z))
  associative-mul-prod-Commutative-Ring = {!!}

  left-unit-law-mul-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id (mul-prod-Commutative-Ring one-prod-Commutative-Ring x) x
  left-unit-law-mul-prod-Commutative-Ring = {!!}

  right-unit-law-mul-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id (mul-prod-Commutative-Ring x one-prod-Commutative-Ring) x
  right-unit-law-mul-prod-Commutative-Ring = {!!}

  left-distributive-mul-add-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( mul-prod-Commutative-Ring x (add-prod-Commutative-Ring y z))
      ( add-prod-Commutative-Ring
        ( mul-prod-Commutative-Ring x y)
        ( mul-prod-Commutative-Ring x z))
  left-distributive-mul-add-prod-Commutative-Ring = {!!}

  right-distributive-mul-add-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( mul-prod-Commutative-Ring (add-prod-Commutative-Ring x y) z)
      ( add-prod-Commutative-Ring
        ( mul-prod-Commutative-Ring x z)
        ( mul-prod-Commutative-Ring y z))
  right-distributive-mul-add-prod-Commutative-Ring = {!!}

  semigroup-prod-Commutative-Ring : Semigroup (l1 ⊔ l2)
  semigroup-prod-Commutative-Ring = {!!}

  group-prod-Commutative-Ring : Group (l1 ⊔ l2)
  group-prod-Commutative-Ring = {!!}

  ab-prod-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-prod-Commutative-Ring = {!!}

  ring-prod-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-prod-Commutative-Ring = {!!}

  commutative-mul-prod-Commutative-Ring :
    (x y : type-prod-Commutative-Ring) →
    mul-prod-Commutative-Ring x y ＝ mul-prod-Commutative-Ring y x
  commutative-mul-prod-Commutative-Ring (x1 , x2) (y1 , y2) = {!!}

  prod-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  pr1 prod-Commutative-Ring = {!!}
```
