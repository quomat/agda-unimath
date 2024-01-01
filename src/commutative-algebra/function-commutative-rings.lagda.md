# Function commutative rings

```agda
module commutative-algebra.function-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-commutative-rings

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids

open import ring-theory.rings
```

</details>

## Idea

Given a commutative ring `A` and a type `X`, the type `A^X` of functions from
`X` into the underlying type of `A` is again a commutative ring.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (X : UU l2)
  where

  function-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  function-Commutative-Ring = {!!}

  ring-function-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-function-Commutative-Ring = {!!}

  ab-function-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-function-Commutative-Ring = {!!}

  multiplicative-commutative-monoid-function-Commutative-Ring :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-function-Commutative-Ring = {!!}

  set-function-Commutative-Ring : Set (l1 ⊔ l2)
  set-function-Commutative-Ring = {!!}

  type-function-Commutative-Ring : UU (l1 ⊔ l2)
  type-function-Commutative-Ring = {!!}

  is-set-type-function-Commutative-Ring : is-set type-function-Commutative-Ring
  is-set-type-function-Commutative-Ring = {!!}

  add-function-Commutative-Ring :
    type-function-Commutative-Ring → type-function-Commutative-Ring →
    type-function-Commutative-Ring
  add-function-Commutative-Ring = {!!}

  zero-function-Commutative-Ring : type-function-Commutative-Ring
  zero-function-Commutative-Ring = {!!}

  associative-add-function-Commutative-Ring :
    (x y z : type-function-Commutative-Ring) →
    add-function-Commutative-Ring (add-function-Commutative-Ring x y) z ＝
    add-function-Commutative-Ring x (add-function-Commutative-Ring y z)
  associative-add-function-Commutative-Ring = {!!}

  left-unit-law-add-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    add-function-Commutative-Ring zero-function-Commutative-Ring x ＝ x
  left-unit-law-add-function-Commutative-Ring = {!!}

  right-unit-law-add-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    add-function-Commutative-Ring x zero-function-Commutative-Ring ＝ x
  right-unit-law-add-function-Commutative-Ring = {!!}

  commutative-add-function-Commutative-Ring :
    (x y : type-function-Commutative-Ring) →
    add-function-Commutative-Ring x y ＝ add-function-Commutative-Ring y x
  commutative-add-function-Commutative-Ring = {!!}

  mul-function-Commutative-Ring :
    type-function-Commutative-Ring → type-function-Commutative-Ring →
    type-function-Commutative-Ring
  mul-function-Commutative-Ring = {!!}

  one-function-Commutative-Ring : type-function-Commutative-Ring
  one-function-Commutative-Ring = {!!}

  associative-mul-function-Commutative-Ring :
    (x y z : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring (mul-function-Commutative-Ring x y) z ＝
    mul-function-Commutative-Ring x (mul-function-Commutative-Ring y z)
  associative-mul-function-Commutative-Ring = {!!}

  left-unit-law-mul-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring one-function-Commutative-Ring x ＝ x
  left-unit-law-mul-function-Commutative-Ring = {!!}

  right-unit-law-mul-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring x one-function-Commutative-Ring ＝ x
  right-unit-law-mul-function-Commutative-Ring = {!!}

  left-distributive-mul-add-function-Commutative-Ring :
    (f g h : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring f (add-function-Commutative-Ring g h) ＝
    add-function-Commutative-Ring
      ( mul-function-Commutative-Ring f g)
      ( mul-function-Commutative-Ring f h)
  left-distributive-mul-add-function-Commutative-Ring = {!!}

  right-distributive-mul-add-function-Commutative-Ring :
    (f g h : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring (add-function-Commutative-Ring f g) h ＝
    add-function-Commutative-Ring
      ( mul-function-Commutative-Ring f h)
      ( mul-function-Commutative-Ring g h)
  right-distributive-mul-add-function-Commutative-Ring = {!!}

  left-zero-law-mul-function-Commutative-Ring :
    (f : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring zero-function-Commutative-Ring f ＝
    zero-function-Commutative-Ring
  left-zero-law-mul-function-Commutative-Ring = {!!}

  right-zero-law-mul-function-Commutative-Ring :
    (f : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring f zero-function-Commutative-Ring ＝
    zero-function-Commutative-Ring
  right-zero-law-mul-function-Commutative-Ring = {!!}

  commutative-mul-function-Commutative-Ring :
    (f g : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring f g ＝ mul-function-Commutative-Ring g f
  commutative-mul-function-Commutative-Ring = {!!}
```
