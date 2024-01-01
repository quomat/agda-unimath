# Function commutative monoids

```agda
module group-theory.function-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.dependent-products-commutative-monoids
open import group-theory.monoids
```

</details>

## Idea

Given a commutative monoid `M` and a type `X`, the function commuative monoid
`M^X` consists of functions from `X` to the underlying type of `M`. The
multiplicative operation and the unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (X : UU l2)
  where

  function-Commutative-Monoid : Commutative-Monoid (l1 ⊔ l2)
  function-Commutative-Monoid = {!!}

  monoid-function-Commutative-Monoid : Monoid (l1 ⊔ l2)
  monoid-function-Commutative-Monoid = {!!}

  set-function-Commutative-Monoid : Set (l1 ⊔ l2)
  set-function-Commutative-Monoid = {!!}

  type-function-Commutative-Monoid : UU (l1 ⊔ l2)
  type-function-Commutative-Monoid = {!!}

  unit-function-Commutative-Monoid : type-function-Commutative-Monoid
  unit-function-Commutative-Monoid = {!!}

  mul-function-Commutative-Monoid :
    (f g : type-function-Commutative-Monoid) →
    type-function-Commutative-Monoid
  mul-function-Commutative-Monoid = {!!}

  associative-mul-function-Commutative-Monoid :
    (f g h : type-function-Commutative-Monoid) →
    mul-function-Commutative-Monoid (mul-function-Commutative-Monoid f g) h ＝
    mul-function-Commutative-Monoid f (mul-function-Commutative-Monoid g h)
  associative-mul-function-Commutative-Monoid = {!!}

  left-unit-law-mul-function-Commutative-Monoid :
    (f : type-function-Commutative-Monoid) →
    mul-function-Commutative-Monoid unit-function-Commutative-Monoid f ＝ f
  left-unit-law-mul-function-Commutative-Monoid = {!!}

  right-unit-law-mul-function-Commutative-Monoid :
    (f : type-function-Commutative-Monoid) →
    mul-function-Commutative-Monoid f unit-function-Commutative-Monoid ＝ f
  right-unit-law-mul-function-Commutative-Monoid = {!!}

  commutative-mul-function-Commutative-Monoid :
    (f g : type-function-Commutative-Monoid) →
    mul-function-Commutative-Monoid f g ＝ mul-function-Commutative-Monoid g f
  commutative-mul-function-Commutative-Monoid = {!!}
```
