# Dependent products of commutative monoids

```agda
module group-theory.dependent-products-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.dependent-products-monoids
open import group-theory.monoids
```

</details>

## Idea

Given a family of commutative monoids `Mᵢ` indexed by `i : I`, the dependent
product `Π(i : I), Mᵢ` is a commutative monoid consisting of dependent functions
taking `i : I` to an element of the underlying type of `Mᵢ`. The multiplicative
operation and the unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → Commutative-Monoid l2)
  where

  monoid-Π-Commutative-Monoid : Monoid (l1 ⊔ l2)
  monoid-Π-Commutative-Monoid = {!!}

  set-Π-Commutative-Monoid : Set (l1 ⊔ l2)
  set-Π-Commutative-Monoid = {!!}

  type-Π-Commutative-Monoid : UU (l1 ⊔ l2)
  type-Π-Commutative-Monoid = {!!}

  unit-Π-Commutative-Monoid : type-Π-Commutative-Monoid
  unit-Π-Commutative-Monoid = {!!}

  mul-Π-Commutative-Monoid :
    (f g : type-Π-Commutative-Monoid) → type-Π-Commutative-Monoid
  mul-Π-Commutative-Monoid = {!!}

  associative-mul-Π-Commutative-Monoid :
    (f g h : type-Π-Commutative-Monoid) →
    mul-Π-Commutative-Monoid (mul-Π-Commutative-Monoid f g) h ＝
    mul-Π-Commutative-Monoid f (mul-Π-Commutative-Monoid g h)
  associative-mul-Π-Commutative-Monoid = {!!}

  left-unit-law-mul-Π-Commutative-Monoid :
    (f : type-Π-Commutative-Monoid) →
    mul-Π-Commutative-Monoid unit-Π-Commutative-Monoid f ＝ f
  left-unit-law-mul-Π-Commutative-Monoid = {!!}

  right-unit-law-mul-Π-Commutative-Monoid :
    (f : type-Π-Commutative-Monoid) →
    mul-Π-Commutative-Monoid f unit-Π-Commutative-Monoid ＝ f
  right-unit-law-mul-Π-Commutative-Monoid = {!!}

  commutative-mul-Π-Commutative-Monoid :
    (f g : type-Π-Commutative-Monoid) →
    mul-Π-Commutative-Monoid f g ＝ mul-Π-Commutative-Monoid g f
  commutative-mul-Π-Commutative-Monoid = {!!}

  Π-Commutative-Monoid : Commutative-Monoid (l1 ⊔ l2)
  pr1 Π-Commutative-Monoid = {!!}
```
