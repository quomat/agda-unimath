# Dependent products of monoids

```agda
module group-theory.dependent-products-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.dependent-products-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

Given a family of monoids `Mᵢ` indexed by `i : I`, the dependent product
`Π(i : I), Mᵢ` is a monoid consisting of dependent functions taking `i : I` to
an element of the underlying type of `Mᵢ`. The multiplicative operation and the
unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → Monoid l2)
  where

  semigroup-Π-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-Π-Monoid = {!!}

  set-Π-Monoid : Set (l1 ⊔ l2)
  set-Π-Monoid = {!!}

  type-Π-Monoid : UU (l1 ⊔ l2)
  type-Π-Monoid = {!!}

  mul-Π-Monoid : (f g : type-Π-Monoid) → type-Π-Monoid
  mul-Π-Monoid = {!!}

  associative-mul-Π-Monoid :
    (f g h : type-Π-Monoid) →
    mul-Π-Monoid (mul-Π-Monoid f g) h ＝
    mul-Π-Monoid f (mul-Π-Monoid g h)
  associative-mul-Π-Monoid = {!!}

  unit-Π-Monoid : type-Π-Monoid
  unit-Π-Monoid i = {!!}

  left-unit-law-mul-Π-Monoid :
    (f : type-Π-Monoid) → mul-Π-Monoid unit-Π-Monoid f ＝ f
  left-unit-law-mul-Π-Monoid f = {!!}

  right-unit-law-mul-Π-Monoid :
    (f : type-Π-Monoid) → mul-Π-Monoid f unit-Π-Monoid ＝ f
  right-unit-law-mul-Π-Monoid f = {!!}

  is-unital-Π-Monoid : is-unital-Semigroup semigroup-Π-Monoid
  pr1 is-unital-Π-Monoid = {!!}

  Π-Monoid : Monoid (l1 ⊔ l2)
  pr1 Π-Monoid = {!!}
```
