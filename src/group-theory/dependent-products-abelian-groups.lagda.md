# Dependent products of abelian groups

```agda
module group-theory.dependent-products-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.dependent-products-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

Given a family of abelian groups `Aᵢ` indexed by `i : I`, the dependent product
`Π(i : I), Aᵢ` is an abelian group consisting of dependent functions taking
`i : I` to an element of the underlying type of `Aᵢ`. The multiplicative
operation and the unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A : I → Ab l2)
  where

  group-Π-Ab : Group (l1 ⊔ l2)
  group-Π-Ab = {!!}

  semigroup-Π-Ab : Semigroup (l1 ⊔ l2)
  semigroup-Π-Ab = {!!}

  set-Π-Ab : Set (l1 ⊔ l2)
  set-Π-Ab = {!!}

  type-Π-Ab : UU (l1 ⊔ l2)
  type-Π-Ab = {!!}

  add-Π-Ab : (f g : type-Π-Ab) → type-Π-Ab
  add-Π-Ab = {!!}

  associative-add-Π-Ab :
    (f g h : type-Π-Ab) →
    add-Π-Ab (add-Π-Ab f g) h ＝ add-Π-Ab f (add-Π-Ab g h)
  associative-add-Π-Ab = {!!}

  zero-Π-Ab : type-Π-Ab
  zero-Π-Ab = {!!}

  left-unit-law-add-Π-Ab : (f : type-Π-Ab) → add-Π-Ab zero-Π-Ab f ＝ f
  left-unit-law-add-Π-Ab = {!!}

  right-unit-law-add-Π-Ab : (f : type-Π-Ab) → add-Π-Ab f zero-Π-Ab ＝ f
  right-unit-law-add-Π-Ab = {!!}

  is-unital-Π-Ab : is-unital-Semigroup semigroup-Π-Ab
  is-unital-Π-Ab = {!!}

  monoid-Π-Ab : Monoid (l1 ⊔ l2)
  monoid-Π-Ab = {!!}

  neg-Π-Ab : type-Π-Ab → type-Π-Ab
  neg-Π-Ab = {!!}

  left-inverse-law-add-Π-Ab :
    (f : type-Π-Ab) → add-Π-Ab (neg-Π-Ab f) f ＝ zero-Π-Ab
  left-inverse-law-add-Π-Ab = {!!}

  right-inverse-law-add-Π-Ab :
    (f : type-Π-Ab) → add-Π-Ab f (neg-Π-Ab f) ＝ zero-Π-Ab
  right-inverse-law-add-Π-Ab = {!!}

  is-group-Π-Ab : is-group semigroup-Π-Ab
  is-group-Π-Ab = {!!}

  commutative-add-Π-Ab :
    (f g : type-Π-Ab) → add-Π-Ab f g ＝ add-Π-Ab g f
  commutative-add-Π-Ab f g = {!!}

  Π-Ab : Ab (l1 ⊔ l2)
  pr1 Π-Ab = {!!}
```
