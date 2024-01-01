# Dependent products of wild monoids

```agda
module structured-types.dependent-products-wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.dependent-products-h-spaces
open import structured-types.h-spaces
open import structured-types.pointed-types
open import structured-types.wild-monoids
```

</details>

## Idea

Given a family of [wild monoids](structured-types.wild-monoids.md) `Mᵢ` indexed
by `i : I`, the dependent product `Π(i : I), Mᵢ` is a wild monoid consisting of
dependent functions taking `i : I` to an element of the underlying type of `Mᵢ`.
Every component of the structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → Wild-Monoid l2)
  where

  h-space-Π-Wild-Monoid : H-Space (l1 ⊔ l2)
  h-space-Π-Wild-Monoid = {!!}

  pointed-type-Π-Wild-Monoid : Pointed-Type (l1 ⊔ l2)
  pointed-type-Π-Wild-Monoid = {!!}

  type-Π-Wild-Monoid : UU (l1 ⊔ l2)
  type-Π-Wild-Monoid = {!!}

  unit-Π-Wild-Monoid : type-Π-Wild-Monoid
  unit-Π-Wild-Monoid = {!!}

  mul-Π-Wild-Monoid :
    type-Π-Wild-Monoid → type-Π-Wild-Monoid → type-Π-Wild-Monoid
  mul-Π-Wild-Monoid = {!!}

  left-unit-law-mul-Π-Wild-Monoid :
    (f : type-Π-Wild-Monoid) → (mul-Π-Wild-Monoid (unit-Π-Wild-Monoid) f) ＝ f
  left-unit-law-mul-Π-Wild-Monoid = {!!}

  right-unit-law-mul-Π-Wild-Monoid :
    (f : type-Π-Wild-Monoid) → (mul-Π-Wild-Monoid f (unit-Π-Wild-Monoid)) ＝ f
  right-unit-law-mul-Π-Wild-Monoid = {!!}

  associator-Π-Wild-Monoid :
    associator-H-Space h-space-Π-Wild-Monoid
  associator-Π-Wild-Monoid = {!!}

  unital-associator-Π-Wild-Monoid :
    unital-associator h-space-Π-Wild-Monoid
  unital-associator-Π-Wild-Monoid = {!!}

  Π-Wild-Monoid : Wild-Monoid (l1 ⊔ l2)
  Π-Wild-Monoid = {!!}
```
