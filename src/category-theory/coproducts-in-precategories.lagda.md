# Coproducts in precategories

```agda
module category-theory.coproducts-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.unique-existence
open import foundation.universe-levels
```

</details>

## Idea

We manually dualize the definition of products in precategories for convenience.
See the documentation in that file for further information.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-coproduct-Precategory :
    (x y p : obj-Precategory C) →
    hom-Precategory C x p → hom-Precategory C y p → UU (l1 ⊔ l2)
  is-coproduct-Precategory = {!!}

  coproduct-Precategory : obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
  coproduct-Precategory x y = {!!}

  has-all-binary-coproducts : UU (l1 ⊔ l2)
  has-all-binary-coproducts = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2) (t : has-all-binary-coproducts C)
  where

  object-coproduct-Precategory :
    obj-Precategory C → obj-Precategory C → obj-Precategory C
  object-coproduct-Precategory = {!!}

  inl-coproduct-Precategory :
    (x y : obj-Precategory C) →
    hom-Precategory C x (object-coproduct-Precategory x y)
  inl-coproduct-Precategory = {!!}

  inr-coproduct-Precategory :
    (x y : obj-Precategory C) →
    hom-Precategory C y (object-coproduct-Precategory x y)
  inr-coproduct-Precategory = {!!}

  module _
    (x y z : obj-Precategory C)
    (f : hom-Precategory C x z)
    (g : hom-Precategory C y z)
    where

    morphism-out-of-coproduct-Precategory :
      hom-Precategory C (object-coproduct-Precategory x y) z
    morphism-out-of-coproduct-Precategory = {!!}

    morphism-out-of-coproduct-Precategory-comm-inl :
      comp-hom-Precategory
        ( C)
        ( morphism-out-of-coproduct-Precategory)
        ( inl-coproduct-Precategory x y) ＝ f
    morphism-out-of-coproduct-Precategory-comm-inl = {!!}

    morphism-out-of-coproduct-Precategory-comm-inr :
      comp-hom-Precategory
        ( C)
        ( morphism-out-of-coproduct-Precategory)
        ( inr-coproduct-Precategory x y) ＝ g
    morphism-out-of-coproduct-Precategory-comm-inr = {!!}

    is-unique-morphism-out-of-coproduct-Precategory :
      (h : hom-Precategory C (object-coproduct-Precategory x y) z) →
      comp-hom-Precategory C h (inl-coproduct-Precategory x y) ＝ f →
      comp-hom-Precategory C h (inr-coproduct-Precategory x y) ＝ g →
      morphism-out-of-coproduct-Precategory ＝ h
    is-unique-morphism-out-of-coproduct-Precategory = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y p : obj-Precategory C)
  (l : hom-Precategory C x p)
  (r : hom-Precategory C y p)
  where

  is-prop-is-coproduct-Precategory :
    is-prop (is-coproduct-Precategory C x y p l r)
  is-prop-is-coproduct-Precategory = {!!}

  is-coproduct-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-coproduct-prop-Precategory = {!!}
```

## Properties

### Coproducts of morphisms

If `C` has all binary coproducts then for any pair of morphisms `f : hom x₁ y₁`
and `g : hom x₂ y₂` we can construct a morphism
`f + g : hom (x₁ + x₂) (y₁ + y₂)`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-binary-coproducts C)
  {x₁ x₂ y₁ y₂ : obj-Precategory C}
  (f : hom-Precategory C x₁ y₁)
  (g : hom-Precategory C x₂ y₂)
  where

  map-coproduct-Precategory :
    hom-Precategory C
      (object-coproduct-Precategory C t x₁ x₂)
      (object-coproduct-Precategory C t y₁ y₂)
  map-coproduct-Precategory = {!!}
```
