# Pullbacks in precategories

```agda
module category-theory.pullbacks-in-precategories where
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

A pullback of two morphisms `f : hom y x` and `g : hom z x` in a category `C`
consists of:

- an object `w`
- morphisms `p₁ : hom w y` and `p₂ : hom w z` such that
- `f ∘ p₁ = {!!}
- `p₁ ∘ h = {!!}
- `p₂ ∘ h = {!!}

We say that `C` has all pullbacks if there is a choice of a pullback for each
object `x` and pair of morphisms into `x` in `C`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pullback-Precategory :
    (x y z : obj-Precategory C) →
    (f : hom-Precategory C y x) →
    (g : hom-Precategory C z x) →
    (w : obj-Precategory C) →
    (p₁ : hom-Precategory C w y) →
    (p₂ : hom-Precategory C w z) →
    comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂ →
    UU (l1 ⊔ l2)
  is-pullback-Precategory = {!!}

  pullback-Precategory :
    (x y z : obj-Precategory C) →
    hom-Precategory C y x →
    hom-Precategory C z x →
    UU (l1 ⊔ l2)
  pullback-Precategory = {!!}

  has-all-pullback-Precategory : UU (l1 ⊔ l2)
  has-all-pullback-Precategory = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-pullback-Precategory C)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C y x)
  (g : hom-Precategory C z x)
  where

  object-pullback-Precategory : obj-Precategory C
  object-pullback-Precategory = {!!}

  pr1-pullback-Precategory :
    hom-Precategory C object-pullback-Precategory y
  pr1-pullback-Precategory = {!!}

  pr2-pullback-Precategory :
    hom-Precategory C object-pullback-Precategory z
  pr2-pullback-Precategory = {!!}

  pullback-square-Precategory-comm :
    comp-hom-Precategory C f pr1-pullback-Precategory ＝
    comp-hom-Precategory C g pr2-pullback-Precategory
  pullback-square-Precategory-comm = {!!}

  module _
    (w' : obj-Precategory C)
    (p₁' : hom-Precategory C w' y)
    (p₂' : hom-Precategory C w' z)
    (α : comp-hom-Precategory C f p₁' ＝ comp-hom-Precategory C g p₂')
    where

    morphism-into-pullback-Precategory :
      hom-Precategory C w' object-pullback-Precategory
    morphism-into-pullback-Precategory = {!!}

    morphism-into-pullback-comm-pr1 :
      comp-hom-Precategory C
        pr1-pullback-Precategory
        morphism-into-pullback-Precategory ＝
      p₁'
    morphism-into-pullback-comm-pr1 = {!!}

    morphism-into-pullback-comm-pr2 :
      comp-hom-Precategory C
        pr2-pullback-Precategory
        morphism-into-pullback-Precategory ＝
      p₂'
    morphism-into-pullback-comm-pr2 = {!!}

    is-unique-morphism-into-pullback-Precategory :
      (h' : hom-Precategory C w' object-pullback-Precategory) →
      comp-hom-Precategory C pr1-pullback-Precategory h' ＝ p₁' →
      comp-hom-Precategory C pr2-pullback-Precategory h' ＝ p₂' →
      morphism-into-pullback-Precategory ＝ h'
    is-unique-morphism-into-pullback-Precategory = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C y x)
  (g : hom-Precategory C z x)
  (w : obj-Precategory C)
  (p₁ : hom-Precategory C w y)
  (p₂ : hom-Precategory C w z)
  (α : comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂)
  where

  is-prop-is-pullback-Precategory :
    is-prop (is-pullback-Precategory C x y z f g w p₁ p₂ α)
  is-prop-is-pullback-Precategory = {!!}

  is-pullback-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-pullback-prop-Precategory = {!!}
```
