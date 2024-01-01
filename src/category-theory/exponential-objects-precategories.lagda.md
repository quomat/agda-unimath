# Exponential objects in precategories

```agda
module category-theory.exponential-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.products-in-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unique-existence
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a category with all binary products. For objects `x` and `y` in `C`,
an exponential (often denoted y^x) consists of:

- an object `e`
- a morphism `ev : hom (e × x) y` such that for every object `z` and morphism
  `f : hom (z × x) y` there exists a unique morphism `g : hom z e` such that
- `(g × id x) ∘ ev = {!!}

We say that `C` has all exponentials if there is a choice of an exponential for
each pair of objects.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (p : has-all-binary-products-Precategory C)
  where

  is-exponential-Precategory :
    (x y e : obj-Precategory C) →
    hom-Precategory C (object-product-Precategory C p e x) y →
    UU (l1 ⊔ l2)
  is-exponential-Precategory = {!!}

  exponential-Precategory :
    obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
  exponential-Precategory = {!!}

  has-all-exponentials-Precategory : UU (l1 ⊔ l2)
  has-all-exponentials-Precategory = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (p : has-all-binary-products-Precategory C)
  (t : has-all-exponentials-Precategory C p)
  (x y : obj-Precategory C)
  where

  object-exponential-Precategory : obj-Precategory C
  object-exponential-Precategory = {!!}

  eval-exponential-Precategory :
    hom-Precategory C
      ( object-product-Precategory C p object-exponential-Precategory x)
      ( y)
  eval-exponential-Precategory = {!!}

  module _
    (z : obj-Precategory C)
    (f : hom-Precategory C (object-product-Precategory C p z x) y)
    where

    morphism-into-exponential-Precategory :
      hom-Precategory C z object-exponential-Precategory
    morphism-into-exponential-Precategory = {!!}

    morphism-into-exponential-Precategory-comm :
      ( comp-hom-Precategory C
        ( eval-exponential-Precategory)
        ( map-product-Precategory C p
          ( morphism-into-exponential-Precategory)
          ( id-hom-Precategory C))) ＝
      ( f)
    morphism-into-exponential-Precategory-comm = {!!}

    is-unique-morphism-into-exponential-Precategory :
      ( g : hom-Precategory C z object-exponential-Precategory) →
      ( comp-hom-Precategory C
        ( eval-exponential-Precategory)
        ( map-product-Precategory C p g (id-hom-Precategory C)) ＝ f) →
      morphism-into-exponential-Precategory ＝ g
    is-unique-morphism-into-exponential-Precategory = {!!}
```
