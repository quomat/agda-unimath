# Products of precategories

```agda
module category-theory.products-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The **product** of two [precategories](category-theory.precategories.md) `C` and
`D` has as objects pairs `(x , y)`, for `x` in `obj-Precategory C` and `y` in
`obj-Precategory D`; and has a morphism `Hom (x , y) (x' , y)` for each pair of
morphisms `f : x → x'` and `g : y → y'`. Composition of morphisms is given by
composing each entry.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  prod-Precategory :
    Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 prod-Precategory = {!!}
```
