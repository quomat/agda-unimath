# Full functors between precategories

```agda
module category-theory.full-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-maps-precategories
open import category-theory.functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **full** if
it's [surjective](foundation.surjective-maps.md) on
hom-[sets](foundation-core.sets.md).

## Definition

### The predicate of being full on functors between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-full-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-full-functor-Precategory = {!!}

  is-prop-is-full-functor-Precategory :
    is-prop is-full-functor-Precategory
  is-prop-is-full-functor-Precategory = {!!}

  is-full-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-full-prop-functor-Precategory = {!!}
```

### The type of full functors between two precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  full-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  full-functor-Precategory = {!!}

  functor-full-functor-Precategory :
    full-functor-Precategory → functor-Precategory C D
  functor-full-functor-Precategory = {!!}

  is-full-full-functor-Precategory :
    (F : full-functor-Precategory) →
    is-full-functor-Precategory C D (functor-full-functor-Precategory F)
  is-full-full-functor-Precategory = {!!}

  obj-full-functor-Precategory :
    full-functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-full-functor-Precategory = {!!}

  hom-full-functor-Precategory :
    (F : full-functor-Precategory) {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-full-functor-Precategory F x)
      ( obj-full-functor-Precategory F y)
  hom-full-functor-Precategory = {!!}
```
