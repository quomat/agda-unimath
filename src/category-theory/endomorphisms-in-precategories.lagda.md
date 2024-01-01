# Endomorphisms in precategories

```agda
module category-theory.endomorphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Definition

### The monoid of endomorphisms on an object in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  type-endo-Precategory : UU l2
  type-endo-Precategory = {!!}

  comp-endo-Precategory :
    type-endo-Precategory → type-endo-Precategory → type-endo-Precategory
  comp-endo-Precategory g f = {!!}

  id-endo-Precategory : type-endo-Precategory
  id-endo-Precategory = {!!}

  associative-comp-endo-Precategory :
    (h g f : type-endo-Precategory) →
    ( comp-endo-Precategory (comp-endo-Precategory h g) f) ＝
    ( comp-endo-Precategory h (comp-endo-Precategory g f))
  associative-comp-endo-Precategory = {!!}

  left-unit-law-comp-endo-Precategory :
    (f : type-endo-Precategory) →
    comp-endo-Precategory id-endo-Precategory f ＝ f
  left-unit-law-comp-endo-Precategory = {!!}

  right-unit-law-comp-endo-Precategory :
    (f : type-endo-Precategory) →
    comp-endo-Precategory f id-endo-Precategory ＝ f
  right-unit-law-comp-endo-Precategory = {!!}

  set-endo-Precategory : Set l2
  set-endo-Precategory = {!!}

  semigroup-endo-Precategory : Semigroup l2
  pr1 semigroup-endo-Precategory = {!!}

  monoid-endo-Precategory : Monoid l2
  pr1 monoid-endo-Precategory = {!!}
```
