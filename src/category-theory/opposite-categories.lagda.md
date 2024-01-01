# Opposite categories

```agda
module category-theory.opposite-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.involutions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a [category](category-theory.categories.md), its **opposite
category** `Cᵒᵖ` is given by reversing every morphism.

## Lemma

### The underlying precategory is a category if and only if the opposite is a category

```agda
abstract
  is-category-opposite-is-category-Precategory :
    {l1 l2 : Level} (C : Precategory l1 l2) →
    is-category-Precategory C →
    is-category-Precategory (opposite-Precategory C)
  is-category-opposite-is-category-Precategory C is-category-C x y = {!!}

abstract
  is-category-is-category-opposite-Precategory :
    {l1 l2 : Level} (C : Precategory l1 l2) →
    is-category-Precategory (opposite-Precategory C) →
    is-category-Precategory C
  is-category-is-category-opposite-Precategory C = {!!}
```

## Definitions

### The opposite category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  obj-opposite-Category : UU l1
  obj-opposite-Category = {!!}

  hom-set-opposite-Category : (x y : obj-opposite-Category) → Set l2
  hom-set-opposite-Category = {!!}

  hom-opposite-Category : (x y : obj-opposite-Category) → UU l2
  hom-opposite-Category = {!!}

  comp-hom-opposite-Category :
    {x y z : obj-opposite-Category} →
    hom-opposite-Category y z →
    hom-opposite-Category x y →
    hom-opposite-Category x z
  comp-hom-opposite-Category = {!!}

  associative-comp-hom-opposite-Category :
    {x y z w : obj-opposite-Category}
    (h : hom-opposite-Category z w)
    (g : hom-opposite-Category y z)
    (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category (comp-hom-opposite-Category h g) f ＝
    comp-hom-opposite-Category h (comp-hom-opposite-Category g f)
  associative-comp-hom-opposite-Category = {!!}

  inv-associative-comp-hom-opposite-Category :
    {x y z w : obj-opposite-Category}
    (h : hom-opposite-Category z w)
    (g : hom-opposite-Category y z)
    (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category h (comp-hom-opposite-Category g f) ＝
    comp-hom-opposite-Category (comp-hom-opposite-Category h g) f
  inv-associative-comp-hom-opposite-Category = {!!}

  id-hom-opposite-Category :
    {x : obj-opposite-Category} → hom-opposite-Category x x
  id-hom-opposite-Category = {!!}

  left-unit-law-comp-hom-opposite-Category :
    {x y : obj-opposite-Category}
    (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category id-hom-opposite-Category f ＝ f
  left-unit-law-comp-hom-opposite-Category = {!!}

  right-unit-law-comp-hom-opposite-Category :
    {x y : obj-opposite-Category} (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category f id-hom-opposite-Category ＝ f
  right-unit-law-comp-hom-opposite-Category = {!!}

  precategory-opposite-Category : Precategory l1 l2
  precategory-opposite-Category = {!!}

  opposite-Category : Category l1 l2
  pr1 opposite-Category = {!!}
```

## Properties

### The opposite construction is an involution on the type of categories

```agda
is-involution-opposite-Category :
  {l1 l2 : Level} → is-involution (opposite-Category {l1} {l2})
is-involution-opposite-Category C = {!!}

involution-opposite-Category :
  (l1 l2 : Level) → involution (Category l1 l2)
pr1 (involution-opposite-Category l1 l2) = {!!}
pr2 (involution-opposite-Category l1 l2) = {!!}

is-equiv-opposite-Category :
  {l1 l2 : Level} → is-equiv (opposite-Category {l1} {l2})
is-equiv-opposite-Category = {!!}

equiv-opposite-Category :
  (l1 l2 : Level) → Category l1 l2 ≃ Category l1 l2
equiv-opposite-Category l1 l2 = {!!}
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
