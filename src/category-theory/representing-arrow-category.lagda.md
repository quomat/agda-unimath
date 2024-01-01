# The representing arrow category

```agda
module category-theory.representing-arrow-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **representing arrow** is the [category](category-theory.categories.md) that
[represents](category-theory.representable-functors-categories.md) arrows in a
([pre-](category-theory.precategories.md))category. We model it after
implication on the [booleans](foundation.booleans.md).

## Definition

### The objects and hom-sets of the representing arrow

```agda
obj-representing-arrow-Category : UU lzero
obj-representing-arrow-Category = {!!}

hom-set-representing-arrow-Category :
  obj-representing-arrow-Category → obj-representing-arrow-Category → Set lzero
hom-set-representing-arrow-Category = {!!}

hom-representing-arrow-Category :
  obj-representing-arrow-Category → obj-representing-arrow-Category → UU lzero
hom-representing-arrow-Category = {!!}
```

### The underlying precategory of the representing arrow

```agda
comp-hom-representing-arrow-Category :
  {x y z : obj-representing-arrow-Category} →
  hom-representing-arrow-Category y z →
  hom-representing-arrow-Category x y →
  hom-representing-arrow-Category x z
comp-hom-representing-arrow-Category = {!!}

associative-comp-hom-representing-arrow-Category :
  {x y z w : obj-representing-arrow-Category} →
  (h : hom-representing-arrow-Category z w)
  (g : hom-representing-arrow-Category y z)
  (f : hom-representing-arrow-Category x y) →
  ( comp-hom-representing-arrow-Category
    { x} (comp-hom-representing-arrow-Category {y} h g) f) ＝
  ( comp-hom-representing-arrow-Category
    { x} h (comp-hom-representing-arrow-Category {x} g f))
associative-comp-hom-representing-arrow-Category = {!!}
associative-comp-hom-representing-arrow-Category {false} h g f = {!!}

inv-associative-comp-hom-representing-arrow-Category :
  {x y z w : obj-representing-arrow-Category} →
  (h : hom-representing-arrow-Category z w)
  (g : hom-representing-arrow-Category y z)
  (f : hom-representing-arrow-Category x y) →
  ( comp-hom-representing-arrow-Category
    { x} h (comp-hom-representing-arrow-Category {x} g f)) ＝
  ( comp-hom-representing-arrow-Category
    { x} (comp-hom-representing-arrow-Category {y} h g) f)
inv-associative-comp-hom-representing-arrow-Category = {!!}
inv-associative-comp-hom-representing-arrow-Category {false} h g f = {!!}

associative-composition-operation-representing-arrow-Category :
  associative-composition-operation-binary-family-Set
    ( hom-set-representing-arrow-Category)
associative-composition-operation-representing-arrow-Category = {!!}

id-hom-representing-arrow-Category :
  {x : obj-representing-arrow-Category} → hom-representing-arrow-Category x x
id-hom-representing-arrow-Category = {!!}

left-unit-law-comp-hom-representing-arrow-Category :
  {x y : obj-representing-arrow-Category} →
  (f : hom-representing-arrow-Category x y) →
  comp-hom-representing-arrow-Category
    { x} (id-hom-representing-arrow-Category {y}) f ＝
  f
left-unit-law-comp-hom-representing-arrow-Category = {!!}

right-unit-law-comp-hom-representing-arrow-Category :
  {x y : obj-representing-arrow-Category} →
  (f : hom-representing-arrow-Category x y) →
  comp-hom-representing-arrow-Category
    { x} f (id-hom-representing-arrow-Category {x}) ＝
  f
right-unit-law-comp-hom-representing-arrow-Category = {!!}

is-unital-composition-operation-representing-arrow-Category :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-representing-arrow-Category)
    ( λ {x} {y} {z} → comp-hom-representing-arrow-Category {x} {y} {z})
is-unital-composition-operation-representing-arrow-Category = {!!}
pr1 (pr2 is-unital-composition-operation-representing-arrow-Category) = {!!}
pr2 (pr2 is-unital-composition-operation-representing-arrow-Category) = {!!}

representing-arrow-Precategory : Precategory lzero lzero
representing-arrow-Precategory = {!!}
pr1 (pr2 representing-arrow-Precategory) = {!!}
pr1 (pr2 (pr2 representing-arrow-Precategory)) = {!!}
pr2 (pr2 (pr2 representing-arrow-Precategory)) = {!!}
```

### The representing arrow category

```agda
is-category-representing-arrow-Category :
  is-category-Precategory representing-arrow-Precategory
is-category-representing-arrow-Category = {!!}

representing-arrow-Category : Category lzero lzero
representing-arrow-Category = {!!}
pr2 representing-arrow-Category = {!!}
```

## Properties

### The representing arrow represents arrows in a category

This remains to be formalized.

## External links

- [Interval category](https://1lab.dev/Cat.Instances.Shape.Interval.html#interval-category)
  at 1lab
- [interval category](https://ncatlab.org/nlab/show/interval+category) at $n$Lab

A wikidata identifier was not available for this concept.
