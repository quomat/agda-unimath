# Opposite preunivalent categories

```agda
module category-theory.opposite-preunivalent-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories

open import foundation.dependent-pair-types
open import foundation.embeddings
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

Let `C` be a
[preunivalent category](category-theory.preunivalent-categories.md), its
**opposite preunivalent category** `Cᵒᵖ` is given by reversing every morphism.

## Lemma

### A precategory is preunivalent if and only if the opposite is preunivalent

```agda
abstract
  is-preunivalent-opposite-is-preunivalent-Precategory :
    {l1 l2 : Level} (C : Precategory l1 l2) →
    is-preunivalent-Precategory C →
    is-preunivalent-Precategory (opposite-Precategory C)
  is-preunivalent-opposite-is-preunivalent-Precategory C is-preunivalent-C x y = {!!}

abstract
  is-preunivalent-is-preunivalent-opposite-Precategory :
    {l1 l2 : Level} (C : Precategory l1 l2) →
    is-preunivalent-Precategory (opposite-Precategory C) →
    is-preunivalent-Precategory C
  is-preunivalent-is-preunivalent-opposite-Precategory C = {!!}
```

## Definitions

### The opposite preunivalent category

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  obj-opposite-Preunivalent-Category : UU l1
  obj-opposite-Preunivalent-Category = {!!}

  hom-set-opposite-Preunivalent-Category :
    (x y : obj-opposite-Preunivalent-Category) → Set l2
  hom-set-opposite-Preunivalent-Category = {!!}

  hom-opposite-Preunivalent-Category :
    (x y : obj-opposite-Preunivalent-Category) → UU l2
  hom-opposite-Preunivalent-Category = {!!}

  comp-hom-opposite-Preunivalent-Category :
    {x y z : obj-opposite-Preunivalent-Category} →
    hom-opposite-Preunivalent-Category y z →
    hom-opposite-Preunivalent-Category x y →
    hom-opposite-Preunivalent-Category x z
  comp-hom-opposite-Preunivalent-Category = {!!}

  associative-comp-hom-opposite-Preunivalent-Category :
    {x y z w : obj-opposite-Preunivalent-Category}
    (h : hom-opposite-Preunivalent-Category z w)
    (g : hom-opposite-Preunivalent-Category y z)
    (f : hom-opposite-Preunivalent-Category x y) →
    comp-hom-opposite-Preunivalent-Category
      ( comp-hom-opposite-Preunivalent-Category h g)
      ( f) ＝
    comp-hom-opposite-Preunivalent-Category
      ( h)
      ( comp-hom-opposite-Preunivalent-Category g f)
  associative-comp-hom-opposite-Preunivalent-Category = {!!}

  inv-associative-comp-hom-opposite-Preunivalent-Category :
    {x y z w : obj-opposite-Preunivalent-Category}
    (h : hom-opposite-Preunivalent-Category z w)
    (g : hom-opposite-Preunivalent-Category y z)
    (f : hom-opposite-Preunivalent-Category x y) →
    comp-hom-opposite-Preunivalent-Category
      ( h)
      ( comp-hom-opposite-Preunivalent-Category g f) ＝
    comp-hom-opposite-Preunivalent-Category
      ( comp-hom-opposite-Preunivalent-Category h g)
      ( f)
  inv-associative-comp-hom-opposite-Preunivalent-Category = {!!}

  id-hom-opposite-Preunivalent-Category :
    {x : obj-opposite-Preunivalent-Category} →
    hom-opposite-Preunivalent-Category x x
  id-hom-opposite-Preunivalent-Category = {!!}

  left-unit-law-comp-hom-opposite-Preunivalent-Category :
    {x y : obj-opposite-Preunivalent-Category}
    (f : hom-opposite-Preunivalent-Category x y) →
    comp-hom-opposite-Preunivalent-Category
      ( id-hom-opposite-Preunivalent-Category)
      ( f) ＝
    f
  left-unit-law-comp-hom-opposite-Preunivalent-Category = {!!}

  right-unit-law-comp-hom-opposite-Preunivalent-Category :
    {x y : obj-opposite-Preunivalent-Category}
    (f : hom-opposite-Preunivalent-Category x y) →
    comp-hom-opposite-Preunivalent-Category
      ( f) (id-hom-opposite-Preunivalent-Category) ＝
    ( f)
  right-unit-law-comp-hom-opposite-Preunivalent-Category = {!!}

  precategory-opposite-Preunivalent-Category : Precategory l1 l2
  precategory-opposite-Preunivalent-Category = {!!}

  opposite-Preunivalent-Category : Preunivalent-Category l1 l2
  pr1 opposite-Preunivalent-Category = {!!}
```

## Properties

### The opposite construction is an involution on the type of preunivalent categories

```agda
is-involution-opposite-Preunivalent-Category :
  {l1 l2 : Level} → is-involution (opposite-Preunivalent-Category {l1} {l2})
is-involution-opposite-Preunivalent-Category C = {!!}

involution-opposite-Preunivalent-Category :
  (l1 l2 : Level) → involution (Preunivalent-Category l1 l2)
pr1 (involution-opposite-Preunivalent-Category l1 l2) = {!!}
pr2 (involution-opposite-Preunivalent-Category l1 l2) = {!!}

is-equiv-opposite-Preunivalent-Category :
  {l1 l2 : Level} → is-equiv (opposite-Preunivalent-Category {l1} {l2})
is-equiv-opposite-Preunivalent-Category = {!!}

equiv-opposite-Preunivalent-Category :
  (l1 l2 : Level) → Preunivalent-Category l1 l2 ≃ Preunivalent-Category l1 l2
equiv-opposite-Preunivalent-Category l1 l2 = {!!}
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
