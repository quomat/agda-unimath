# The initial category

```agda
module category-theory.initial-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-precategories
open import category-theory.gaunt-categories
open import category-theory.indiscrete-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories
open import category-theory.strict-categories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **initial category** is the [category](category-theory.categories.md) with
no objects.

## Definition

### The objects and hom-sets of the initial category

```agda
obj-initial-Category : UU lzero
obj-initial-Category = {!!}

hom-set-initial-Category :
  obj-initial-Category → obj-initial-Category → Set lzero
hom-set-initial-Category = {!!}

hom-initial-Category :
  obj-initial-Category → obj-initial-Category → UU lzero
hom-initial-Category = {!!}
```

### The underlying precategory of the initial category

```agda
comp-hom-initial-Category = {!!}

associative-comp-hom-initial-Category = {!!}

associative-composition-operation-initial-Category = {!!}

id-hom-initial-Category = {!!}

left-unit-law-comp-hom-initial-Category = {!!}

right-unit-law-comp-hom-initial-Category = {!!}

is-unital-composition-operation-initial-Category = {!!}

initial-Precategory : Precategory lzero lzero
initial-Precategory = {!!}
```

### The initial category

```agda
is-category-initial-Category :
  is-category-Precategory initial-Precategory
is-category-initial-Category = {!!}
pr2 initial-Category = {!!}
```

### The initial preunivalent category

```agda
is-preunivalent-initial-Category :
  is-preunivalent-Precategory initial-Precategory
is-preunivalent-initial-Category = {!!}
```

### The initial strict category

```agda
is-strict-category-initial-Category :
  is-strict-category-Precategory initial-Precategory
is-strict-category-initial-Category = {!!}
pr2 initial-Strict-Category = {!!}
```

### The initial gaunt category

```agda
is-gaunt-initial-Category : is-gaunt-Category initial-Category
is-gaunt-initial-Category ()

initial-Gaunt-Category : Gaunt-Category lzero lzero
pr1 initial-Gaunt-Category = {!!}
pr2 initial-Gaunt-Category = {!!}
```

## Properties

### The initial category is initial

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  initial-functor-Precategory : functor-Precategory initial-Precategory C
  pr1 initial-functor-Precategory ()
  pr1 (pr2 initial-functor-Precategory) {()}
  pr1 (pr2 (pr2 initial-functor-Precategory)) {()}
  pr2 (pr2 (pr2 initial-functor-Precategory)) ()

  abstract
    uniqueness-initial-functor-Precategory :
      (F : functor-Precategory initial-Precategory C) →
      initial-functor-Precategory ＝ F
    uniqueness-initial-functor-Precategory = {!!}

  abstract
    is-contr-functor-initial-Precategory :
      is-contr (functor-Precategory initial-Precategory C)
    is-contr-functor-initial-Precategory = {!!}
```

## See also

- [The terminal category](category-theory.terminal-category.md)

## External links

- [empty category](https://ncatlab.org/nlab/show/empty+category) at $n$Lab

A wikidata identifier was not available for this concept.
