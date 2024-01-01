# Strict categories

```agda
module category-theory.strict-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **strict category** is a [precategory](category-theory.precategories.md) for
which the type of objects form a [set](foundation-core.sets.md). Such categories
are the set-theoretic analogue to
[(univalent) categories](category-theory.categories.md), and have the defect
that strict categorical constructions may generally fail to be invariant under
equivalences.

## Definitions

### The predicate on precategories of being a strict category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-strict-category-prop-Precategory : Prop l1
  is-strict-category-prop-Precategory = {!!}

  is-strict-category-Precategory : UU l1
  is-strict-category-Precategory = {!!}
```

### The predicate on preunivalent categories of being a strict category

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-strict-category-prop-Preunivalent-Category : Prop l1
  is-strict-category-prop-Preunivalent-Category = {!!}

  is-strict-category-Preunivalent-Category : UU l1
  is-strict-category-Preunivalent-Category = {!!}
```

### The predicate on categories of being a strict category

We note that [(univalent) categories](category-theory.categories.md) that are
strict form a very restricted class of strict categories where every
[isomorphism](category-theory.isomorphisms-in-categories.md)-set is a
[proposition](foundation-core.propositions.md). Such a category is called
[gaunt](category-theory.gaunt-categories.md).

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-strict-category-prop-Category : Prop l1
  is-strict-category-prop-Category = {!!}

  is-strict-category-Category : UU l1
  is-strict-category-Category = {!!}
```

### The type of strict categories

```agda
Strict-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strict-Category l1 l2 = {!!}

module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  precategory-Strict-Category : Precategory l1 l2
  precategory-Strict-Category = {!!}

  obj-Strict-Category : UU l1
  obj-Strict-Category = {!!}

  is-set-obj-Strict-Category : is-set obj-Strict-Category
  is-set-obj-Strict-Category = {!!}

  hom-set-Strict-Category : obj-Strict-Category → obj-Strict-Category → Set l2
  hom-set-Strict-Category = {!!}

  hom-Strict-Category : obj-Strict-Category → obj-Strict-Category → UU l2
  hom-Strict-Category = {!!}

  is-set-hom-Strict-Category :
    (x y : obj-Strict-Category) → is-set (hom-Strict-Category x y)
  is-set-hom-Strict-Category = {!!}

  comp-hom-Strict-Category :
    {x y z : obj-Strict-Category} →
    hom-Strict-Category y z → hom-Strict-Category x y → hom-Strict-Category x z
  comp-hom-Strict-Category = {!!}

  associative-comp-hom-Strict-Category :
    {x y z w : obj-Strict-Category}
    (h : hom-Strict-Category z w)
    (g : hom-Strict-Category y z)
    (f : hom-Strict-Category x y) →
    comp-hom-Strict-Category (comp-hom-Strict-Category h g) f ＝
    comp-hom-Strict-Category h (comp-hom-Strict-Category g f)
  associative-comp-hom-Strict-Category = {!!}

  associative-composition-operation-Strict-Category :
    associative-composition-operation-binary-family-Set hom-set-Strict-Category
  associative-composition-operation-Strict-Category = {!!}

  id-hom-Strict-Category : {x : obj-Strict-Category} → hom-Strict-Category x x
  id-hom-Strict-Category = {!!}

  left-unit-law-comp-hom-Strict-Category :
    {x y : obj-Strict-Category} (f : hom-Strict-Category x y) →
    comp-hom-Strict-Category id-hom-Strict-Category f ＝ f
  left-unit-law-comp-hom-Strict-Category = {!!}

  right-unit-law-comp-hom-Strict-Category :
    {x y : obj-Strict-Category} (f : hom-Strict-Category x y) →
    comp-hom-Strict-Category f id-hom-Strict-Category ＝ f
  right-unit-law-comp-hom-Strict-Category = {!!}

  is-unital-composition-operation-Strict-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Strict-Category
      comp-hom-Strict-Category
  is-unital-composition-operation-Strict-Category = {!!}

  is-strict-category-Strict-Category :
    is-strict-category-Precategory precategory-Strict-Category
  is-strict-category-Strict-Category = {!!}
```

### The underlying nonunital precategory of a strict category

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  nonunital-precategory-Strict-Category : Nonunital-Precategory l1 l2
  nonunital-precategory-Strict-Category = {!!}
```

### The underlying preunivalent category of a strict category

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  abstract
    is-preunivalent-Strict-Category :
      is-preunivalent-Precategory (precategory-Strict-Category C)
    is-preunivalent-Strict-Category x y = {!!}

  preunivalent-category-Strict-Category : Preunivalent-Category l1 l2
  pr1 preunivalent-category-Strict-Category = {!!}
```

### The total hom-set of a strict category

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  total-hom-Strict-Category : UU (l1 ⊔ l2)
  total-hom-Strict-Category = {!!}

  obj-total-hom-Strict-Category :
    total-hom-Strict-Category → obj-Strict-Category C × obj-Strict-Category C
  obj-total-hom-Strict-Category = {!!}

  is-set-total-hom-Strict-Category :
    is-set total-hom-Strict-Category
  is-set-total-hom-Strict-Category = {!!}

  total-hom-set-Strict-Category : Set (l1 ⊔ l2)
  total-hom-set-Strict-Category = {!!}
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  hom-eq-Strict-Category :
    (x y : obj-Strict-Category C) → x ＝ y → hom-Strict-Category C x y
  hom-eq-Strict-Category = {!!}

  hom-inv-eq-Strict-Category :
    (x y : obj-Strict-Category C) → x ＝ y → hom-Strict-Category C y x
  hom-inv-eq-Strict-Category = {!!}
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Strict-Category :
  {l1 l2 : Level} (C : Strict-Category l1 l2) {x y : obj-Strict-Category C}
  (f : hom-Strict-Category C x y) (z : obj-Strict-Category C) →
  hom-Strict-Category C y z → hom-Strict-Category C x z
precomp-hom-Strict-Category C = {!!}

postcomp-hom-Strict-Category :
  {l1 l2 : Level} (C : Strict-Category l1 l2) {x y : obj-Strict-Category C}
  (f : hom-Strict-Category C x y) (z : obj-Strict-Category C) →
  hom-Strict-Category C z x → hom-Strict-Category C z y
postcomp-hom-Strict-Category C = {!!}
```

## See also

- [Preunivalent categories](category-theory.preunivalent-categories.md) for the
  common generalization of (univalent) categories and strict categories.
- [Gaunt categories](category-theory.gaunt-categories.md) for the common
  intersection of (univalent) categories and strict categories.

## External links

- [Strict Precategories](https://1lab.dev/Cat.Strict.html#strict-precategories)
  at 1lab
- [strict category](https://ncatlab.org/nlab/show/strict+category) at $n$Lab
- [Category (mathematics)](<https://en.wikipedia.org/wiki/Category_(mathematics)>)
  at Wikipedia
