# Gaunt categories

```agda
module category-theory.gaunt-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphism-induction-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories
open import category-theory.rigid-objects-categories
open import category-theory.strict-categories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **gaunt category** is a [category](category-theory.categories.md) such that
one of the following equivalent conditions hold:

1. The
   [isomorphism](category-theory.isomorphisms-in-categories.md)-[sets](foundation-core.sets.md)
   are [propositions](foundation-core.propositions.md).
2. The objects form a set.
3. Every object is [rigid](category-theory.rigid-objects-categories.md), meaning
   its [automorphism group](group-theory.automorphism-groups.md) is
   [trivial](group-theory.trivial-groups.md).

Gaunt categories forms the common intersection of (univalent) categories and
[strict categories](category-theory.strict-categories.md). We have the following
diagram relating the different notions of "category":

```text
        Gaunt categories
              /   \
            /       \
          v           v
  Categories         Strict categories
          \           /
            \       /
              v   v
      Preunivalent categories
                |
                |
                v
          Precategories
```

## Definitions

### The predicate on precategories that there is at most one isomorphism between any two objects

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-prop-iso-prop-Precategory : Prop (l1 ⊔ l2)
  is-prop-iso-prop-Precategory = {!!}

  is-prop-iso-Precategory : UU (l1 ⊔ l2)
  is-prop-iso-Precategory = {!!}

  is-property-is-prop-iso-Precategory : is-prop is-prop-iso-Precategory
  is-property-is-prop-iso-Precategory = {!!}
```

### The predicate on precategories of being gaunt

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-gaunt-prop-Precategory : Prop (l1 ⊔ l2)
  is-gaunt-prop-Precategory = {!!}

  is-gaunt-Precategory : UU (l1 ⊔ l2)
  is-gaunt-Precategory = {!!}
```

### The predicate on categories of being gaunt

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-gaunt-prop-Category : Prop (l1 ⊔ l2)
  is-gaunt-prop-Category = {!!}

  is-gaunt-Category : UU (l1 ⊔ l2)
  is-gaunt-Category = {!!}
```

### The type of gaunt categories

```agda
Gaunt-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Gaunt-Category l1 l2 = {!!}

module _
  {l1 l2 : Level} (C : Gaunt-Category l1 l2)
  where

  category-Gaunt-Category : Category l1 l2
  category-Gaunt-Category = {!!}

  obj-Gaunt-Category : UU l1
  obj-Gaunt-Category = {!!}

  hom-set-Gaunt-Category :
    obj-Gaunt-Category → obj-Gaunt-Category → Set l2
  hom-set-Gaunt-Category = {!!}

  hom-Gaunt-Category :
    obj-Gaunt-Category → obj-Gaunt-Category → UU l2
  hom-Gaunt-Category = {!!}

  is-set-hom-Gaunt-Category :
    (x y : obj-Gaunt-Category) → is-set (hom-Gaunt-Category x y)
  is-set-hom-Gaunt-Category = {!!}

  comp-hom-Gaunt-Category :
    {x y z : obj-Gaunt-Category} →
    hom-Gaunt-Category y z →
    hom-Gaunt-Category x y →
    hom-Gaunt-Category x z
  comp-hom-Gaunt-Category = {!!}

  associative-comp-hom-Gaunt-Category :
    {x y z w : obj-Gaunt-Category}
    (h : hom-Gaunt-Category z w)
    (g : hom-Gaunt-Category y z)
    (f : hom-Gaunt-Category x y) →
    comp-hom-Gaunt-Category (comp-hom-Gaunt-Category h g) f ＝
    comp-hom-Gaunt-Category h (comp-hom-Gaunt-Category g f)
  associative-comp-hom-Gaunt-Category = {!!}

  inv-associative-comp-hom-Gaunt-Category :
    {x y z w : obj-Gaunt-Category}
    (h : hom-Gaunt-Category z w)
    (g : hom-Gaunt-Category y z)
    (f : hom-Gaunt-Category x y) →
    comp-hom-Gaunt-Category h (comp-hom-Gaunt-Category g f) ＝
    comp-hom-Gaunt-Category (comp-hom-Gaunt-Category h g) f
  inv-associative-comp-hom-Gaunt-Category = {!!}

  associative-composition-operation-Gaunt-Category :
    associative-composition-operation-binary-family-Set
      hom-set-Gaunt-Category
  associative-composition-operation-Gaunt-Category = {!!}

  id-hom-Gaunt-Category :
    {x : obj-Gaunt-Category} → hom-Gaunt-Category x x
  id-hom-Gaunt-Category = {!!}

  left-unit-law-comp-hom-Gaunt-Category :
    {x y : obj-Gaunt-Category} (f : hom-Gaunt-Category x y) →
    comp-hom-Gaunt-Category id-hom-Gaunt-Category f ＝ f
  left-unit-law-comp-hom-Gaunt-Category = {!!}

  right-unit-law-comp-hom-Gaunt-Category :
    {x y : obj-Gaunt-Category} (f : hom-Gaunt-Category x y) →
    comp-hom-Gaunt-Category f id-hom-Gaunt-Category ＝ f
  right-unit-law-comp-hom-Gaunt-Category = {!!}

  is-unital-composition-operation-Gaunt-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Gaunt-Category
      comp-hom-Gaunt-Category
  is-unital-composition-operation-Gaunt-Category = {!!}

  is-gaunt-Gaunt-Category :
    is-gaunt-Category category-Gaunt-Category
  is-gaunt-Gaunt-Category = {!!}
```

### The underlying nonunital precategory of a gaunt category

```agda
nonunital-precategory-Gaunt-Category :
  {l1 l2 : Level} → Gaunt-Category l1 l2 → Nonunital-Precategory l1 l2
nonunital-precategory-Gaunt-Category = {!!}
```

### The underlying precategory of a gaunt category

```agda
precategory-Gaunt-Category :
  {l1 l2 : Level} → Gaunt-Category l1 l2 → Precategory l1 l2
precategory-Gaunt-Category = {!!}
```

### The underlying preunivalent category of a gaunt category

```agda
preunivalent-category-Gaunt-Category :
  {l1 l2 : Level} → Gaunt-Category l1 l2 → Preunivalent-Category l1 l2
preunivalent-category-Gaunt-Category = {!!}
```

### The total hom-type of a gaunt category

```agda
total-hom-Gaunt-Category :
  {l1 l2 : Level} (C : Gaunt-Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Gaunt-Category = {!!}

obj-total-hom-Gaunt-Category :
  {l1 l2 : Level} (C : Gaunt-Category l1 l2) →
  total-hom-Gaunt-Category C →
  obj-Gaunt-Category C × obj-Gaunt-Category C
obj-total-hom-Gaunt-Category = {!!}
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Gaunt-Category l1 l2)
  where

  hom-eq-Gaunt-Category :
    (x y : obj-Gaunt-Category C) → x ＝ y → hom-Gaunt-Category C x y
  hom-eq-Gaunt-Category = {!!}

  hom-inv-eq-Gaunt-Category :
    (x y : obj-Gaunt-Category C) → x ＝ y → hom-Gaunt-Category C y x
  hom-inv-eq-Gaunt-Category = {!!}
```

## Properties

### Preunivalent categories whose isomorphism-sets are propositions are strict categories

```agda
is-strict-category-is-prop-iso-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2) →
  is-prop-iso-Precategory (precategory-Preunivalent-Category C) →
  is-strict-category-Preunivalent-Category C
is-strict-category-is-prop-iso-Preunivalent-Category = {!!}
```

### Gaunt categories are strict

```agda
is-strict-category-is-gaunt-Category :
  {l1 l2 : Level} (C : Category l1 l2) →
  is-gaunt-Category C → is-strict-category-Category C
is-strict-category-is-gaunt-Category = {!!}
```

### A strict category is gaunt if `iso-eq` is surjective

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  is-category-is-surjective-iso-eq-Strict-Category :
    is-surjective-iso-eq-Precategory (precategory-Strict-Category C) →
    is-category-Precategory (precategory-Strict-Category C)
  is-category-is-surjective-iso-eq-Strict-Category = {!!}

  is-prop-iso-is-category-Strict-Category :
    is-category-Precategory (precategory-Strict-Category C) →
    is-prop-iso-Precategory (precategory-Strict-Category C)
  is-prop-iso-is-category-Strict-Category = {!!}

  is-prop-iso-is-surjective-iso-eq-Strict-Category :
    is-surjective-iso-eq-Precategory (precategory-Strict-Category C) →
    is-prop-iso-Precategory (precategory-Strict-Category C)
  is-prop-iso-is-surjective-iso-eq-Strict-Category = {!!}

  is-gaunt-is-surjective-iso-eq-Strict-Category :
    is-surjective-iso-eq-Precategory (precategory-Strict-Category C) →
    is-gaunt-Precategory (precategory-Strict-Category C)
  is-gaunt-is-surjective-iso-eq-Strict-Category = {!!}
```

### A category is gaunt if and only if every object is rigid

**Proof:** Using the fact that a type is a
[proposition](foundation-core.propositions.md) if and only if having an
inhabitant implies it is [contractible](foundation-core.contractible-types.md),
we can apply
[isomorphism induction](category-theory.isomorphism-induction-categories.md) to
get our result.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-gaunt-is-rigid-Category :
    ((x : obj-Category C) → is-rigid-obj-Category C x) → is-gaunt-Category C
  is-gaunt-is-rigid-Category = {!!}

  is-rigid-is-gaunt-Category :
    is-gaunt-Category C → (x : obj-Category C) → is-rigid-obj-Category C x
  is-rigid-is-gaunt-Category = {!!}
```

## See also

- [Posets](order-theory.posets.md) are gaunt.

## External links

- [Gaunt (pre)categories](https://1lab.dev/Cat.Gaunt.html) at 1lab
- [gaunt category](https://ncatlab.org/nlab/show/gaunt+category#in_type_theory)
  at $n$Lab
