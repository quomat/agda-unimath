# Preunivalent categories

```agda
module category-theory.preunivalent-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **preunivalent category** is a [precategory](category-theory.precategories.md)
for which the [identifications](foundation-core.identity-types.md) between the
objects [embed](foundation-core.embeddings.md) into the
[isomorphisms](category-theory.isomorphisms-in-precategories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A precategory is a preunivalent category if this function,
called `iso-eq`, is an embedding.

The idea of [preunivalence](foundation.preunivalence.md) is that it is a common
generalization of univalent mathematics and mathematics with Axiom K. Hence
preunivalent categories generalize both
[(univalent) categories](category-theory.categories.md) and
[strict categories](category-theory.strict-categories.md), which are
precategories whose objects form a [set](foundation-core.sets.md).

The preunivalence condition on precategories states that the type of objects is
a subgroupoid of the [groupoid](category-theory.groupoids.md) of isomorphisms.
For univalent categories the groupoid of objects is equivalent to the groupoid
of isomorphisms, while for strict categories the groupoid of objects is
discrete. Indeed, in this sense preunivalence provides a generalization of both
notions of "category", with _no more structure_. This is opposed to the even
more general notion of precategory, where the homotopy structure on the objects
can be almost completely unrelated to the homotopy structure of the morphisms.

## Definitions

### The predicate on precategories of being a preunivalent category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-preunivalent-prop-Precategory = {!!}

  is-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-preunivalent-Precategory = {!!}
```

### The type of preunivalent categories

```agda
Preunivalent-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preunivalent-Category = {!!}

module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  precategory-Preunivalent-Category : Precategory l1 l2
  precategory-Preunivalent-Category = {!!}

  obj-Preunivalent-Category : UU l1
  obj-Preunivalent-Category = {!!}

  hom-set-Preunivalent-Category :
    obj-Preunivalent-Category → obj-Preunivalent-Category → Set l2
  hom-set-Preunivalent-Category = {!!}

  hom-Preunivalent-Category :
    obj-Preunivalent-Category → obj-Preunivalent-Category → UU l2
  hom-Preunivalent-Category = {!!}

  is-set-hom-Preunivalent-Category :
    (x y : obj-Preunivalent-Category) → is-set (hom-Preunivalent-Category x y)
  is-set-hom-Preunivalent-Category = {!!}

  comp-hom-Preunivalent-Category :
    {x y z : obj-Preunivalent-Category} →
    hom-Preunivalent-Category y z →
    hom-Preunivalent-Category x y →
    hom-Preunivalent-Category x z
  comp-hom-Preunivalent-Category = {!!}

  associative-comp-hom-Preunivalent-Category :
    {x y z w : obj-Preunivalent-Category}
    (h : hom-Preunivalent-Category z w)
    (g : hom-Preunivalent-Category y z)
    (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category (comp-hom-Preunivalent-Category h g) f ＝
    comp-hom-Preunivalent-Category h (comp-hom-Preunivalent-Category g f)
  associative-comp-hom-Preunivalent-Category = {!!}

  inv-associative-comp-hom-Preunivalent-Category :
    {x y z w : obj-Preunivalent-Category}
    (h : hom-Preunivalent-Category z w)
    (g : hom-Preunivalent-Category y z)
    (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category h (comp-hom-Preunivalent-Category g f) ＝
    comp-hom-Preunivalent-Category (comp-hom-Preunivalent-Category h g) f
  inv-associative-comp-hom-Preunivalent-Category = {!!}

  associative-composition-operation-Preunivalent-Category :
    associative-composition-operation-binary-family-Set
      hom-set-Preunivalent-Category
  associative-composition-operation-Preunivalent-Category = {!!}

  id-hom-Preunivalent-Category :
    {x : obj-Preunivalent-Category} → hom-Preunivalent-Category x x
  id-hom-Preunivalent-Category = {!!}

  left-unit-law-comp-hom-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category id-hom-Preunivalent-Category f ＝ f
  left-unit-law-comp-hom-Preunivalent-Category = {!!}

  right-unit-law-comp-hom-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category f id-hom-Preunivalent-Category ＝ f
  right-unit-law-comp-hom-Preunivalent-Category = {!!}

  is-unital-composition-operation-Preunivalent-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Preunivalent-Category
      comp-hom-Preunivalent-Category
  is-unital-composition-operation-Preunivalent-Category = {!!}

  is-preunivalent-Preunivalent-Category :
    is-preunivalent-Precategory precategory-Preunivalent-Category
  is-preunivalent-Preunivalent-Category = {!!}

  emb-iso-eq-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} →
    (x ＝ y) ↪ (iso-Precategory precategory-Preunivalent-Category x y)
  emb-iso-eq-Preunivalent-Category = {!!}
```

### The total hom-type of a preunivalent category

```agda
total-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Preunivalent-Category = {!!}

obj-total-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2) →
  total-hom-Preunivalent-Category C →
  obj-Preunivalent-Category C × obj-Preunivalent-Category C
obj-total-hom-Preunivalent-Category = {!!}
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Preunivalent-Category l1 l2)
  where

  hom-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category C) →
    x ＝ y → hom-Preunivalent-Category C x y
  hom-eq-Preunivalent-Category = {!!}

  hom-inv-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category C) →
    x ＝ y → hom-Preunivalent-Category C y x
  hom-inv-eq-Preunivalent-Category = {!!}
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  {x y : obj-Preunivalent-Category C}
  (f : hom-Preunivalent-Category C x y)
  (z : obj-Preunivalent-Category C) →
  hom-Preunivalent-Category C y z →
  hom-Preunivalent-Category C x z
precomp-hom-Preunivalent-Category = {!!}

postcomp-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  {x y : obj-Preunivalent-Category C}
  (f : hom-Preunivalent-Category C x y)
  (z : obj-Preunivalent-Category C) →
  hom-Preunivalent-Category C z x →
  hom-Preunivalent-Category C z y
postcomp-hom-Preunivalent-Category = {!!}
```

## Properties

### The objects in a preunivalent category form a 1-type

The type of identities between two objects in a preunivalent category embeds
into the type of isomorphisms between them. But this type is a set, and thus the
identity type is a set.

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-1-type-obj-Preunivalent-Category : is-1-type (obj-Preunivalent-Category C)
  is-1-type-obj-Preunivalent-Category = {!!}

  obj-1-type-Preunivalent-Category : 1-Type l1
  obj-1-type-Preunivalent-Category = {!!}
```

### The total hom-type of a preunivalent category is a 1-type

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-1-type-total-hom-Preunivalent-Category :
    is-1-type (total-hom-Preunivalent-Category C)
  is-1-type-total-hom-Preunivalent-Category = {!!}

  total-hom-1-type-Preunivalent-Category : 1-Type (l1 ⊔ l2)
  total-hom-1-type-Preunivalent-Category = {!!}
```

## See also

- [The preunivalence axiom](foundation.preunivalence.md)
