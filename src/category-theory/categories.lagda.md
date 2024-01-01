# Categories

```agda
module category-theory.categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories

open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels
```

</details>

## Idea

A **category** in Homotopy Type Theory is a
[precategory](category-theory.precategories.md) for which the
[identifications](foundation-core.identity-types.md) between the objects are the
[isomorphisms](category-theory.isomorphisms-in-precategories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A precategory is a category if this function, called
`iso-eq`, is an [equivalence](foundation-core.equivalences.md). In particular,
being a category is a [proposition](foundation-core.propositions.md) since
`is-equiv` is a proposition.

## Definitions

### The predicate on precategories of being a category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-category-prop-Precategory : Prop (l1 ⊔ l2)
  is-category-prop-Precategory = {!!}

  is-category-Precategory : UU (l1 ⊔ l2)
  is-category-Precategory = {!!}

  is-prop-is-category-Precategory : is-prop is-category-Precategory
  is-prop-is-category-Precategory = {!!}
```

### The type of categories

```agda
Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Category = {!!}

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  precategory-Category : Precategory l1 l2
  precategory-Category = {!!}

  obj-Category : UU l1
  obj-Category = {!!}

  hom-set-Category : obj-Category → obj-Category → Set l2
  hom-set-Category = {!!}

  hom-Category : obj-Category → obj-Category → UU l2
  hom-Category = {!!}

  is-set-hom-Category :
    (x y : obj-Category) → is-set (hom-Category x y)
  is-set-hom-Category = {!!}

  comp-hom-Category :
    {x y z : obj-Category} →
    hom-Category y z → hom-Category x y → hom-Category x z
  comp-hom-Category = {!!}

  associative-comp-hom-Category :
    {x y z w : obj-Category}
    (h : hom-Category z w)
    (g : hom-Category y z)
    (f : hom-Category x y) →
    comp-hom-Category (comp-hom-Category h g) f ＝
    comp-hom-Category h (comp-hom-Category g f)
  associative-comp-hom-Category = {!!}

  inv-associative-comp-hom-Category :
    {x y z w : obj-Category}
    (h : hom-Category z w)
    (g : hom-Category y z)
    (f : hom-Category x y) →
    comp-hom-Category h (comp-hom-Category g f) ＝
    comp-hom-Category (comp-hom-Category h g) f
  inv-associative-comp-hom-Category = {!!}

  associative-composition-operation-Category :
    associative-composition-operation-binary-family-Set hom-set-Category
  associative-composition-operation-Category = {!!}

  id-hom-Category : {x : obj-Category} → hom-Category x x
  id-hom-Category = {!!}

  left-unit-law-comp-hom-Category :
    {x y : obj-Category} (f : hom-Category x y) →
    comp-hom-Category id-hom-Category f ＝ f
  left-unit-law-comp-hom-Category = {!!}

  right-unit-law-comp-hom-Category :
    {x y : obj-Category} (f : hom-Category x y) →
    comp-hom-Category f id-hom-Category ＝ f
  right-unit-law-comp-hom-Category = {!!}

  is-unital-composition-operation-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Category
      comp-hom-Category
  is-unital-composition-operation-Category = {!!}

  is-category-Category :
    is-category-Precategory precategory-Category
  is-category-Category = {!!}
```

### The underlying nonunital precategory of a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  nonunital-precategory-Category : Nonunital-Precategory l1 l2
  nonunital-precategory-Category = {!!}
```

### The underlying preunivalent category of a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-preunivalent-category-Category :
    is-preunivalent-Precategory (precategory-Category C)
  is-preunivalent-category-Category = {!!}

  preunivalent-category-Category : Preunivalent-Category l1 l2
  preunivalent-category-Category = {!!}
```

### The total hom-type of a category

```agda
total-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Category = {!!}

obj-total-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) →
  total-hom-Category C →
  obj-Category C × obj-Category C
obj-total-hom-Category = {!!}
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (x y : obj-Category C)
  where

  hom-eq-Category : x ＝ y → hom-Category C x y
  hom-eq-Category = {!!}

  hom-inv-eq-Category : x ＝ y → hom-Category C y x
  hom-inv-eq-Category = {!!}
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  (f : hom-Category C x y) (z : obj-Category C) →
  hom-Category C y z → hom-Category C x z
precomp-hom-Category = {!!}

postcomp-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  (f : hom-Category C x y) (z : obj-Category C) →
  hom-Category C z x → hom-Category C z y
postcomp-hom-Category = {!!}
```

## Properties

### The objects in a category form a 1-type

The type of identities between two objects in a category is equivalent to the
type of isomorphisms between them. But this type is a set, and thus the identity
type is a set.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-1-type-obj-Category : is-1-type (obj-Category C)
  is-1-type-obj-Category = {!!}

  obj-1-type-Category : 1-Type l1
  obj-1-type-Category = {!!}
```

### The total hom-type of a category is a 1-type

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-1-type-total-hom-Category :
    is-1-type (total-hom-Category C)
  is-1-type-total-hom-Category = {!!}

  total-hom-1-type-Category : 1-Type (l1 ⊔ l2)
  total-hom-1-type-Category = {!!}
```

### A preunivalent category is a category if and only if `iso-eq` is surjective

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-surjective-iso-eq-prop-Precategory : Prop (l1 ⊔ l2)
  is-surjective-iso-eq-prop-Precategory = {!!}

  is-surjective-iso-eq-Precategory : UU (l1 ⊔ l2)
  is-surjective-iso-eq-Precategory = {!!}

  is-prop-is-surjective-iso-eq-Precategory :
    is-prop is-surjective-iso-eq-Precategory
  is-prop-is-surjective-iso-eq-Precategory = {!!}
```

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-category-is-surjective-iso-eq-Preunivalent-Category :
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C) →
    is-category-Precategory (precategory-Preunivalent-Category C)
  is-category-is-surjective-iso-eq-Preunivalent-Category = {!!}

  is-surjective-iso-eq-is-category-Preunivalent-Category :
    is-category-Precategory (precategory-Preunivalent-Category C) →
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C)
  is-surjective-iso-eq-is-category-Preunivalent-Category = {!!}

  is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Category :
    is-equiv is-category-is-surjective-iso-eq-Preunivalent-Category
  is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Category = {!!}

  is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Category :
    is-equiv is-surjective-iso-eq-is-category-Preunivalent-Category
  is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Category = {!!}

  equiv-is-category-is-surjective-iso-eq-Preunivalent-Category :
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C) ≃
    is-category-Precategory (precategory-Preunivalent-Category C)
  equiv-is-category-is-surjective-iso-eq-Preunivalent-Category = {!!}

  equiv-is-surjective-iso-eq-is-category-Preunivalent-Category :
    is-category-Precategory (precategory-Preunivalent-Category C) ≃
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C)
  equiv-is-surjective-iso-eq-is-category-Preunivalent-Category = {!!}
```
