# Wide subcategories

```agda
module category-theory.wide-subcategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.faithful-functors-precategories
open import category-theory.functors-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-categories
open import category-theory.precategories
open import category-theory.subcategories
open import category-theory.wide-subprecategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A **wide subcategory** of a [category](category-theory.categories.md) `C` is a
[subcategory](category-theory.subcategories.md) that contains all the objects of
`C`.

## Lemma

### Wide subprecategories of categories are categories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Wide-Subprecategory l3 C)
  (is-category-C : is-category-Precategory C)
  where

  is-category-is-category-Wide-Subprecategory :
    is-category-Precategory (precategory-Wide-Subprecategory C P)
  is-category-is-category-Wide-Subprecategory = {!!}
```

## Definitions

### The predicate of being a wide subcategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  is-wide-prop-Subcategory : Prop (l1 ⊔ l3)
  is-wide-prop-Subcategory = {!!}

  is-wide-Subcategory : UU (l1 ⊔ l3)
  is-wide-Subcategory = {!!}

  is-prop-is-wide-Subcategory : is-prop (is-wide-Subcategory)
  is-prop-is-wide-Subcategory = {!!}
```

### wide sub-hom-families of categories

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (C : Category l1 l2)
  where

  subtype-hom-wide-Category : UU (l1 ⊔ l2 ⊔ lsuc l3)
  subtype-hom-wide-Category = {!!}
```

### Categorical predicates on wide sub-hom-families

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P₁ : subtype-hom-wide-Category l3 C)
  where

  contains-id-prop-subtype-hom-wide-Category : Prop (l1 ⊔ l3)
  contains-id-prop-subtype-hom-wide-Category = {!!}

  contains-id-subtype-hom-wide-Category : UU (l1 ⊔ l3)
  contains-id-subtype-hom-wide-Category = {!!}

  is-prop-contains-id-subtype-hom-wide-Category :
    is-prop contains-id-subtype-hom-wide-Category
  is-prop-contains-id-subtype-hom-wide-Category = {!!}

  is-closed-under-composition-subtype-hom-wide-Category : UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-composition-subtype-hom-wide-Category = {!!}

  is-prop-is-closed-under-composition-subtype-hom-wide-Category :
    is-prop is-closed-under-composition-subtype-hom-wide-Category
  is-prop-is-closed-under-composition-subtype-hom-wide-Category = {!!}

  is-closed-under-composition-prop-subtype-hom-wide-Category :
    Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-under-composition-prop-subtype-hom-wide-Category = {!!}
```

### The predicate on a subtype of the hom-sets of being a wide subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P₁ : subtype-hom-wide-Category l3 C)
  where

  is-wide-subcategory-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-wide-subcategory-Prop = {!!}

  is-wide-subcategory : UU (l1 ⊔ l2 ⊔ l3)
  is-wide-subcategory = {!!}

  is-prop-is-wide-subcategory : is-prop (is-wide-subcategory)
  is-prop-is-wide-subcategory = {!!}

  contains-id-is-wide-subcategory :
    is-wide-subcategory → contains-id-subtype-hom-wide-Category C P₁
  contains-id-is-wide-subcategory = {!!}

  is-closed-under-composition-is-wide-subcategory :
    is-wide-subcategory →
    is-closed-under-composition-subtype-hom-wide-Category C P₁
  is-closed-under-composition-is-wide-subcategory = {!!}
```

### Wide subcategories

```agda
Wide-Subcategory :
  {l1 l2 : Level} (l3 : Level)
  (C : Category l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
Wide-Subcategory = {!!}
```

#### Objects in wide subcategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Wide-Subcategory l3 C)
  where

  subtype-obj-Wide-Subcategory : subtype lzero (obj-Category C)
  subtype-obj-Wide-Subcategory = {!!}

  obj-Wide-Subcategory : UU l1
  obj-Wide-Subcategory = {!!}

  inclusion-obj-Wide-Subcategory :
    obj-Wide-Subcategory → obj-Category C
  inclusion-obj-Wide-Subcategory = {!!}
```

#### Morphisms in wide subcategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Wide-Subcategory l3 C)
  where

  subtype-hom-Wide-Subcategory : subtype-hom-wide-Category l3 C
  subtype-hom-Wide-Subcategory = {!!}

  hom-Wide-Subcategory : (x y : obj-Wide-Subcategory C P) → UU (l2 ⊔ l3)
  hom-Wide-Subcategory = {!!}

  inclusion-hom-Wide-Subcategory :
    (x y : obj-Wide-Subcategory C P) →
    hom-Wide-Subcategory x y →
    hom-Category C
      ( inclusion-obj-Wide-Subcategory C P x)
      ( inclusion-obj-Wide-Subcategory C P y)
  inclusion-hom-Wide-Subcategory = {!!}
```

The predicate on a morphism between any objects of being contained in the wide
subcategory:

```agda
  is-in-hom-Wide-Subcategory :
    (x y : obj-Category C) (f : hom-Category C x y) → UU l3
  is-in-hom-Wide-Subcategory = {!!}

  is-prop-is-in-hom-Wide-Subcategory :
    (x y : obj-Category C) (f : hom-Category C x y) →
    is-prop (is-in-hom-Wide-Subcategory x y f)
  is-prop-is-in-hom-Wide-Subcategory = {!!}

  is-in-hom-inclusion-hom-Wide-Subcategory :
    (x y : obj-Wide-Subcategory C P)
    (f : hom-Wide-Subcategory x y) →
    is-in-hom-Wide-Subcategory
      ( inclusion-obj-Wide-Subcategory C P x)
      ( inclusion-obj-Wide-Subcategory C P y)
      ( inclusion-hom-Wide-Subcategory x y f)
  is-in-hom-inclusion-hom-Wide-Subcategory = {!!}
```

Wide subcategories are wide subcategories:

```agda
  is-wide-subcategory-Wide-Subcategory :
    is-wide-subcategory C subtype-hom-Wide-Subcategory
  is-wide-subcategory-Wide-Subcategory = {!!}

  contains-id-Wide-Subcategory :
    contains-id-subtype-hom-wide-Category C
      ( subtype-hom-Wide-Subcategory)
  contains-id-Wide-Subcategory = {!!}

  is-closed-under-composition-Wide-Subcategory :
    is-closed-under-composition-subtype-hom-wide-Category C
      ( subtype-hom-Wide-Subcategory)
  is-closed-under-composition-Wide-Subcategory = {!!}
```

Wide subcategories are subcategories:

```agda
  subtype-hom-subcategory-Wide-Subcategory :
    subtype-hom-Category l3 C (subtype-obj-Wide-Subcategory C P)
  subtype-hom-subcategory-Wide-Subcategory = {!!}

  is-subcategory-Wide-Subcategory :
    is-subcategory C
      ( subtype-obj-Wide-Subcategory C P)
      ( subtype-hom-subcategory-Wide-Subcategory)
  is-subcategory-Wide-Subcategory = {!!}

  subcategory-Wide-Subcategory : Subcategory lzero l3 C
  subcategory-Wide-Subcategory = {!!}

  is-wide-Wide-Subcategory :
    is-wide-Subcategory C (subcategory-Wide-Subcategory)
  is-wide-Wide-Subcategory = {!!}
```

### The underlying category of a wide subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Wide-Subcategory l3 C)
  where

  hom-set-Wide-Subcategory :
    (x y : obj-Wide-Subcategory C P) → Set (l2 ⊔ l3)
  hom-set-Wide-Subcategory = {!!}

  is-set-hom-Wide-Subcategory :
    (x y : obj-Wide-Subcategory C P) →
    is-set (hom-Wide-Subcategory C P x y)
  is-set-hom-Wide-Subcategory = {!!}

  id-hom-Wide-Subcategory :
    {x : obj-Wide-Subcategory C P} → hom-Wide-Subcategory C P x x
  id-hom-Wide-Subcategory = {!!}

  comp-hom-Wide-Subcategory :
    {x y z : obj-Wide-Subcategory C P} →
    hom-Wide-Subcategory C P y z →
    hom-Wide-Subcategory C P x y →
    hom-Wide-Subcategory C P x z
  comp-hom-Wide-Subcategory = {!!}

  associative-comp-hom-Wide-Subcategory :
    {x y z w : obj-Wide-Subcategory C P}
    (h : hom-Wide-Subcategory C P z w)
    (g : hom-Wide-Subcategory C P y z)
    (f : hom-Wide-Subcategory C P x y) →
    comp-hom-Wide-Subcategory (comp-hom-Wide-Subcategory h g) f ＝
    comp-hom-Wide-Subcategory h (comp-hom-Wide-Subcategory g f)
  associative-comp-hom-Wide-Subcategory = {!!}

  inv-associative-comp-hom-Wide-Subcategory :
    {x y z w : obj-Wide-Subcategory C P}
    (h : hom-Wide-Subcategory C P z w)
    (g : hom-Wide-Subcategory C P y z)
    (f : hom-Wide-Subcategory C P x y) →
    comp-hom-Wide-Subcategory h (comp-hom-Wide-Subcategory g f) ＝
    comp-hom-Wide-Subcategory (comp-hom-Wide-Subcategory h g) f
  inv-associative-comp-hom-Wide-Subcategory = {!!}

  left-unit-law-comp-hom-Wide-Subcategory :
    {x y : obj-Wide-Subcategory C P}
    (f : hom-Wide-Subcategory C P x y) →
    comp-hom-Wide-Subcategory (id-hom-Wide-Subcategory) f ＝ f
  left-unit-law-comp-hom-Wide-Subcategory = {!!}

  right-unit-law-comp-hom-Wide-Subcategory :
    {x y : obj-Wide-Subcategory C P}
    (f : hom-Wide-Subcategory C P x y) →
    comp-hom-Wide-Subcategory f (id-hom-Wide-Subcategory) ＝ f
  right-unit-law-comp-hom-Wide-Subcategory = {!!}

  associative-composition-operation-Wide-Subcategory :
    associative-composition-operation-binary-family-Set
      ( hom-set-Wide-Subcategory)
  associative-composition-operation-Wide-Subcategory = {!!}

  is-unital-composition-operation-Wide-Subcategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Wide-Subcategory)
      ( comp-hom-Wide-Subcategory)
  is-unital-composition-operation-Wide-Subcategory = {!!}

  precategory-Wide-Subcategory : Precategory l1 (l2 ⊔ l3)
  precategory-Wide-Subcategory = {!!}
```

### The underlying category of a wide subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Wide-Subcategory l3 C)
  where

  category-Wide-Subcategory : Category l1 (l2 ⊔ l3)
  category-Wide-Subcategory = {!!}
```

### The inclusion functor of a wide subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Wide-Subcategory l3 C)
  where

  inclusion-map-Wide-Subcategory :
    map-Category (category-Wide-Subcategory C P) C
  inclusion-map-Wide-Subcategory = {!!}

  is-functor-inclusion-Wide-Subcategory :
    is-functor-map-Category
      ( category-Wide-Subcategory C P)
      ( C)
      ( inclusion-map-Wide-Subcategory)
  is-functor-inclusion-Wide-Subcategory = {!!}

  inclusion-Wide-Subcategory :
    functor-Category (category-Wide-Subcategory C P) C
  inclusion-Wide-Subcategory = {!!}
```

## Properties

### The inclusion functor is faithful and an equivalence on objects

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Wide-Subcategory l3 C)
  where

  is-faithful-inclusion-Wide-Subcategory :
    is-faithful-functor-Precategory
      ( precategory-Wide-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Wide-Subcategory C P)
  is-faithful-inclusion-Wide-Subcategory = {!!}

  is-equiv-obj-inclusion-Wide-Subcategory :
    is-equiv
      ( obj-functor-Category
        ( category-Wide-Subcategory C P)
        ( C)
        ( inclusion-Wide-Subcategory C P))
  is-equiv-obj-inclusion-Wide-Subcategory = {!!}
```

### The inclusion functor is pseudomonic

This remains to be formalized. This is a consequence of repeleteness.

## External links

- [Wide subcategories](https://1lab.dev/Cat.Functor.WideSubcategory.html) at
  1lab
- [wide subcategory](https://ncatlab.org/nlab/show/wide+subcategory) at $n$Lab
