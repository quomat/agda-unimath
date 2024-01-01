# Wide subprecategories

```agda
module category-theory.wide-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.precategories
open import category-theory.subprecategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
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

A **wide subprecategory** of a [precategory](category-theory.precategories.md)
`C` is a [subprecategory](category-theory.subprecategories.md) that contains all
the objects of `C`.

## Definitions

### The predicate of being a wide subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-wide-prop-Subprecategory : Prop (l1 ⊔ l3)
  is-wide-prop-Subprecategory = {!!}

  is-wide-Subprecategory : UU (l1 ⊔ l3)
  is-wide-Subprecategory = {!!}

  is-prop-is-wide-Subprecategory : is-prop (is-wide-Subprecategory)
  is-prop-is-wide-Subprecategory = {!!}
```

### Wide sub-hom-families of precategories

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (C : Precategory l1 l2)
  where

  subtype-hom-wide-Precategory : UU (l1 ⊔ l2 ⊔ lsuc l3)
  subtype-hom-wide-Precategory = {!!}
```

### Categorical predicates on wide sub-hom-families

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P₁ : subtype-hom-wide-Precategory l3 C)
  where

  contains-id-prop-subtype-hom-wide-Precategory : Prop (l1 ⊔ l3)
  contains-id-prop-subtype-hom-wide-Precategory = {!!}

  contains-id-subtype-hom-wide-Precategory : UU (l1 ⊔ l3)
  contains-id-subtype-hom-wide-Precategory = {!!}

  is-prop-contains-id-subtype-hom-wide-Precategory :
    is-prop contains-id-subtype-hom-wide-Precategory
  is-prop-contains-id-subtype-hom-wide-Precategory = {!!}

  is-closed-under-composition-subtype-hom-wide-Precategory : UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-composition-subtype-hom-wide-Precategory = {!!}

  is-prop-is-closed-under-composition-subtype-hom-wide-Precategory :
    is-prop is-closed-under-composition-subtype-hom-wide-Precategory
  is-prop-is-closed-under-composition-subtype-hom-wide-Precategory = {!!}

  is-closed-under-composition-prop-subtype-hom-wide-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3)
  pr1 is-closed-under-composition-prop-subtype-hom-wide-Precategory = {!!}
```

### The predicate on a subtype of the hom-sets of being a wide subprecategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P₁ : subtype-hom-wide-Precategory l3 C)
  where

  is-wide-subprecategory-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-wide-subprecategory-Prop = {!!}

  is-wide-subprecategory : UU (l1 ⊔ l2 ⊔ l3)
  is-wide-subprecategory = {!!}

  is-prop-is-wide-subprecategory : is-prop (is-wide-subprecategory)
  is-prop-is-wide-subprecategory = {!!}

  contains-id-is-wide-subprecategory :
    is-wide-subprecategory → contains-id-subtype-hom-wide-Precategory C P₁
  contains-id-is-wide-subprecategory = {!!}

  is-closed-under-composition-is-wide-subprecategory :
    is-wide-subprecategory →
    is-closed-under-composition-subtype-hom-wide-Precategory C P₁
  is-closed-under-composition-is-wide-subprecategory = {!!}
```

### Wide subprecategories

```agda
Wide-Subprecategory :
  {l1 l2 : Level} (l3 : Level)
  (C : Precategory l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
Wide-Subprecategory l3 C = {!!}
```

#### Objects in wide subprecategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Wide-Subprecategory l3 C)
  where

  subtype-obj-Wide-Subprecategory : subtype lzero (obj-Precategory C)
  subtype-obj-Wide-Subprecategory _ = {!!}

  obj-Wide-Subprecategory : UU l1
  obj-Wide-Subprecategory = {!!}

  inclusion-obj-Wide-Subprecategory :
    obj-Wide-Subprecategory → obj-Precategory C
  inclusion-obj-Wide-Subprecategory = {!!}
```

#### Morphisms in wide subprecategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Wide-Subprecategory l3 C)
  where

  subtype-hom-Wide-Subprecategory : subtype-hom-wide-Precategory l3 C
  subtype-hom-Wide-Subprecategory = {!!}

  hom-Wide-Subprecategory : (x y : obj-Wide-Subprecategory C P) → UU (l2 ⊔ l3)
  hom-Wide-Subprecategory x y = {!!}

  inclusion-hom-Wide-Subprecategory :
    (x y : obj-Wide-Subprecategory C P) →
    hom-Wide-Subprecategory x y →
    hom-Precategory C
      ( inclusion-obj-Wide-Subprecategory C P x)
      ( inclusion-obj-Wide-Subprecategory C P y)
  inclusion-hom-Wide-Subprecategory x y = {!!}
```

The predicate on a morphism between any objects of being contained in the wide
subprecategory:

```agda
  is-in-hom-Wide-Subprecategory :
    (x y : obj-Precategory C) (f : hom-Precategory C x y) → UU l3
  is-in-hom-Wide-Subprecategory x y = {!!}

  is-prop-is-in-hom-Wide-Subprecategory :
    (x y : obj-Precategory C) (f : hom-Precategory C x y) →
    is-prop (is-in-hom-Wide-Subprecategory x y f)
  is-prop-is-in-hom-Wide-Subprecategory x y = {!!}

  is-in-hom-inclusion-hom-Wide-Subprecategory :
    (x y : obj-Wide-Subprecategory C P)
    (f : hom-Wide-Subprecategory x y) →
    is-in-hom-Wide-Subprecategory
      ( inclusion-obj-Wide-Subprecategory C P x)
      ( inclusion-obj-Wide-Subprecategory C P y)
      ( inclusion-hom-Wide-Subprecategory x y f)
  is-in-hom-inclusion-hom-Wide-Subprecategory x y = {!!}
```

Wide subprecategories are wide subprecategories:

```agda
  is-wide-subprecategory-Wide-Subprecategory :
    is-wide-subprecategory C subtype-hom-Wide-Subprecategory
  is-wide-subprecategory-Wide-Subprecategory = {!!}

  contains-id-Wide-Subprecategory :
    contains-id-subtype-hom-wide-Precategory C
      ( subtype-hom-Wide-Subprecategory)
  contains-id-Wide-Subprecategory = {!!}

  is-closed-under-composition-Wide-Subprecategory :
    is-closed-under-composition-subtype-hom-wide-Precategory C
      ( subtype-hom-Wide-Subprecategory)
  is-closed-under-composition-Wide-Subprecategory = {!!}
```

Wide subprecategories are subprecategories:

```agda
  subtype-hom-subprecategory-Wide-Subprecategory :
    subtype-hom-Precategory l3 C (subtype-obj-Wide-Subprecategory C P)
  subtype-hom-subprecategory-Wide-Subprecategory x y _ _ = {!!}

  is-subprecategory-Wide-Subprecategory :
    is-subprecategory C
      ( subtype-obj-Wide-Subprecategory C P)
      ( subtype-hom-subprecategory-Wide-Subprecategory)
  pr1 is-subprecategory-Wide-Subprecategory x _ = {!!}

  subprecategory-Wide-Subprecategory : Subprecategory lzero l3 C
  pr1 subprecategory-Wide-Subprecategory = {!!}

  is-wide-Wide-Subprecategory :
    is-wide-Subprecategory C (subprecategory-Wide-Subprecategory)
  is-wide-Wide-Subprecategory _ = {!!}
```

### The underlying precategory of a wide subprecategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Wide-Subprecategory l3 C)
  where

  hom-set-Wide-Subprecategory :
    (x y : obj-Wide-Subprecategory C P) → Set (l2 ⊔ l3)
  hom-set-Wide-Subprecategory x y = {!!}

  is-set-hom-Wide-Subprecategory :
    (x y : obj-Wide-Subprecategory C P) →
    is-set (hom-Wide-Subprecategory C P x y)
  is-set-hom-Wide-Subprecategory x y = {!!}

  id-hom-Wide-Subprecategory :
    {x : obj-Wide-Subprecategory C P} → hom-Wide-Subprecategory C P x x
  pr1 id-hom-Wide-Subprecategory = {!!}

  comp-hom-Wide-Subprecategory :
    {x y z : obj-Wide-Subprecategory C P} →
    hom-Wide-Subprecategory C P y z →
    hom-Wide-Subprecategory C P x y →
    hom-Wide-Subprecategory C P x z
  pr1 (comp-hom-Wide-Subprecategory {x} {y} {z} g f) = {!!}

  associative-comp-hom-Wide-Subprecategory :
    {x y z w : obj-Wide-Subprecategory C P}
    (h : hom-Wide-Subprecategory C P z w)
    (g : hom-Wide-Subprecategory C P y z)
    (f : hom-Wide-Subprecategory C P x y) →
    comp-hom-Wide-Subprecategory (comp-hom-Wide-Subprecategory h g) f ＝
    comp-hom-Wide-Subprecategory h (comp-hom-Wide-Subprecategory g f)
  associative-comp-hom-Wide-Subprecategory {x} {y} {z} {w} h g f = {!!}

  inv-associative-comp-hom-Wide-Subprecategory :
    {x y z w : obj-Wide-Subprecategory C P}
    (h : hom-Wide-Subprecategory C P z w)
    (g : hom-Wide-Subprecategory C P y z)
    (f : hom-Wide-Subprecategory C P x y) →
    ( comp-hom-Wide-Subprecategory h
      ( comp-hom-Wide-Subprecategory g f)) ＝
    ( comp-hom-Wide-Subprecategory
      ( comp-hom-Wide-Subprecategory h g) f)

  inv-associative-comp-hom-Wide-Subprecategory {x} {y} {z} {w} h g f = {!!}

  left-unit-law-comp-hom-Wide-Subprecategory :
    {x y : obj-Wide-Subprecategory C P}
    (f : hom-Wide-Subprecategory C P x y) →
    comp-hom-Wide-Subprecategory (id-hom-Wide-Subprecategory) f ＝ f
  left-unit-law-comp-hom-Wide-Subprecategory {x} {y} f = {!!}

  right-unit-law-comp-hom-Wide-Subprecategory :
    {x y : obj-Wide-Subprecategory C P}
    (f : hom-Wide-Subprecategory C P x y) →
    comp-hom-Wide-Subprecategory f (id-hom-Wide-Subprecategory) ＝ f
  right-unit-law-comp-hom-Wide-Subprecategory {x} {y} f = {!!}

  associative-composition-operation-Wide-Subprecategory :
    associative-composition-operation-binary-family-Set
      ( hom-set-Wide-Subprecategory)
  pr1 associative-composition-operation-Wide-Subprecategory = {!!}

  is-unital-composition-operation-Wide-Subprecategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Wide-Subprecategory)
      ( comp-hom-Wide-Subprecategory)
  pr1 is-unital-composition-operation-Wide-Subprecategory x = {!!}

  precategory-Wide-Subprecategory : Precategory l1 (l2 ⊔ l3)
  pr1 precategory-Wide-Subprecategory = {!!}
```

### The inclusion functor of a wide subprecategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Wide-Subprecategory l3 C)
  where

  inclusion-map-Wide-Subprecategory :
    map-Precategory (precategory-Wide-Subprecategory C P) C
  pr1 inclusion-map-Wide-Subprecategory = {!!}

  is-functor-inclusion-Wide-Subprecategory :
    is-functor-map-Precategory
      ( precategory-Wide-Subprecategory C P)
      ( C)
      ( inclusion-map-Wide-Subprecategory)
  pr1 is-functor-inclusion-Wide-Subprecategory g f = {!!}

  inclusion-Wide-Subprecategory :
    functor-Precategory (precategory-Wide-Subprecategory C P) C
  pr1 inclusion-Wide-Subprecategory = {!!}
```

## Properties

### The inclusion functor is faithful and an equivalence on objects

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Wide-Subprecategory l3 C)
  where

  is-faithful-inclusion-Wide-Subprecategory :
    is-faithful-functor-Precategory
      ( precategory-Wide-Subprecategory C P)
      ( C)
      ( inclusion-Wide-Subprecategory C P)
  is-faithful-inclusion-Wide-Subprecategory x y = {!!}

  is-equiv-obj-inclusion-Wide-Subprecategory :
    is-equiv
      ( obj-functor-Precategory
        ( precategory-Wide-Subprecategory C P)
        ( C)
        ( inclusion-Wide-Subprecategory C P))
  is-equiv-obj-inclusion-Wide-Subprecategory = {!!}
```

## External links

- [Wide subcategories](https://1lab.dev/Cat.Functor.WideSubcategory.html) at
  1lab
- [wide subcategory](https://ncatlab.org/nlab/show/wide+subcategory) at $n$Lab
