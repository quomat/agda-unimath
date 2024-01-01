# Subprecategories

```agda
module category-theory.subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **subprecategory** of a [precategory](category-theory.precategories.md) `C`
consists of a [subtype](foundation-core.subtypes.md) `P₀` of the objects of `C`,
and a family of subtypes `P₁`

```text
  P₁ : (X Y : obj C) → P₀ X → P₀ Y → subtype (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition.

## Definition

### Sub-hom-families

```agda
subtype-hom-Precategory :
  {l1 l2 l3 : Level} (l4 : Level)
  (C : Precategory l1 l2)
  (P₀ : subtype l3 (obj-Precategory C)) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
subtype-hom-Precategory = {!!}
```

### Categorical predicates on sub-hom-families

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P₀ : subtype l3 (obj-Precategory C))
  (P₁ : subtype-hom-Precategory l4 C P₀)
  where

  contains-id-subtype-Precategory : UU (l1 ⊔ l3 ⊔ l4)
  contains-id-subtype-Precategory = {!!}

  is-prop-contains-id-subtype-Precategory :
    is-prop contains-id-subtype-Precategory
  is-prop-contains-id-subtype-Precategory = {!!}

  contains-id-prop-subtype-Precategory : Prop (l1 ⊔ l3 ⊔ l4)
  pr1 contains-id-prop-subtype-Precategory = {!!}

  is-closed-under-composition-subtype-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-under-composition-subtype-Precategory = {!!}

  is-prop-is-closed-under-composition-subtype-Precategory :
    is-prop is-closed-under-composition-subtype-Precategory
  is-prop-is-closed-under-composition-subtype-Precategory = {!!}

  is-closed-under-composition-prop-subtype-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-under-composition-prop-subtype-Precategory = {!!}
```

### The predicate of being a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P₀ : subtype l3 (obj-Precategory C))
  (P₁ : subtype-hom-Precategory l4 C P₀)
  where

  is-subprecategory-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subprecategory-Prop = {!!}

  is-subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subprecategory = {!!}

  is-prop-is-subprecategory : is-prop (is-subprecategory)
  is-prop-is-subprecategory = {!!}

  contains-id-is-subprecategory :
    is-subprecategory → contains-id-subtype-Precategory C P₀ P₁
  contains-id-is-subprecategory = {!!}

  is-closed-under-composition-is-subprecategory :
    is-subprecategory → is-closed-under-composition-subtype-Precategory C P₀ P₁
  is-closed-under-composition-is-subprecategory = {!!}
```

### Subprecategories

```agda
Subprecategory :
  {l1 l2 : Level} (l3 l4 : Level)
  (C : Precategory l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Subprecategory = {!!}
```

#### Objects in subprecategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  subtype-obj-Subprecategory : subtype l3 (obj-Precategory C)
  subtype-obj-Subprecategory = {!!}

  obj-Subprecategory : UU (l1 ⊔ l3)
  obj-Subprecategory = {!!}

  inclusion-obj-Subprecategory : obj-Subprecategory → obj-Precategory C
  inclusion-obj-Subprecategory = {!!}

  is-in-obj-Subprecategory : (x : obj-Precategory C) → UU l3
  is-in-obj-Subprecategory = {!!}

  is-prop-is-in-obj-Subprecategory :
    (x : obj-Precategory C) → is-prop (is-in-obj-Subprecategory x)
  is-prop-is-in-obj-Subprecategory = {!!}

  is-in-obj-inclusion-obj-Subprecategory :
    (x : obj-Subprecategory) →
    is-in-obj-Subprecategory (inclusion-obj-Subprecategory x)
  is-in-obj-inclusion-obj-Subprecategory = {!!}
```

#### Morphisms in subprecategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  subtype-hom-Subprecategory :
    subtype-hom-Precategory l4 C (subtype-obj-Subprecategory C P)
  subtype-hom-Subprecategory = {!!}

  subtype-hom-obj-subprecategory-Subprecategory :
    (x y : obj-Subprecategory C P) →
    subtype l4
      ( hom-Precategory C
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y))
  subtype-hom-obj-subprecategory-Subprecategory = {!!}

  hom-Subprecategory : (x y : obj-Subprecategory C P) → UU (l2 ⊔ l4)
  hom-Subprecategory x y = {!!}

  inclusion-hom-Subprecategory :
    (x y : obj-Subprecategory C P) →
    hom-Subprecategory x y →
    hom-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
  inclusion-hom-Subprecategory = {!!}
```

The predicate on a morphism between subobjects of being contained in the
subprecategory:

```agda
  is-in-hom-obj-subprecategory-Subprecategory :
    ( x y : obj-Subprecategory C P) →
    hom-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y) →
    UU l4
  is-in-hom-obj-subprecategory-Subprecategory = {!!}

  is-prop-is-in-hom-obj-subprecategory-Subprecategory :
    ( x y : obj-Subprecategory C P)
    ( f :
      hom-Precategory C
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y)) →
    is-prop (is-in-hom-obj-subprecategory-Subprecategory x y f)
  is-prop-is-in-hom-obj-subprecategory-Subprecategory = {!!}
```

The predicate on a morphism between any objects of being contained in the
subprecategory:

```agda
  is-in-hom-Subprecategory :
    (x y : obj-Precategory C) (f : hom-Precategory C x y) → UU (l3 ⊔ l4)
  is-in-hom-Subprecategory = {!!}

  is-prop-is-in-hom-Subprecategory :
    (x y : obj-Precategory C) (f : hom-Precategory C x y) →
    is-prop (is-in-hom-Subprecategory x y f)
  is-prop-is-in-hom-Subprecategory = {!!}

  is-in-hom-obj-subprecategory-inclusion-hom-Subprecategory :
    (x y : obj-Subprecategory C P)
    (f : hom-Subprecategory x y) →
    is-in-hom-obj-subprecategory-Subprecategory x y
      ( inclusion-hom-Subprecategory x y f)
  is-in-hom-obj-subprecategory-inclusion-hom-Subprecategory = {!!}

  is-in-hom-inclusion-hom-Subprecategory :
    (x y : obj-Subprecategory C P)
    (f : hom-Subprecategory x y) →
    is-in-hom-Subprecategory
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
      ( inclusion-hom-Subprecategory x y f)
  is-in-hom-inclusion-hom-Subprecategory = {!!}
```

#### Subprecategories are subprecategories

```agda
  is-subprecategory-Subprecategory :
    is-subprecategory C
      ( subtype-obj-Subprecategory C P) (subtype-hom-Subprecategory)
  is-subprecategory-Subprecategory = {!!}

  contains-id-Subprecategory :
    contains-id-subtype-Precategory C
      ( subtype-obj-Subprecategory C P)
      ( subtype-hom-Subprecategory)
  contains-id-Subprecategory = {!!}

  is-closed-under-composition-Subprecategory :
    is-closed-under-composition-subtype-Precategory C
      ( subtype-obj-Subprecategory C P)
      ( subtype-hom-Subprecategory)
  is-closed-under-composition-Subprecategory = {!!}
```

### The underlying precategory of a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  hom-set-Subprecategory : (x y : obj-Subprecategory C P) → Set (l2 ⊔ l4)
  hom-set-Subprecategory x y = {!!}

  is-set-hom-Subprecategory :
    (x y : obj-Subprecategory C P) → is-set (hom-Subprecategory C P x y)
  is-set-hom-Subprecategory = {!!}

  id-hom-Subprecategory :
    {x : obj-Subprecategory C P} → hom-Subprecategory C P x x
  pr1 (id-hom-Subprecategory) = {!!}

  comp-hom-Subprecategory :
    {x y z : obj-Subprecategory C P} →
    hom-Subprecategory C P y z →
    hom-Subprecategory C P x y →
    hom-Subprecategory C P x z
  comp-hom-Subprecategory = {!!}

  associative-comp-hom-Subprecategory :
    {x y z w : obj-Subprecategory C P}
    (h : hom-Subprecategory C P z w)
    (g : hom-Subprecategory C P y z)
    (f : hom-Subprecategory C P x y) →
    comp-hom-Subprecategory {x} {y} {w}
      ( comp-hom-Subprecategory {y} {z} {w} h g)
      ( f) ＝
    comp-hom-Subprecategory {x} {z} {w}
      ( h)
      ( comp-hom-Subprecategory {x} {y} {z} g f)
  associative-comp-hom-Subprecategory = {!!}

  inv-associative-comp-hom-Subprecategory :
    {x y z w : obj-Subprecategory C P}
    (h : hom-Subprecategory C P z w)
    (g : hom-Subprecategory C P y z)
    (f : hom-Subprecategory C P x y) →
    ( comp-hom-Subprecategory {x} {z} {w} h
      ( comp-hom-Subprecategory {x} {y} {z} g f)) ＝
    ( comp-hom-Subprecategory {x} {y} {w}
      ( comp-hom-Subprecategory {y} {z} {w} h g) f)
  inv-associative-comp-hom-Subprecategory = {!!}

  left-unit-law-comp-hom-Subprecategory :
    {x y : obj-Subprecategory C P}
    (f : hom-Subprecategory C P x y) →
    comp-hom-Subprecategory {x} {y} {y} (id-hom-Subprecategory {y}) f ＝ f
  left-unit-law-comp-hom-Subprecategory = {!!}

  right-unit-law-comp-hom-Subprecategory :
    {x y : obj-Subprecategory C P}
    (f : hom-Subprecategory C P x y) →
    comp-hom-Subprecategory {x} {x} {y} f (id-hom-Subprecategory {x}) ＝ f
  right-unit-law-comp-hom-Subprecategory = {!!}

  associative-composition-operation-Subprecategory :
    associative-composition-operation-binary-family-Set hom-set-Subprecategory
  associative-composition-operation-Subprecategory = {!!}

  is-unital-composition-operation-Subprecategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Subprecategory)
      ( comp-hom-Subprecategory)
  is-unital-composition-operation-Subprecategory = {!!}

  precategory-Subprecategory : Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 precategory-Subprecategory = {!!}
```

### The inclusion functor of a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  inclusion-map-Subprecategory :
    map-Precategory (precategory-Subprecategory C P) C
  inclusion-map-Subprecategory = {!!}

  is-functor-inclusion-Subprecategory :
    is-functor-map-Precategory
      ( precategory-Subprecategory C P)
      ( C)
      ( inclusion-map-Subprecategory)
  is-functor-inclusion-Subprecategory = {!!}

  inclusion-Subprecategory :
    functor-Precategory (precategory-Subprecategory C P) C
  inclusion-Subprecategory = {!!}
```

## Properties

### The inclusion functor is an embedding on objects and hom-sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-faithful-inclusion-Subprecategory :
    is-faithful-functor-Precategory
      ( precategory-Subprecategory C P)
      ( C)
      ( inclusion-Subprecategory C P)
  is-faithful-inclusion-Subprecategory = {!!}

  is-emb-obj-inclusion-Subprecategory :
    is-emb
      ( obj-functor-Precategory
        ( precategory-Subprecategory C P)
        ( C)
        ( inclusion-Subprecategory C P))
  is-emb-obj-inclusion-Subprecategory = {!!}
```

## See also

- [Large subprecategories](category-theory.large-subprecategories.md)
- [Subcategories](category-theory.subcategories.md)

## External links

- [subcategory](https://ncatlab.org/nlab/show/subcategory) at $n$Lab
- [Subcategory](https://en.wikipedia.org/wiki/Subcategory) at Wikipedia
- [Subcategory](https://mathworld.wolfram.com/Subcategory.html) at Wolfram
  MathWorld
