# Full subprecategories

```agda
module category-theory.full-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.embeddings-precategories
open import category-theory.fully-faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **full subprecategory** of a [precategory](category-theory.precategories.md)
`C` consists of a [subtype](foundation-core.subtypes.md) `P₀` of the objects of
`C`.

Alternatively, we say that a
[subprecategory](category-theory.subprecategories.md) **is full** if for every
two objects `X` and `Y` in the subprecategory, the subtype of morphisms from `X`
to `Y` in the subprecategory is [full](foundation.full-subtypes.md).

## Definitions

### Full subprecategories

```agda
Full-Subprecategory :
  {l1 l2 : Level} (l3 : Level) (C : Precategory l1 l2) → UU (l1 ⊔ lsuc l3)
Full-Subprecategory l3 C = {!!}

module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Full-Subprecategory l3 C)
  where

  subtype-obj-Full-Subprecategory : subtype l3 (obj-Precategory C)
  subtype-obj-Full-Subprecategory = {!!}

  obj-Full-Subprecategory : UU (l1 ⊔ l3)
  obj-Full-Subprecategory = {!!}

  inclusion-obj-Full-Subprecategory :
    obj-Full-Subprecategory → obj-Precategory C
  inclusion-obj-Full-Subprecategory = {!!}

  is-in-obj-Full-Subprecategory : (x : obj-Precategory C) → UU l3
  is-in-obj-Full-Subprecategory = {!!}

  is-prop-is-in-obj-Full-Subprecategory :
    (x : obj-Precategory C) → is-prop (is-in-obj-Full-Subprecategory x)
  is-prop-is-in-obj-Full-Subprecategory = {!!}

  is-in-obj-inclusion-obj-Full-Subprecategory :
    (x : obj-Full-Subprecategory) →
    is-in-obj-Full-Subprecategory (inclusion-obj-Full-Subprecategory x)
  is-in-obj-inclusion-obj-Full-Subprecategory = {!!}
```

### The underlying precategory of a full subprecategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Full-Subprecategory l3 C)
  where

  hom-set-Full-Subprecategory : (x y : obj-Full-Subprecategory C P) → Set l2
  hom-set-Full-Subprecategory x y = {!!}

  hom-Full-Subprecategory : (x y : obj-Full-Subprecategory C P) → UU l2
  hom-Full-Subprecategory x y = {!!}

  is-set-hom-Full-Subprecategory :
    (x y : obj-Full-Subprecategory C P) → is-set (hom-Full-Subprecategory x y)
  is-set-hom-Full-Subprecategory x y = {!!}

  id-hom-Full-Subprecategory :
    {x : obj-Full-Subprecategory C P} → hom-Full-Subprecategory x x
  id-hom-Full-Subprecategory = {!!}

  comp-hom-Full-Subprecategory :
    {x y z : obj-Full-Subprecategory C P} →
    hom-Full-Subprecategory y z →
    hom-Full-Subprecategory x y →
    hom-Full-Subprecategory x z
  comp-hom-Full-Subprecategory = {!!}

  associative-comp-hom-Full-Subprecategory :
    {x y z w : obj-Full-Subprecategory C P}
    (h : hom-Full-Subprecategory z w)
    (g : hom-Full-Subprecategory y z)
    (f : hom-Full-Subprecategory x y) →
    comp-hom-Full-Subprecategory {x} {y} {w}
      ( comp-hom-Full-Subprecategory {y} {z} {w} h g)
      ( f) ＝
    comp-hom-Full-Subprecategory {x} {z} {w}
      ( h)
      ( comp-hom-Full-Subprecategory {x} {y} {z} g f)
  associative-comp-hom-Full-Subprecategory = {!!}

  inv-associative-comp-hom-Full-Subprecategory :
    {x y z w : obj-Full-Subprecategory C P}
    (h : hom-Full-Subprecategory z w)
    (g : hom-Full-Subprecategory y z)
    (f : hom-Full-Subprecategory x y) →
    comp-hom-Full-Subprecategory {x} {z} {w}
      ( h)
      ( comp-hom-Full-Subprecategory {x} {y} {z} g f) ＝
    comp-hom-Full-Subprecategory {x} {y} {w}
      ( comp-hom-Full-Subprecategory {y} {z} {w} h g)
      ( f)
  inv-associative-comp-hom-Full-Subprecategory = {!!}

  left-unit-law-comp-hom-Full-Subprecategory :
    {x y : obj-Full-Subprecategory C P}
    (f : hom-Full-Subprecategory x y) →
    comp-hom-Full-Subprecategory {x} {y} {y}
      ( id-hom-Full-Subprecategory {y})
      ( f) ＝
    f
  left-unit-law-comp-hom-Full-Subprecategory = {!!}

  right-unit-law-comp-hom-Full-Subprecategory :
    {x y : obj-Full-Subprecategory C P}
    (f : hom-Full-Subprecategory x y) →
    comp-hom-Full-Subprecategory {x} {x} {y}
      ( f)
      ( id-hom-Full-Subprecategory {x}) ＝
    f
  right-unit-law-comp-hom-Full-Subprecategory = {!!}

  associative-composition-operation-Full-Subprecategory :
    associative-composition-operation-binary-family-Set
      hom-set-Full-Subprecategory
  pr1 associative-composition-operation-Full-Subprecategory {x} {y} {z} = {!!}

  is-unital-composition-operation-Full-Subprecategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Full-Subprecategory)
      ( λ {x} {y} {z} → comp-hom-Full-Subprecategory {x} {y} {z})
  pr1 is-unital-composition-operation-Full-Subprecategory x = {!!}

  precategory-Full-Subprecategory : Precategory (l1 ⊔ l3) l2
  pr1 precategory-Full-Subprecategory = {!!}
```

### Isomorphisms in full subprecategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Full-Subprecategory l3 C)
  where

  iso-Full-Subprecategory :
    (X Y : obj-Full-Subprecategory C P) → UU l2
  iso-Full-Subprecategory X Y = {!!}

  iso-eq-Full-Subprecategory :
    (X Y : obj-Full-Subprecategory C P) → X ＝ Y → iso-Full-Subprecategory X Y
  iso-eq-Full-Subprecategory = {!!}
```

### The inclusion functor of a full subprecategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Full-Subprecategory l3 C)
  where

  inclusion-map-Full-Subprecategory :
    map-Precategory (precategory-Full-Subprecategory C P) C
  pr1 inclusion-map-Full-Subprecategory = {!!}

  is-functor-inclusion-Full-Subprecategory :
    is-functor-map-Precategory
      ( precategory-Full-Subprecategory C P)
      ( C)
      ( inclusion-map-Full-Subprecategory)
  pr1 is-functor-inclusion-Full-Subprecategory g f = {!!}

  inclusion-Full-Subprecategory :
    functor-Precategory (precategory-Full-Subprecategory C P) C
  pr1 inclusion-Full-Subprecategory = {!!}
```

## Properties

### A full subprecategory of a category is a category

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Full-Subprecategory l3 C)
  where

  is-category-precategory-is-category-Full-Subprecategory :
    is-category-Precategory C →
    is-category-Precategory (precategory-Full-Subprecategory C P)
  is-category-precategory-is-category-Full-Subprecategory is-category-C X = {!!}
```

### The inclusion functor is an embedding

```agda
module _
  {l1 l2 l3 : Level}
  (C : Precategory l1 l2)
  (P : Full-Subprecategory l3 C)
  where

  is-fully-faithful-inclusion-Full-Subprecategory :
    is-fully-faithful-functor-Precategory
      ( precategory-Full-Subprecategory C P)
      ( C)
      ( inclusion-Full-Subprecategory C P)
  is-fully-faithful-inclusion-Full-Subprecategory x y = {!!}

  is-emb-obj-inclusion-Full-Subprecategory :
    is-emb
      ( obj-functor-Precategory
        ( precategory-Full-Subprecategory C P)
        ( C)
        ( inclusion-Full-Subprecategory C P))
  is-emb-obj-inclusion-Full-Subprecategory = {!!}

  is-embedding-inclusion-Full-Subprecategory :
    is-embedding-functor-Precategory
      ( precategory-Full-Subprecategory C P)
      ( C)
      ( inclusion-Full-Subprecategory C P)
  pr1 is-embedding-inclusion-Full-Subprecategory = {!!}

  embedding-Full-Subprecategory :
    embedding-Precategory
      ( precategory-Full-Subprecategory C P)
      ( C)
  pr1 embedding-Full-Subprecategory = {!!}
```

## See also

- [Wide subprecategories](category-theory.wide-subprecategories.md)

## External links

- [Full subcategories](https://1lab.dev/Cat.Functor.FullSubcategory.html) at
  1lab
- [full subcategory](https://ncatlab.org/nlab/show/full+subcategory) at $n$Lab
