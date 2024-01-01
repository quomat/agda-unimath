# Replete subprecategories

```agda
module category-theory.replete-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphism-induction-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.isomorphisms-in-subprecategories
open import category-theory.precategories
open import category-theory.subprecategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subsingleton-induction
open import foundation.subtypes
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **replete subprecategory** of a [precategory](category-theory.categories.md)
`C` is a [subprecategory](category-theory.subprecategories.md) `P` that is
closed under [isomorphisms](category-theory.isomorphisms-in-precategories.md):

Given an object `x` in `P`, then every isomorphism `f : x ≅ y` in `C`, is
contained in `P`.

## Definitions

### The predicate on a subprecategory of being closed under isomorphic objects

We can define what it means for subprecategories to have objects that are closed
under isomorphisms. Observe that this is not yet the correct definition of a
replete subprecategory.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  contains-iso-obj-Subprecategory : UU (l1 ⊔ l2 ⊔ l3)
  contains-iso-obj-Subprecategory = {!!}

  is-prop-contains-iso-obj-Subprecategory :
    is-prop contains-iso-obj-Subprecategory
  is-prop-contains-iso-obj-Subprecategory = {!!}

  contains-iso-obj-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 contains-iso-obj-prop-Subprecategory = {!!}
```

### The predicate of being a replete subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-replete-Subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-replete-Subprecategory = {!!}

  is-prop-is-replete-Subprecategory :
    is-prop is-replete-Subprecategory
  is-prop-is-replete-Subprecategory = {!!}

  is-replete-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-replete-prop-Subprecategory = {!!}
```

### The type of replete subprecategories

```agda
Replete-Subprecategory :
  {l1 l2 : Level} (l3 l4 : Level) (C : Precategory l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Replete-Subprecategory = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Replete-Subprecategory l3 l4 C)
  where

  subprecategory-Replete-Subprecategory : Subprecategory l3 l4 C
  subprecategory-Replete-Subprecategory = {!!}

  is-replete-Replete-Subprecategory :
    is-replete-Subprecategory C subprecategory-Replete-Subprecategory
  is-replete-Replete-Subprecategory = {!!}
```

## Properties

### A slight reformulation of repleteness

In our main definition of repleteness, the containment proof of the isomorphism
must be fixed at the left end-point. This is of course not necessary, so we can
ask for a slighty relaxed proof of repleteness:

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-unfixed-replete-Subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-unfixed-replete-Subprecategory = {!!}

  is-prop-is-unfixed-replete-Subprecategory :
    is-prop (is-unfixed-replete-Subprecategory)
  is-prop-is-unfixed-replete-Subprecategory = {!!}

  is-unfixed-replete-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-unfixed-replete-prop-Subprecategory = {!!}

  is-unfixed-replete-is-replete-Subprecategory :
    is-replete-Subprecategory C P → is-unfixed-replete-Subprecategory
  is-unfixed-replete-is-replete-Subprecategory = {!!}

  is-replete-is-unfixed-replete-Subprecategory :
    is-unfixed-replete-Subprecategory → is-replete-Subprecategory C P
  is-replete-is-unfixed-replete-Subprecategory = {!!}
```

### Isomorphism-sets in replete subprecategories are equivalent to isomorphism-sets in the base precategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-replete-P : is-replete-Subprecategory C P)
  {x y : obj-Subprecategory C P} (f : hom-Subprecategory C P x y)
  where

  is-iso-is-iso-base-is-replete-Subprecategory :
    is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f) →
    is-iso-Subprecategory C P f
  is-iso-is-iso-base-is-replete-Subprecategory = {!!}

  is-equiv-is-iso-is-iso-base-is-replete-Subprecategory :
    is-equiv is-iso-is-iso-base-is-replete-Subprecategory
  is-equiv-is-iso-is-iso-base-is-replete-Subprecategory = {!!}

  equiv-is-iso-is-iso-base-is-replete-Subprecategory :
    is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f) ≃
    is-iso-Subprecategory C P f
  equiv-is-iso-is-iso-base-is-replete-Subprecategory = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-replete-P : is-replete-Subprecategory C P)
  (x y : obj-Subprecategory C P)
  where

  compute-iso-is-replete-Subprecategory :
    iso-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y) ≃
    iso-Subprecategory C P x y
  compute-iso-is-replete-Subprecategory = {!!}

  inv-compute-iso-is-replete-Subprecategory :
    iso-Subprecategory C P x y ≃
    iso-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
  inv-compute-iso-is-replete-Subprecategory = {!!}
```

### Subprecategories of categories are replete

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-category-C : is-category-Precategory C)
  where

  is-unfixed-replete-subprecategory-is-category-Subprecategory :
    {x : obj-Subprecategory C P}
    {y : obj-Precategory C}
    (f : iso-Precategory C (inclusion-obj-Subprecategory C P x) y) →
    is-in-iso-Subprecategory C P f
  is-unfixed-replete-subprecategory-is-category-Subprecategory = {!!}

  is-replete-subprecategory-is-category-Subprecategory :
    is-replete-Subprecategory C P
  is-replete-subprecategory-is-category-Subprecategory = {!!}
```

### If a full subprecategory is closed under isomorphic objects then it is replete

This remains to be formalized.

### The inclusion functor of a replete subprecategory is pseudomonic

This remains to be formalized.

## See also

- Every [subcategory](category-theory.subcategories.md) is replete.

- Because of universe polymorphism,
  [large subcategories](category-theory.large-subcategories.md) are not large
  replete by construction, although they are levelwise replete.

## External links

- [replete subcategory](https://ncatlab.org/nlab/show/replete+replete-subprecategory)
  at $n$Lab
- [Isomorphism-closed subcategory](https://en.wikipedia.org/wiki/Isomorphism-closed_subcategory)
  at Wikipedia
- [isomorphism-closed subcategory](https://www.wikidata.org/wiki/Q6086096) at
  Wikidata
