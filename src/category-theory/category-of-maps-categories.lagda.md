# The category of maps and natural transformations between two categories

```agda
module category-theory.category-of-maps-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-categories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-maps-categories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories
open import category-theory.precategory-of-maps-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-maps-categories.md)
between them form another category whose identity map and composition structure
are inherited pointwise from the codomain category. This is called the
**category of maps between categories**.

## Lemmas

### Extensionality of maps of precategories when the codomain is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  equiv-natural-isomorphism-htpy-map-is-category-Precategory :
    (F G : map-Precategory C D) →
    ( htpy-map-Precategory C D F G) ≃
    ( natural-isomorphism-map-Precategory C D F G)
  equiv-natural-isomorphism-htpy-map-is-category-Precategory = {!!}

  extensionality-map-is-category-Precategory :
    (F G : map-Precategory C D) →
    ( F ＝ G) ≃
    ( natural-isomorphism-map-Precategory C D F G)
  extensionality-map-is-category-Precategory = {!!}
```

### When the codomain is a category the map precategory is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  abstract
    is-category-map-precategory-is-category-Precategory :
      is-category-Precategory (map-precategory-Precategory C D)
    is-category-map-precategory-is-category-Precategory = {!!}
```

## Definitions

### The category of maps and natural transformations between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2) (D : Category l3 l4)
  where

  map-category-Category :
    Category (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  map-category-Category = {!!}

  extensionality-map-Category :
    (F G : map-Category C D) →
    (F ＝ G) ≃ natural-isomorphism-map-Category C D F G
  extensionality-map-Category = {!!}

  eq-natural-isomorphism-map-Category :
    (F G : map-Category C D) →
    natural-isomorphism-map-Category C D F G → F ＝ G
  eq-natural-isomorphism-map-Category = {!!}
```
