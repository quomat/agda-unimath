# The category of functors and natural transformations between two categories

```agda
module category-theory.category-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.category-of-maps-categories
open import category-theory.functors-categories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.natural-isomorphisms-functors-categories
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-functors-categories.md)
between them assemble to a new category whose identity functor and composition
structure are inherited pointwise from the codomain category. This is called the
**category of functors**.

## Definitons

### Extensionality of functors of precategories when the codomain is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  equiv-natural-isomorphism-htpy-functor-is-category-Precategory :
    (F G : functor-Precategory C D) →
    htpy-functor-Precategory C D F G ≃ natural-isomorphism-Precategory C D F G
  equiv-natural-isomorphism-htpy-functor-is-category-Precategory F G = {!!}

  extensionality-functor-is-category-Precategory :
    (F G : functor-Precategory C D) →
    ( F ＝ G) ≃
    ( natural-isomorphism-Precategory C D F G)
  extensionality-functor-is-category-Precategory F G = {!!}
```

### When the codomain is a category the functor precategory is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  abstract
    is-category-functor-precategory-is-category-Precategory :
      is-category-Precategory (functor-precategory-Precategory C D)
    is-category-functor-precategory-is-category-Precategory F G = {!!}
```

## Definitions

### The category of functors and natural transformations between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2) (D : Category l3 l4)
  where

  functor-category-Category :
    Category (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-category-Category = {!!}

  extensionality-functor-Category :
    (F G : functor-Category C D) →
    (F ＝ G) ≃ natural-isomorphism-Category C D F G
  extensionality-functor-Category F G = {!!}

  eq-natural-isomorphism-functor-Category :
    (F G : functor-Category C D) →
    natural-isomorphism-Category C D F G → F ＝ G
  eq-natural-isomorphism-functor-Category F G = {!!}
```
