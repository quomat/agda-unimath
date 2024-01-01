# Embeddings between precategories

```agda
module category-theory.embeddings-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.embedding-maps-precategories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is an
**embedding** if it's an [embedding](foundation-core.embeddings.md) on objects
and [fully faithful](category-theory.fully-faithful-functors-precategories.md).
Hence embeddings are functors that are embeddings on objects and
[equivalences](foundation-core.equivalences.md) on
hom-[sets](foundation-core.sets.md).

## Definition

### The predicate of being an embedding on maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-embedding-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-prop-map-Precategory = {!!}

  is-embedding-map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-map-Precategory = {!!}

  is-prop-is-embedding-map-Precategory : is-prop is-embedding-map-Precategory
  is-prop-is-embedding-map-Precategory = {!!}
```

### The predicate of being an embedding on functors between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-embedding-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-prop-functor-Precategory = {!!}

  is-embedding-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-functor-Precategory = {!!}

  is-prop-is-embedding-functor-Precategory :
    is-prop is-embedding-functor-Precategory
  is-prop-is-embedding-functor-Precategory = {!!}
```

### The type of embeddings between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  embedding-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  embedding-Precategory = {!!}

  functor-embedding-Precategory :
    embedding-Precategory → functor-Precategory C D
  functor-embedding-Precategory = {!!}

  is-embedding-embedding-Precategory :
    (e : embedding-Precategory) →
    is-embedding-functor-Precategory C D (functor-embedding-Precategory e)
  is-embedding-embedding-Precategory = {!!}
```
