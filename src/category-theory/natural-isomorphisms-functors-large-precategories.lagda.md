# Natural isomorphisms between functors between large precategories

```agda
module category-theory.natural-isomorphisms-functors-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategories
open import category-theory.functors-large-precategories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-large-precategories

open import foundation.universe-levels
```

</details>

## Idea

A **natural isomorphism** `γ` from
[functor](category-theory.functors-large-precategories.md) `F : C → D` to
`G : C → D` is a
[natural transformation](category-theory.natural-transformations-functors-large-precategories.md)
from `F` to `G` such that the morphism `γ x : hom (F x) (G x)` is an
[isomorphism](category-theory.isomorphisms-in-precategories.md), for every
object `x` in `C`.

## Definition

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG C D)
  where

  iso-family-functor-Large-Precategory : UUω
  iso-family-functor-Large-Precategory = {!!}

  record natural-isomorphism-Large-Precategory : UUω
    where
    constructor make-natural-isomorphism
    field
      iso-natural-isomorphism-Large-Precategory :
        iso-family-functor-Large-Precategory
      iso-natural-isomorphism-Large-Precategory = {!!}
```
