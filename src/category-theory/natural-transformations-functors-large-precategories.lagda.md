# Natural transformations between functors between large precategories

```agda
module category-theory.natural-transformations-functors-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategories
open import category-theory.functors-large-precategories
open import category-theory.large-precategories

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given [large precategories](category-theory.large-precategories.md) `C` and `D`,
a **natural transformation** from a
[functor](category-theory.functors-large-precategories.md) `F : C → D` to
`G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = {!!}

## Definition

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG C D)
  where

  family-of-morphisms-functor-Large-Precategory : UUω
  family-of-morphisms-functor-Large-Precategory = {!!}

  naturality-family-of-morphisms-functor-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory → UUω
  naturality-family-of-morphisms-functor-Large-Precategory τ = {!!}

  record natural-transformation-Large-Precategory : UUω
    where
    constructor make-natural-transformation
    field
      hom-natural-transformation-Large-Precategory :
        family-of-morphisms-functor-Large-Precategory
      naturality-natural-transformation-Large-Precategory :
        naturality-family-of-morphisms-functor-Large-Precategory
          hom-natural-transformation-Large-Precategory

  open natural-transformation-Large-Precategory public
```

## Properties

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
module _
  { αC αD γF : Level → Level}
  { βC βD : Level → Level → Level}
  ( C : Large-Precategory αC βC)
  ( D : Large-Precategory αD βD)
  ( F : functor-Large-Precategory γF C D)
  where

  hom-id-natural-transformation-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory C D F F
  hom-id-natural-transformation-Large-Precategory X = {!!}

  naturality-id-natural-transformation-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory C D F F
      hom-id-natural-transformation-Large-Precategory
  naturality-id-natural-transformation-Large-Precategory f = {!!}

  id-natural-transformation-Large-Precategory :
    natural-transformation-Large-Precategory C D F F
  hom-natural-transformation-Large-Precategory
    id-natural-transformation-Large-Precategory = {!!}
```

### Composition of natural transformations

```agda
module _
  {αC αD γF γG γH : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG C D)
  (H : functor-Large-Precategory γH C D)
  (τ : natural-transformation-Large-Precategory C D G H)
  (σ : natural-transformation-Large-Precategory C D F G)
  where

  hom-comp-natural-transformation-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory C D F H
  hom-comp-natural-transformation-Large-Precategory X = {!!}

  naturality-comp-natural-transformation-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory C D F H
      hom-comp-natural-transformation-Large-Precategory
  naturality-comp-natural-transformation-Large-Precategory {X = X} {Y} f = {!!}

  comp-natural-transformation-Large-Precategory :
    natural-transformation-Large-Precategory C D F H
  hom-natural-transformation-Large-Precategory
    comp-natural-transformation-Large-Precategory = {!!}
```

## See also

- [Homotopies of natural transformations in large precategories](category-theory.homotopies-natural-transformations-large-precategories.md)
