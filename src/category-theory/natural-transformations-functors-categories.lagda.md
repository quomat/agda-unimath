# Natural transformations between functors between categories

```agda
module category-theory.natural-transformations-functors-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.natural-transformations-functors-precategories

open import foundation.embeddings
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **natural transformation** between
[functors between categories](category-theory.functors-categories.md) is a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
between the [functors](category-theory.functors-precategories.md) on the
underlying [precategories](category-theory.precategories.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : functor-Category C D)
  where

  hom-family-functor-Category : UU (l1 ⊔ l4)
  hom-family-functor-Category = {!!}

  is-natural-transformation-Category :
    hom-family-functor-Category → UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Category = {!!}

  natural-transformation-Category : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Category = {!!}

  hom-family-natural-transformation-Category :
    natural-transformation-Category → hom-family-functor-Category
  hom-family-natural-transformation-Category = {!!}

  naturality-natural-transformation-Category :
    (γ : natural-transformation-Category) →
    is-natural-transformation-Category
      ( hom-family-natural-transformation-Category γ)
  naturality-natural-transformation-Category = {!!}
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  where

  id-natural-transformation-Category :
    (F : functor-Category C D) → natural-transformation-Category C D F F
  id-natural-transformation-Category = {!!}

  comp-natural-transformation-Category :
    (F G H : functor-Category C D) →
    natural-transformation-Category C D G H →
    natural-transformation-Category C D F G →
    natural-transformation-Category C D F H
  comp-natural-transformation-Category = {!!}
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : functor-Category C D)
  where

  is-prop-is-natural-transformation-Category :
    ( γ : hom-family-functor-Category C D F G) →
    is-prop (is-natural-transformation-Category C D F G γ)
  is-prop-is-natural-transformation-Category = {!!}

  is-natural-transformation-prop-Category :
    ( γ : hom-family-functor-Category C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-prop-Category = {!!}
```

### The set of natural transformations

```agda
  is-emb-hom-family-natural-transformation-Category :
    is-emb (hom-family-natural-transformation-Category C D F G)
  is-emb-hom-family-natural-transformation-Category = {!!}

  is-set-natural-transformation-Category :
    is-set (natural-transformation-Category C D F G)
  is-set-natural-transformation-Category = {!!}

  natural-transformation-set-Category : Set (l1 ⊔ l2 ⊔ l4)
  natural-transformation-set-Category = {!!}

  extensionality-natural-transformation-Category :
    (α β : natural-transformation-Category C D F G) →
    ( α ＝ β) ≃
    ( hom-family-natural-transformation-Category C D F G α ~
      hom-family-natural-transformation-Category C D F G β)
  extensionality-natural-transformation-Category = {!!}

  eq-htpy-hom-family-natural-transformation-Category :
    (α β : natural-transformation-Category C D F G) →
    ( hom-family-natural-transformation-Category C D F G α ~
      hom-family-natural-transformation-Category C D F G β) →
    α ＝ β
  eq-htpy-hom-family-natural-transformation-Category = {!!}
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  where

  right-unit-law-comp-natural-transformation-Category :
    {F G : functor-Category C D}
    (α : natural-transformation-Category C D F G) →
    comp-natural-transformation-Category C D F F G α
      ( id-natural-transformation-Category C D F) ＝ α
  right-unit-law-comp-natural-transformation-Category {F} {G} = {!!}

  left-unit-law-comp-natural-transformation-Category :
    {F G : functor-Category C D}
    (α : natural-transformation-Category C D F G) →
    comp-natural-transformation-Category C D F G G
      ( id-natural-transformation-Category C D G) α ＝ α
  left-unit-law-comp-natural-transformation-Category {F} {G} = {!!}

  associative-comp-natural-transformation-Category :
    (F G H I : functor-Category C D)
    (α : natural-transformation-Category C D F G)
    (β : natural-transformation-Category C D G H)
    (γ : natural-transformation-Category C D H I) →
    comp-natural-transformation-Category C D F G I
      ( comp-natural-transformation-Category C D G H I γ β) α ＝
    comp-natural-transformation-Category C D F H I γ
      ( comp-natural-transformation-Category C D F G H β α)
  associative-comp-natural-transformation-Category = {!!}
```
