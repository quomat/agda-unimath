# Opposite large precategories

```agda
module category-theory.opposite-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a [large precategory](category-theory.large-precategories.md), its
**opposite large precategory** `Cᵒᵖ` is given by reversing every morphism.

## Definition

### The opposite large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (C : Large-Precategory α β)
  where

  obj-opposite-Large-Precategory : (l : Level) → UU (α l)
  obj-opposite-Large-Precategory = {!!}

  hom-set-opposite-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-opposite-Large-Precategory l1)
    (Y : obj-opposite-Large-Precategory l2) → Set (β l2 l1)
  hom-set-opposite-Large-Precategory = {!!}

  hom-opposite-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-opposite-Large-Precategory l1)
    (Y : obj-opposite-Large-Precategory l2) → UU (β l2 l1)
  hom-opposite-Large-Precategory = {!!}

  comp-hom-opposite-Large-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    {Z : obj-opposite-Large-Precategory l3} →
    hom-opposite-Large-Precategory Y Z →
    hom-opposite-Large-Precategory X Y →
    hom-opposite-Large-Precategory X Z
  comp-hom-opposite-Large-Precategory = {!!}

  associative-comp-hom-opposite-Large-Precategory :
    {l1 l2 l3 l4 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    {Z : obj-opposite-Large-Precategory l3}
    {W : obj-opposite-Large-Precategory l4}
    (h : hom-opposite-Large-Precategory Z W)
    (g : hom-opposite-Large-Precategory Y Z)
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory
      ( comp-hom-opposite-Large-Precategory h g)
      ( f) ＝
    comp-hom-opposite-Large-Precategory
      ( h)
      ( comp-hom-opposite-Large-Precategory g f)
  associative-comp-hom-opposite-Large-Precategory = {!!}

  inv-associative-comp-hom-opposite-Large-Precategory :
    {l1 l2 l3 l4 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    {Z : obj-opposite-Large-Precategory l3}
    {W : obj-opposite-Large-Precategory l4}
    (h : hom-opposite-Large-Precategory Z W)
    (g : hom-opposite-Large-Precategory Y Z)
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory
      ( h)
      ( comp-hom-opposite-Large-Precategory g f) ＝
    comp-hom-opposite-Large-Precategory
      ( comp-hom-opposite-Large-Precategory h g)
      ( f)
  inv-associative-comp-hom-opposite-Large-Precategory = {!!}

  id-hom-opposite-Large-Precategory :
    {l1 : Level} {X : obj-opposite-Large-Precategory l1} →
    hom-opposite-Large-Precategory X X
  id-hom-opposite-Large-Precategory = {!!}

  left-unit-law-comp-hom-opposite-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory id-hom-opposite-Large-Precategory f ＝ f
  left-unit-law-comp-hom-opposite-Large-Precategory = {!!}

  right-unit-law-comp-hom-opposite-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory f id-hom-opposite-Large-Precategory ＝ f
  right-unit-law-comp-hom-opposite-Large-Precategory = {!!}

  opposite-Large-Precategory : Large-Precategory α (λ l1 l2 → β l2 l1)
  opposite-Large-Precategory = {!!}
```

## Properties

### Computing the isomorphism sets of the opposite large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {l1 l2 : Level}
  (C : Large-Precategory α β)
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  map-compute-iso-opposite-Large-Precategory :
    iso-Large-Precategory C X Y →
    iso-Large-Precategory (opposite-Large-Precategory C) Y X
  map-compute-iso-opposite-Large-Precategory = {!!}

  map-inv-compute-iso-opposite-Large-Precategory :
    iso-Large-Precategory (opposite-Large-Precategory C) Y X →
    iso-Large-Precategory C X Y
  map-inv-compute-iso-opposite-Large-Precategory = {!!}

  is-equiv-map-compute-iso-opposite-Large-Precategory :
    is-equiv (map-compute-iso-opposite-Large-Precategory)
  pr1 (pr1 is-equiv-map-compute-iso-opposite-Large-Precategory) = {!!}

  compute-iso-opposite-Large-Precategory :
    iso-Large-Precategory C X Y ≃
    iso-Large-Precategory (opposite-Large-Precategory C) Y X
  compute-iso-opposite-Large-Precategory = {!!}
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
