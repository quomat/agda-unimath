# Natural transformations between maps from small to large precategories

```agda
module category-theory.natural-transformations-maps-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategories
open import category-theory.large-precategories
open import category-theory.maps-from-small-to-large-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a small [precategory](category-theory.precategories.md) `C` and a
[large precategory](category-theory.large-precategories.md) `D`, a **natural
transformation** from a
[map of precategories](category-theory.maps-from-small-to-large-precategories.md)
`F : C → D` to `G : C → D` consists of :

- a family of morphisms `a : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (a x) = {!!}

## Definition

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : map-Small-Large-Precategory C D γF)
  (G : map-Small-Large-Precategory C D γG)
  where

  hom-family-map-Small-Large-Precategory : UU (l1 ⊔ β γF γG)
  hom-family-map-Small-Large-Precategory = {!!}

  naturality-hom-family-map-Small-Large-Precategory :
    hom-family-map-Small-Large-Precategory →
    {x y : obj-Precategory C} (f : hom-Precategory C x y) → UU (β γF γG)
  naturality-hom-family-map-Small-Large-Precategory = {!!}

  is-natural-transformation-map-Small-Large-Precategory :
    hom-family-map-Small-Large-Precategory → UU (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-map-Small-Large-Precategory = {!!}

  natural-transformation-map-Small-Large-Precategory : UU (l1 ⊔ l2 ⊔ β γF γG)
  natural-transformation-map-Small-Large-Precategory = {!!}

  hom-natural-transformation-map-Small-Large-Precategory :
    natural-transformation-map-Small-Large-Precategory →
    hom-family-map-Small-Large-Precategory
  hom-natural-transformation-map-Small-Large-Precategory = {!!}

  naturality-natural-transformation-map-Small-Large-Precategory :
    (γ : natural-transformation-map-Small-Large-Precategory) →
    is-natural-transformation-map-Small-Large-Precategory
      ( hom-natural-transformation-map-Small-Large-Precategory γ)
  naturality-natural-transformation-map-Small-Large-Precategory = {!!}
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  id-natural-transformation-map-Small-Large-Precategory :
    {γF : Level} (F : map-Small-Large-Precategory C D γF) →
    natural-transformation-map-Small-Large-Precategory C D F F
  id-natural-transformation-map-Small-Large-Precategory = {!!}

  comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG γH : Level}
    (F : map-Small-Large-Precategory C D γF) →
    (G : map-Small-Large-Precategory C D γG) →
    (H : map-Small-Large-Precategory C D γH) →
    natural-transformation-map-Small-Large-Precategory C D G H →
    natural-transformation-map-Small-Large-Precategory C D F G →
    natural-transformation-map-Small-Large-Precategory C D F H
  comp-natural-transformation-map-Small-Large-Precategory = {!!}
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : map-Small-Large-Precategory C D γF)
  (G : map-Small-Large-Precategory C D γG)
  where

  is-prop-is-natural-transformation-map-Small-Large-Precategory :
    (a : hom-family-map-Small-Large-Precategory C D F G) →
    is-prop (is-natural-transformation-map-Small-Large-Precategory C D F G a)
  is-prop-is-natural-transformation-map-Small-Large-Precategory = {!!}

  is-natural-transformation-prop-map-Small-Large-Precategory :
    (a : hom-family-map-Small-Large-Precategory C D F G) →
    Prop (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-prop-map-Small-Large-Precategory = {!!}
```

### The set of natural transformations

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : map-Small-Large-Precategory C D γF)
  (G : map-Small-Large-Precategory C D γG)
  where

  is-emb-hom-natural-transformation-map-Small-Large-Precategory :
    is-emb
      ( hom-natural-transformation-map-Small-Large-Precategory C D F G)
  is-emb-hom-natural-transformation-map-Small-Large-Precategory = {!!}

  emb-hom-natural-transformation-map-Small-Large-Precategory :
    natural-transformation-map-Small-Large-Precategory C D F G ↪
    hom-family-map-Small-Large-Precategory C D F G
  emb-hom-natural-transformation-map-Small-Large-Precategory = {!!}

  is-set-natural-transformation-map-Small-Large-Precategory :
    is-set (natural-transformation-map-Small-Large-Precategory C D F G)
  is-set-natural-transformation-map-Small-Large-Precategory = {!!}

  natural-transformation-map-set-Small-Large-Precategory :
    Set (l1 ⊔ l2 ⊔ β γF γG)
  pr1 (natural-transformation-map-set-Small-Large-Precategory) = {!!}

  extensionality-natural-transformation-map-Small-Large-Precategory :
    (α β : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( α ＝ β) ≃
    ( hom-natural-transformation-map-Small-Large-Precategory C D F G α ~
      hom-natural-transformation-map-Small-Large-Precategory C D F G β)
  extensionality-natural-transformation-map-Small-Large-Precategory = {!!}

  eq-htpy-hom-natural-transformation-map-Small-Large-Precategory :
    (α β : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( hom-natural-transformation-map-Small-Large-Precategory C D F G α ~
      hom-natural-transformation-map-Small-Large-Precategory C D F G β) →
    α ＝ β
  eq-htpy-hom-natural-transformation-map-Small-Large-Precategory = {!!}
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  right-unit-law-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    comp-natural-transformation-map-Small-Large-Precategory C D F F G a
      ( id-natural-transformation-map-Small-Large-Precategory C D F) ＝ a
  right-unit-law-comp-natural-transformation-map-Small-Large-Precategory = {!!}

  left-unit-law-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G G
      ( id-natural-transformation-map-Small-Large-Precategory C D G) a ＝ a
  left-unit-law-comp-natural-transformation-map-Small-Large-Precategory = {!!}

  associative-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG γH γI : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (H : map-Small-Large-Precategory C D γH)
    (I : map-Small-Large-Precategory C D γI)
    (a : natural-transformation-map-Small-Large-Precategory C D F G)
    (b : natural-transformation-map-Small-Large-Precategory C D G H)
    (c : natural-transformation-map-Small-Large-Precategory C D H I) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I c b)
      ( a) ＝
    comp-natural-transformation-map-Small-Large-Precategory C D F H I c
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G H b a)
  associative-comp-natural-transformation-map-Small-Large-Precategory = {!!}

  inv-associative-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG γH γI : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (H : map-Small-Large-Precategory C D γH)
    (I : map-Small-Large-Precategory C D γI)
    (a : natural-transformation-map-Small-Large-Precategory C D F G)
    (b : natural-transformation-map-Small-Large-Precategory C D G H)
    (c : natural-transformation-map-Small-Large-Precategory C D H I) →
    comp-natural-transformation-map-Small-Large-Precategory C D F H I c
      ( comp-natural-transformation-map-Small-Large-Precategory
        C D F G H b a) ＝
    comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I c b)
      ( a)
  inv-associative-comp-natural-transformation-map-Small-Large-Precategory = {!!}
```
