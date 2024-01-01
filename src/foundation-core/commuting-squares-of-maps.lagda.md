# Commuting squares of maps

```agda
module foundation-core.commuting-squares-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A square of maps

```text
  A ------> X
  |         |
  |         |
  |         |
  V         V
  B ------> Y
```

is said to commute if there is a homotopy between both composites.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (top : C → B) (left : C → A) (right : B → X) (bottom : A → X)
  where

  coherence-square-maps : UU (l3 ⊔ l4)
  coherence-square-maps = {!!}

  coherence-square-maps' : UU (l3 ⊔ l4)
  coherence-square-maps' = {!!}
```

## Properties

### Pasting commuting squares horizontally

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top-left : A → B) (top-right : B → C)
  (left : A → X) (mid : B → Y) (right : C → Z)
  (bottom-left : X → Y) (bottom-right : Y → Z)
  where

  pasting-horizontal-coherence-square-maps :
    coherence-square-maps top-left left mid bottom-left →
    coherence-square-maps top-right mid right bottom-right →
    coherence-square-maps
      (top-right ∘ top-left) left right (bottom-right ∘ bottom-left)
  pasting-horizontal-coherence-square-maps = {!!}

  pasting-horizontal-up-to-htpy-coherence-square-maps :
    {top : A → C} (H : coherence-triangle-maps top top-right top-left)
    {bottom : X → Z}
    (K : coherence-triangle-maps bottom bottom-right bottom-left) →
    coherence-square-maps top-left left mid bottom-left →
    coherence-square-maps top-right mid right bottom-right →
    coherence-square-maps top left right bottom
  pasting-horizontal-up-to-htpy-coherence-square-maps = {!!}
```

### Pasting commuting squares vertically

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top : A → X)
  (left-top : A → B) (right-top : X → Y)
  (mid : B → Y)
  (left-bottom : B → C) (right-bottom : Y → Z)
  (bottom : C → Z)
  where

  pasting-vertical-coherence-square-maps :
    coherence-square-maps top left-top right-top mid →
    coherence-square-maps mid left-bottom right-bottom bottom →
    coherence-square-maps
      top (left-bottom ∘ left-top) (right-bottom ∘ right-top) bottom
  pasting-vertical-coherence-square-maps = {!!}

  pasting-vertical-up-to-htpy-coherence-square-maps :
    {left : A → C} (H : coherence-triangle-maps left left-bottom left-top)
    {right : X → Z} (K : coherence-triangle-maps right right-bottom right-top) →
    coherence-square-maps top left-top right-top mid →
    coherence-square-maps mid left-bottom right-bottom bottom →
    coherence-square-maps top left right bottom
  pasting-vertical-up-to-htpy-coherence-square-maps = {!!}
```

### Associativity of horizontal pasting

**Proof:** Consider a commuting diagram of the form

```text
        α₀       β₀       γ₀
    A -----> X -----> U -----> K
    |        |        |        |
  f |   α  g |   β  h |   γ    | i
    V        V        V        V
    B -----> Y -----> V -----> L.
        α₁       β₁       γ₁
```

Then we can make the following calculation, in which we write `□` for horizontal
pasting of squares:

```text
  (α □ β) □ γ
  ＝ (γ₁ ·l ((β₁ ·l α) ∙h (β ·r α₀))) ∙h (γ ·r (β₀ ∘ α₀))
  ＝ ((γ₁ ·l (β₁ ·l α)) ∙h (γ₁ ·l (β ·r α₀))) ∙h (γ ·r (β₀ ∘ α₀))
  ＝ ((γ₁ ∘ β₁) ·l α) ∙h (((γ₁ ·l β) ·r α₀) ∙h ((γ ·r β₀) ·r α₀))
  ＝ ((γ₁ ∘ β₁) ·l α) ∙h (((γ₁ ·l β) ∙h (γ ·r β₀)) ·r α₀)
  ＝ α □ (β □ γ)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  {K : UU l7} {L : UU l8}
  (α₀ : A → X) (β₀ : X → U) (γ₀ : U → K)
  (f : A → B) (g : X → Y) (h : U → V) (i : K → L)
  (α₁ : B → Y) (β₁ : Y → V) (γ₁ : V → L)
  (α : coherence-square-maps α₀ f g α₁)
  (β : coherence-square-maps β₀ g h β₁)
  (γ : coherence-square-maps γ₀ h i γ₁)
  where

  assoc-pasting-horizontal-coherence-square-maps :
    pasting-horizontal-coherence-square-maps
      ( β₀ ∘ α₀)
      ( γ₀)
      ( f)
      ( h)
      ( i)
      ( β₁ ∘ α₁)
      ( γ₁)
      ( pasting-horizontal-coherence-square-maps α₀ β₀ f g h α₁ β₁ α β)
      ( γ) ~
    pasting-horizontal-coherence-square-maps
      ( α₀)
      ( γ₀ ∘ β₀)
      ( f)
      ( g)
      ( i)
      ( α₁)
      ( γ₁ ∘ β₁)
      ( α)
      ( pasting-horizontal-coherence-square-maps β₀ γ₀ g h i β₁ γ₁ β γ)
  assoc-pasting-horizontal-coherence-square-maps = {!!}
```

### The unit laws for horizontal pasting of commuting squares of maps

#### The left unit law

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : A → X) (f : A → B) (g : X → Y) (j : B → Y)
  (α : coherence-square-maps i f g j)
  where

  left-unit-law-pasting-horizontal-coherence-square-maps :
    pasting-horizontal-coherence-square-maps id i f f g id j refl-htpy α ~ α
  left-unit-law-pasting-horizontal-coherence-square-maps = {!!}
```

### The right unit law

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : A → X) (f : A → B) (g : X → Y) (j : B → Y)
  (α : coherence-square-maps i f g j)
  where

  right-unit-law-pasting-horizontal-coherence-square-maps :
    pasting-horizontal-coherence-square-maps i id f g g j id α refl-htpy ~ α
  right-unit-law-pasting-horizontal-coherence-square-maps = {!!}
```

## See also

Several structures make essential use of commuting squares of maps:

- [Cones over cospans](foundation.cones-over-cospans.md)
- [Cocones under spans](synthetic-homotopy-theory.cocones-under-spans.md)
- [Morphisms of arrows](foundation.morphisms-arrows.md)
