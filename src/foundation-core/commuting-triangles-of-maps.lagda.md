# Commuting triangles of maps

```agda
module foundation-core.commuting-triangles-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A triangle of maps

```text
        top
     A ----> B
      \     /
  left \   / right
        V V
         X
```

is said to **commute** if there is a [homotopy](foundation-core.homotopies.md)
between the map on the left and the composite of the top and right maps:

```text
  left ~ right ∘ top.
```

## Definitions

### Commuting triangles of maps

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  coherence-triangle-maps :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps = {!!}

  coherence-triangle-maps' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps' = {!!}
```

### Concatenation of commuting triangles of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) (i : A → B) (j : B → C)
  where

  concat-coherence-triangle-maps :
    coherence-triangle-maps f g i →
    coherence-triangle-maps g h j →
    coherence-triangle-maps f h (j ∘ i)
  concat-coherence-triangle-maps = {!!}
```

### Coherences of commuting triangles of maps with fixed vertices

This or its opposite should be the coherence in the characterization of
identifications of commuting triangles of maps with fixed end vertices.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (top : A → B)
  (left' : A → X) (right' : B → X) (top' : A → B)
  (c : coherence-triangle-maps left right top)
  (c' : coherence-triangle-maps left' right' top')
  where

  coherence-htpy-triangle-maps :
    left ~ left' → right ~ right' → top ~ top' → UU (l1 ⊔ l2)
  coherence-htpy-triangle-maps = {!!}
```

## Properties

### If the top map has a section, then the reversed triangle with the section on top commutes

If `t : B → A` is a [section](foundation-core.sections.md) of the top map `h`,
then the triangle

```text
       t
  B ------> A
   \       /
   g\     /f
     \   /
      V V
       X
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  (t : section h)
  where

  inv-triangle-section : coherence-triangle-maps' g f (map-section h t)
  inv-triangle-section = {!!}

  triangle-section : coherence-triangle-maps g f (map-section h t)
  triangle-section = {!!}
```

### If the right map has a retraction, then the reversed triangle with the retraction on the right commutes

If `r : X → B` is a retraction of the right map `g` in a triangle `f ~ g ∘ h`,
then the triangle

```text
       f
  A ------> X
   \       /
   h\     /r
     \   /
      V V
       B
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  (r : retraction g)
  where

  inv-triangle-retraction : coherence-triangle-maps' h (map-retraction g r) f
  inv-triangle-retraction = {!!}

  triangle-retraction : coherence-triangle-maps h (map-retraction g r) f
  triangle-retraction = {!!}
```
