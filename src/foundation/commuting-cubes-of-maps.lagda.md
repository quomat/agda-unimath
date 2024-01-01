# Commuting cubes of maps

```agda
module foundation.commuting-cubes-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-hexagons-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

We specify the type of the homotopy witnessing that a cube commutes. Imagine
that the cube is presented as a lattice

```text
            A'
          / | \
         /  |  \
        /   |   \
       B'   A    C'
       |\ /   \ /|
       | \     / |
       |/ \   / \|
       B    D'   C
        \   |   /
         \  |  /
          \ | /
            D
```

with all maps pointing in the downwards direction. Presented in this way, a cube
of maps has a top face, a back-left face, a back-right face, a front-left face,
a front-right face, and a bottom face, all of which are homotopies. An element
of type `coherence-cube-maps` is a homotopy filling the cube.

## Definition

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  where

  coherence-cube-maps :
    (top : (h' ∘ f') ~ (k' ∘ g'))
    (back-left : (f ∘ hA) ~ (hB ∘ f'))
    (back-right : (g ∘ hA) ~ (hC ∘ g'))
    (front-left : (h ∘ hB) ~ (hD ∘ h'))
    (front-right : (k ∘ hC) ~ (hD ∘ k'))
    (bottom : (h ∘ f) ~ (k ∘ g)) →
    UU (l4 ⊔ l1')
  coherence-cube-maps = {!!}
```

### Symmetries of commuting cubes

The symmetry group D₃ acts on a cube. However, the coherence filling a cube
needs to be modified to show that the rotated/reflected cube again commutes. In
the following definitions we provide the homotopies witnessing that the
rotated/reflected cubes again commute.

Note: although in principle it ought to be enough to show this for the
generators of the symmetry group D₃, in practice it is more straightforward to
just do the work for each of the symmetries separately. One reason is that some
of the homotopies witnessing that the faces commute will be inverted as the
result of an application of a symmetry. Inverting a homotopy twice results in a
new homotopy that is only homotopic to the original homotopy.

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : coherence-square-maps g' f' k' h')
  (back-left : coherence-square-maps f' hA hB f)
  (back-right : coherence-square-maps g' hA hC g)
  (front-left : coherence-square-maps h' hB hD h)
  (front-right : coherence-square-maps k' hC hD k)
  (bottom : coherence-square-maps g f k h)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  coherence-cube-maps-rotate-120 :
    coherence-cube-maps hC k' k hD hA f' f hB g' g h' h
      ( back-left)
      ( inv-htpy back-right)
      ( inv-htpy top)
      ( inv-htpy bottom)
      ( inv-htpy front-left)
      ( front-right)
  coherence-cube-maps-rotate-120 = {!!}

  coherence-cube-maps-rotate-240 :
    coherence-cube-maps h' hB hD h g' hA hC g f' k' f k
      ( inv-htpy back-right)
      ( top)
      ( inv-htpy back-left)
      ( inv-htpy front-right)
      ( bottom)
      ( inv-htpy front-left)
  coherence-cube-maps-rotate-240 = {!!}

  coherence-cube-maps-mirror-A :
    coherence-cube-maps g f k h g' f' k' h' hA hC hB hD
      ( inv-htpy top)
      ( back-right)
      ( back-left)
      ( front-right)
      ( front-left)
      ( inv-htpy bottom)
  coherence-cube-maps-mirror-A = {!!}

  coherence-cube-maps-mirror-B :
    coherence-cube-maps hB h' h hD hA g' g hC f' f k' k
      ( back-right)
      ( inv-htpy back-left)
      ( top)
      ( bottom)
      ( inv-htpy front-right)
      ( front-left)
  coherence-cube-maps-mirror-B = {!!}

  coherence-cube-maps-mirror-C :
    coherence-cube-maps k' hC hD k f' hA hB f g' h' g h
      ( inv-htpy back-left)
      ( inv-htpy top)
      ( inv-htpy back-right)
      ( inv-htpy front-left)
      ( inv-htpy bottom)
      ( inv-htpy front-right)
  coherence-cube-maps-mirror-C = {!!}
```

### Rectangles in commuting cubes

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : coherence-square-maps g' f' k' h')
  (back-left : coherence-square-maps f' hA hB f)
  (back-right : coherence-square-maps g' hA hC g)
  (front-left : coherence-square-maps h' hB hD h)
  (front-right : coherence-square-maps k' hC hD k)
  (bottom : coherence-square-maps g f k h)
  where

  rectangle-left-cube :
    ((h ∘ f) ∘ hA) ~ (hD ∘ (h' ∘ f'))
  rectangle-left-cube = {!!}

  rectangle-right-cube :
    ((k ∘ g) ∘ hA) ~ (hD ∘ (k' ∘ g'))
  rectangle-right-cube = {!!}

  coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube :
    (c : coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
    coherence-htpy-parallel-cone
      ( bottom)
      ( refl-htpy' hD)
      ( hA , h' ∘ f' , rectangle-left-cube)
      ( hA , k' ∘ g' , rectangle-right-cube)
      ( refl-htpy' hA)
      ( top)
  coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube = {!!}

  rectangle-top-front-left-cube :
    ((h ∘ hB) ∘ f') ~ ((hD ∘ k') ∘ g')
  rectangle-top-front-left-cube = {!!}

  rectangle-back-right-bottom-cube :
    ((h ∘ f) ∘ hA) ~ ((k ∘ hC) ∘ g')
  rectangle-back-right-bottom-cube = {!!}

  rectangle-top-front-right-cube :
    ((hD ∘ h') ∘ f') ~ ((k ∘ hC) ∘ g')
  rectangle-top-front-right-cube = {!!}

  rectangle-back-left-bottom-cube :
    ((h ∘ hB) ∘ f') ~ ((k ∘ g) ∘ hA)
  rectangle-back-left-bottom-cube = {!!}
```

In analogy to the coherence
`coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube` we also
expect to be able to construct a coherence

```text
  coherence-htpy-parallel-cone-rectangle-top-fl-rectangle-br-bot-cube :
    (c : coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
    coherence-htpy-parallel-cone
      ( inv-htpy front-right)
      ( refl-htpy' h)
      ( g' , hB ∘ f' , inv-htpy (rectangle-top-front-left-cube))
      ( g' , f ∘ hA , inv-htpy (rectangle-back-right-bottom-cube))
      ( refl-htpy' g')
      ( inv-htpy back-left)
```

### Any coherence of commuting cubes induces a coherence of parallel cones

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : coherence-square-maps g' f' k' h')
  (back-left : coherence-square-maps f' hA hB f)
  (back-right : coherence-square-maps g' hA hC g)
  (front-left : coherence-square-maps h' hB hD h)
  (front-right : coherence-square-maps k' hC hD k)
  (bottom : coherence-square-maps g f k h)
  where

  coherence-htpy-parallel-cone-coherence-cube-maps :
    ( c :
      coherence-cube-maps
        f g h k f' g' h' k' hA hB hC hD
        top back-left back-right front-left front-right bottom) →
    coherence-htpy-parallel-cone
      ( front-left)
      ( refl-htpy' k)
      ( ( f') ,
        ( g ∘ hA) ,
        ( rectangle-back-left-bottom-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))
      ( ( f') ,
        ( hC ∘ g') ,
        ( rectangle-top-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))
      ( refl-htpy' f')
      ( back-right)
  coherence-htpy-parallel-cone-coherence-cube-maps = {!!}
```

### Any commuting cube of maps induces a commuting cube of function spaces

```agda
module _
  { l1 l2 l3 l4 l1' l2' l3' l4' l5 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  ( f : A → B) (g : A → C) (h : B → D) (k : C → D)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  ( f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  ( hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  ( top : coherence-square-maps g' f' k' h')
  ( back-left : coherence-square-maps f' hA hB f)
  ( back-right : coherence-square-maps g' hA hC g)
  ( front-left : coherence-square-maps h' hB hD h)
  ( front-right : coherence-square-maps k' hC hD k)
  ( bottom : coherence-square-maps g f k h)
  where

  precomp-coherence-cube-maps :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom) →
    ( W : UU l5) →
    coherence-cube-maps
      ( precomp h' W)
      ( precomp k' W)
      ( precomp f' W)
      ( precomp g' W)
      ( precomp h W)
      ( precomp k W)
      ( precomp f W)
      ( precomp g W)
      ( precomp hD W)
      ( precomp hB W)
      ( precomp hC W)
      ( precomp hA W)
      ( precomp-coherence-square-maps g f k h bottom W)
      ( precomp-coherence-square-maps hB h' h hD (inv-htpy front-left) W)
      ( precomp-coherence-square-maps hC k' k hD (inv-htpy front-right) W)
      ( precomp-coherence-square-maps hA f' f hB (inv-htpy back-left) W)
      ( precomp-coherence-square-maps hA g' g hC (inv-htpy back-right) W)
      ( precomp-coherence-square-maps g' f' k' h' top W)
  precomp-coherence-cube-maps = {!!}
```
