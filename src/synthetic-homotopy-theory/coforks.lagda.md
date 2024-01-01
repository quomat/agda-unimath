# Coforks

```agda
module synthetic-homotopy-theory.coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.codiagonal-maps-of-types
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

A **cofork** of a parallel pair `f, g : A → B` with vertext `X` is a map
`e : B → X` together with a [homotopy](foundation.homotopies.md)
`H : e ∘ f ~ e ∘ g`. The name comes from the diagram

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

which looks like a fork if you flip the arrows, hence a cofork.

Coforks are an analogue of
[cocones under spans](synthetic-homotopy-theory.cocones-under-spans.md) for
parallel pairs. The universal cofork of a pair is their
[coequalizer](synthetic-homotopy-theory.coequalizers.md).

## Definitions

### Coforks

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  cofork : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  cofork = {!!}

  module _
    { X : UU l3} (e : cofork X)
    where

    map-cofork : B → X
    map-cofork = {!!}

    coherence-cofork : map-cofork ∘ f ~ map-cofork ∘ g
    coherence-cofork = {!!}
```

### Homotopies of coforks

A homotopy between coforks with the same vertex is given by a homotopy between
the two maps, together with a coherence datum asserting that we may apply the
given homotopy and the appropriate cofork homotopy in either order.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  where

  coherence-htpy-cofork :
    ( e e' : cofork f g X) →
    ( K : map-cofork f g e ~ map-cofork f g e') →
    UU (l1 ⊔ l3)
  coherence-htpy-cofork = {!!}

  htpy-cofork : cofork f g X → cofork f g X → UU (l1 ⊔ l2 ⊔ l3)
  htpy-cofork = {!!}
```

### Postcomposing coforks

Given a cofork `e : B → X` and a map `h : X → Y`, we may compose the two to get
a new cofork `h ∘ e`.

```text
     g
   ----->     e        h
 A -----> B -----> X -----> Y
     f
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} (e : cofork f g X)
  where

  cofork-map : {l : Level} {Y : UU l} → (X → Y) → cofork f g Y
  cofork-map = {!!}
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  where

  reflexive-htpy-cofork : (e : cofork f g X) → htpy-cofork f g e e
  reflexive-htpy-cofork = {!!}

  htpy-cofork-eq :
    ( e e' : cofork f g X) → (e ＝ e') → htpy-cofork f g e e'
  htpy-cofork-eq = {!!}

  abstract
    is-torsorial-htpy-cofork :
      ( e : cofork f g X) → is-torsorial (htpy-cofork f g e)
    is-torsorial-htpy-cofork = {!!}

    is-equiv-htpy-cofork-eq :
      ( e e' : cofork f g X) → is-equiv (htpy-cofork-eq e e')
    is-equiv-htpy-cofork-eq = {!!}

  eq-htpy-cofork :
    ( e e' : cofork f g X) → htpy-cofork f g e e' → e ＝ e'
  eq-htpy-cofork = {!!}
```

### Postcomposing a cofork by identity is the identity

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  cofork-map-id : cofork-map f g e id ＝ e
  cofork-map-id = {!!}
```

### Postcomposing coforks distributes over function composition

```text
     g
   ----->     e        h        k
 A -----> B -----> X -----> Y -----> Z
     f
```

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} {Y : UU l4} {Z : UU l5}
  ( e : cofork f g X)
  where

  cofork-map-comp :
    (h : X → Y) (k : Y → Z) →
    cofork-map f g e (k ∘ h) ＝ cofork-map f g (cofork-map f g e h) k
  cofork-map-comp = {!!}
```

### Coforks are special cases of cocones under spans

The type of coforks of parallel pairs is equivalent to the type of
[cocones](synthetic-homotopy-theory.cocones-under-spans.md) under the span

```text
     ∇         [f,g]
A <----- A + A -----> B.
```

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  vertical-map-span-cocone-cofork : A + A → A
  vertical-map-span-cocone-cofork = {!!}

  horizontal-map-span-cocone-cofork : A + A → B
  horizontal-map-span-cocone-cofork = {!!}

  module _
    { l3 : Level} {X : UU l3}
    where

    cofork-cocone-codiagonal :
      cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( X) →
      cofork f g X
    cofork-cocone-codiagonal = {!!}

    horizontal-map-cocone-cofork : cofork f g X → A → X
    horizontal-map-cocone-cofork = {!!}

    vertical-map-cocone-cofork : cofork f g X → B → X
    vertical-map-cocone-cofork = {!!}

    coherence-square-cocone-cofork :
      ( e : cofork f g X) →
      coherence-square-maps
        ( horizontal-map-span-cocone-cofork)
        ( vertical-map-span-cocone-cofork)
        ( vertical-map-cocone-cofork e)
        ( horizontal-map-cocone-cofork e)
    coherence-square-cocone-cofork = {!!}

    cocone-codiagonal-cofork :
      cofork f g X →
      cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( X)
    cocone-codiagonal-cofork = {!!}

    abstract
      is-section-cocone-codiagonal-cofork :
        cofork-cocone-codiagonal ∘ cocone-codiagonal-cofork ~ id
      is-section-cocone-codiagonal-cofork = {!!}

      is-retraction-cocone-codiagonal-fork :
        cocone-codiagonal-cofork ∘ cofork-cocone-codiagonal ~ id
      is-retraction-cocone-codiagonal-fork = {!!}

    is-equiv-cofork-cocone-codiagonal :
      is-equiv cofork-cocone-codiagonal
    is-equiv-cofork-cocone-codiagonal = {!!}

    equiv-cocone-codiagonal-cofork :
      cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( X) ≃
      cofork f g X
    equiv-cocone-codiagonal-cofork = {!!}

  triangle-cofork-cocone :
    { l3 l4 : Level} {X : UU l3} {Y : UU l4} →
    ( e : cofork f g X) →
    coherence-triangle-maps
      ( cofork-map f g e {Y = Y})
      ( cofork-cocone-codiagonal)
      ( cocone-map
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( cocone-codiagonal-cofork e))
  triangle-cofork-cocone = {!!}
```
