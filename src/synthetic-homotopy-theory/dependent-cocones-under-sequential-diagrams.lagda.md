# Dependent cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.constant-type-families
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) `c`
with vertex `X` under it, and a type family `P : X → 𝓤`, we may construct
_dependent_ cocones on `P` over `c`.

A **dependent cocone under a
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)** on `P`
over `c ≐ (X, i, H)` consists of a [sequence](foundation.dependent-sequences.md)
of dependent maps `i'ₙ : (x : Aₙ) → P (iₙ x)` and a sequence of
[dependent homotopies](foundation.dependent-homotopies.md)
`H'ₙ : i'ₙ ~ i'ₙ₊₁ ∘ aₙ` over `H`.

## Definitions

### Dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) (P : X → UU l3)
  where

  dependent-cocone-sequential-diagram : UU (l1 ⊔ l3)
  dependent-cocone-sequential-diagram = {!!}
```

### Components of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  ( d : dependent-cocone-sequential-diagram A c P)
  where

  map-dependent-cocone-sequential-diagram :
    ( n : ℕ) (a : family-sequential-diagram A n) →
    P (map-cocone-sequential-diagram A c n a)
  map-dependent-cocone-sequential-diagram = {!!}

  coherence-triangle-dependent-cocone-sequential-diagram :
    ( n : ℕ) → (a : family-sequential-diagram A n) →
    dependent-identification P
      ( coherence-triangle-cocone-sequential-diagram A c n a)
      ( map-dependent-cocone-sequential-diagram n a)
      ( map-dependent-cocone-sequential-diagram
        ( succ-ℕ n)
        ( map-sequential-diagram A n a))
  coherence-triangle-dependent-cocone-sequential-diagram = {!!}
```

### Homotopies of dependent cocones under sequential diagrams

A **homotopy** of dependent cocones `(P, i', H')` and `(P, j', L')` consists of
a sequence of [homotopies](foundation.homotopies.md) `Kₙ : i'ₙ ~ j'ₙ` and a
coherence datum.

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  where

  coherence-htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    ( K :
      ( n : ℕ) →
      ( map-dependent-cocone-sequential-diagram A P d n) ~
      ( map-dependent-cocone-sequential-diagram A P d' n)) →
    UU (l1 ⊔ l3)
  coherence-htpy-dependent-cocone-sequential-diagram = {!!}

  htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    UU (l1 ⊔ l3)
  htpy-dependent-cocone-sequential-diagram = {!!}
```

### Components of homotopies of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  ( d d' : dependent-cocone-sequential-diagram A c P)
  ( H : htpy-dependent-cocone-sequential-diagram A P d d')
  where

  htpy-htpy-dependent-cocone-sequential-diagram :
    ( n : ℕ) →
    ( map-dependent-cocone-sequential-diagram A P d n) ~
    ( map-dependent-cocone-sequential-diagram A P d' n)
  htpy-htpy-dependent-cocone-sequential-diagram = {!!}

  coherence-htpy-htpy-dependent-cocone-sequential-diagram :
    coherence-htpy-dependent-cocone-sequential-diagram A P d d'
      ( htpy-htpy-dependent-cocone-sequential-diagram)
  coherence-htpy-htpy-dependent-cocone-sequential-diagram = {!!}
```

### Obtaining dependent cocones under sequential diagrams by postcomposing cocones under sequential diagrams with dependent maps

Given a cocone `c` with vertex `X`, and a dependent map `h : (x : X) → P x`, we
may extend `c` to a dependent cocone on `P` over `c`.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-cocone-map-sequential-diagram :
    { l : Level} (P : X → UU l) →
    ( (x : X) → P x) → dependent-cocone-sequential-diagram A c P
  dependent-cocone-map-sequential-diagram = {!!}
  pr2 (dependent-cocone-map-sequential-diagram P h) n = {!!}
```

## Properties

### Characterization of identity types of dependent cocones under sequential diagrams

[Equality](foundation.identity-types.md) of dependent cocones is captured by a
homotopy between them.

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  where

  reflexive-htpy-dependent-cocone-sequential-diagram :
    ( d : dependent-cocone-sequential-diagram A c P) →
    htpy-dependent-cocone-sequential-diagram A P d d
  reflexive-htpy-dependent-cocone-sequential-diagram = {!!}

  htpy-eq-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    ( d ＝ d') → htpy-dependent-cocone-sequential-diagram A P d d'
  htpy-eq-dependent-cocone-sequential-diagram = {!!}

  abstract
    is-torsorial-htpy-dependent-cocone-sequential-diagram :
      ( d : dependent-cocone-sequential-diagram A c P) →
      is-torsorial (htpy-dependent-cocone-sequential-diagram A P d)
    is-torsorial-htpy-dependent-cocone-sequential-diagram = {!!}

    is-equiv-htpy-eq-dependent-cocone-sequential-diagram :
      ( d d' : dependent-cocone-sequential-diagram A c P) →
      is-equiv (htpy-eq-dependent-cocone-sequential-diagram d d')
    is-equiv-htpy-eq-dependent-cocone-sequential-diagram = {!!}

  extensionality-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    ( d ＝ d') ≃ htpy-dependent-cocone-sequential-diagram A P d d'
  extensionality-dependent-cocone-sequential-diagram = {!!}
  pr2 (extensionality-dependent-cocone-sequential-diagram d d') = {!!}

  eq-htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    htpy-dependent-cocone-sequential-diagram A P d d' → (d ＝ d')
  eq-htpy-dependent-cocone-sequential-diagram = {!!}
```

### Dependent cocones under sequential diagrams on fiberwise constant type families are equivalent to regular cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) (Y : UU l3)
  where

  compute-dependent-cocone-sequential-diagram-constant-family :
    ( dependent-cocone-sequential-diagram A c (λ _ → Y)) ≃
    ( cocone-sequential-diagram A Y)
  compute-dependent-cocone-sequential-diagram-constant-family = {!!}

  map-compute-dependent-cocone-sequential-diagram-constant-family :
    dependent-cocone-sequential-diagram A c (λ _ → Y) →
    cocone-sequential-diagram A Y
  map-compute-dependent-cocone-sequential-diagram-constant-family = {!!}

  triangle-compute-dependent-cocone-sequential-diagram-constant-family :
    coherence-triangle-maps
      ( cocone-map-sequential-diagram A c)
      ( map-compute-dependent-cocone-sequential-diagram-constant-family)
      ( dependent-cocone-map-sequential-diagram A c (λ _ → Y))
  triangle-compute-dependent-cocone-sequential-diagram-constant-family = {!!}
```

### Dependent cocones under sequential diagrams are special cases of dependent coforks

Just like with the regular
[cocones under sequential diagrams](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md),
we have an analogous correspondence between dependent cocones over a cocone `c`
and dependent coforks over the cofork corresponding to `c`.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  module _
    { l3 : Level} (P : X → UU l3)
    where

    dependent-cocone-sequential-diagram-dependent-cofork :
      dependent-cofork
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( P) →
      dependent-cocone-sequential-diagram A c P
    dependent-cocone-sequential-diagram-dependent-cofork = {!!}
    pr2 (dependent-cocone-sequential-diagram-dependent-cofork e) = {!!}

    dependent-cofork-dependent-cocone-sequential-diagram :
      dependent-cocone-sequential-diagram A c P →
      dependent-cofork
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( P)
    dependent-cofork-dependent-cocone-sequential-diagram = {!!}
    pr2 (dependent-cofork-dependent-cocone-sequential-diagram d) = {!!}

    abstract
      is-section-dependent-cocone-sequential-diagram-dependent-cofork :
        ( dependent-cofork-dependent-cocone-sequential-diagram ∘
          dependent-cocone-sequential-diagram-dependent-cofork) ~
        ( id)
      is-section-dependent-cocone-sequential-diagram-dependent-cofork = {!!}

      is-retraction-dependent-cocone-sequential-diagram-dependent-cofork :
        ( dependent-cocone-sequential-diagram-dependent-cofork ∘
          dependent-cofork-dependent-cocone-sequential-diagram) ~
        ( id)
      is-retraction-dependent-cocone-sequential-diagram-dependent-cofork = {!!}

    is-equiv-dependent-cocone-sequential-diagram-dependent-cofork :
      is-equiv dependent-cocone-sequential-diagram-dependent-cofork
    is-equiv-dependent-cocone-sequential-diagram-dependent-cofork = {!!}

    equiv-dependent-cocone-sequential-diagram-dependent-cofork :
      dependent-cofork
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( P) ≃
      dependent-cocone-sequential-diagram A c P
    equiv-dependent-cocone-sequential-diagram-dependent-cofork = {!!}
    pr2 equiv-dependent-cocone-sequential-diagram-dependent-cofork = {!!}

  triangle-dependent-cocone-sequential-diagram-dependent-cofork :
    { l3 : Level} (P : X → UU l3) →
    coherence-triangle-maps
      ( dependent-cocone-map-sequential-diagram A c P)
      ( dependent-cocone-sequential-diagram-dependent-cofork P)
      ( dependent-cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
  triangle-dependent-cocone-sequential-diagram-dependent-cofork = {!!}
```
