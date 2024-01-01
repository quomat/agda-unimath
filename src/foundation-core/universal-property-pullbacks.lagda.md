# The universal property of pullbacks

```agda
module foundation-core.universal-property-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.postcomposition-functions
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Definition

### The universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  universal-property-pullback : UUω
  universal-property-pullback = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  map-universal-property-pullback :
    universal-property-pullback f g c →
    {C' : UU l5} (c' : cone f g C') → C' → C
  map-universal-property-pullback = {!!}

  compute-map-universal-property-pullback :
    (up-c : universal-property-pullback f g c) →
    {C' : UU l5} (c' : cone f g C') →
    cone-map f g c (map-universal-property-pullback up-c c') ＝ c'
  compute-map-universal-property-pullback = {!!}
```

## Properties

### 3-for-2 property of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  {f : A → X} {g : B → X} (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c')
  where

  inv-triangle-cone-cone :
    {l6 : Level} (D : UU l6) →
    cone-map f g c ∘ postcomp D h ~ cone-map f g c'
  inv-triangle-cone-cone = {!!}

  triangle-cone-cone :
    {l6 : Level} (D : UU l6) →
    cone-map f g c' ~ cone-map f g c ∘ postcomp D h
  triangle-cone-cone = {!!}

  abstract
    is-equiv-up-pullback-up-pullback :
      universal-property-pullback f g c →
      universal-property-pullback f g c' →
      is-equiv h
    is-equiv-up-pullback-up-pullback = {!!}

  abstract
    up-pullback-up-pullback-is-equiv :
      is-equiv h →
      universal-property-pullback f g c →
      universal-property-pullback f g c'
    up-pullback-up-pullback-is-equiv = {!!}

  abstract
    up-pullback-is-equiv-up-pullback :
      universal-property-pullback f g c' →
      is-equiv h →
      universal-property-pullback f g c
    up-pullback-is-equiv-up-pullback = {!!}
```

### Uniqueness of maps obtained via the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  abstract
    uniqueness-universal-property-pullback :
      universal-property-pullback f g c →
      {l5 : Level} (C' : UU l5) (c' : cone f g C') →
      is-contr (Σ (C' → C) (λ h → htpy-cone f g (cone-map f g c h) c'))
    uniqueness-universal-property-pullback = {!!}
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
