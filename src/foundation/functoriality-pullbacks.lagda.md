# Functorialty of pullbacks

```agda
module foundation.functoriality-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.morphisms-cospans
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Idea

The construction of the [standard pullback](foundation-core.pullbacks.md) is
functorial.

## Definitions

### The functorial action on maps of pullbacks

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  where

  map-standard-pullback :
    hom-cospan f' g' f g → standard-pullback f' g' → standard-pullback f g
  map-standard-pullback = {!!}

  map-is-pullback :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone f g C) (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    hom-cospan f' g' f g → C' → C
  map-is-pullback = {!!}
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
