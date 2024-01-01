# Functoriality of sequential limits

```agda
module foundation.functoriality-sequential-limits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cones-over-towers
open import foundation.dependent-pair-types
open import foundation.morphisms-towers
open import foundation.sequential-limits
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

The construction of the [sequential limit](foundation.sequential-limits.md) is
functorial.

## Definitions

### The functorial action on maps of standard sequential limits

```agda
module _
  {l1 l2 : Level} {A : tower l1} {A' : tower l2}
  where

  map-hom-standard-sequential-limit :
    hom-tower A' A → standard-sequential-limit A' → standard-sequential-limit A
  pr1 (map-hom-standard-sequential-limit (f , F) (x , H)) n = {!!}

  map-hom-is-sequential-limit :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone-tower A C) (c' : cone-tower A' C') →
    is-sequential-limit A c → is-sequential-limit A' c' →
    hom-tower A' A → C' → C
  map-hom-is-sequential-limit c c' is-lim-c is-lim-c' h x = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
