# Transfinite cocomposition of maps

```agda
module foundation.transfinite-cocomposition-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.sequential-limits
open import foundation.towers
open import foundation.universe-levels
```

</details>

## Idea

Given a [tower](foundation.towers.md) of maps, i.e. a certain infinite
[sequence](foundation.dependent-sequences.md) of maps `fₙ`:

```text
      ⋯        fₙ      ⋯      f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₁ ---> A₀,
```

we can form the **transfinite cocomposition** of `f` by taking the canonical map
from the [standard sequential limit](foundation.sequential-limits.md) `limₙ Aₙ`
into `A₀`.

## Definitions

### The transfinite cocomposition of a tower of maps

```agda
module _
  {l : Level} (f : tower l)
  where

  transfinite-cocomp : standard-sequential-limit f → type-tower f 0
  transfinite-cocomp = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
