# `0`-Images of maps

```agda
module foundation.0-images-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncation-images-of-maps
open import foundation.universe-levels

open import foundation-core.truncation-levels
```

</details>

## Idea

The 0-image of a map `f : A → B` is the type
`0-im f := {!!}
0-connected and the map `0-im f → B` is `0`-truncated.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  0-im : UU (l1 ⊔ l2)
  0-im = {!!}

  unit-0-im : A → 0-im
  unit-0-im = {!!}

  projection-0-im : 0-im → B
  projection-0-im = {!!}
```

## Properties

### Characterization of the identity type of `0-im f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  Eq-unit-0-im : A → A → UU (l1 ⊔ l2)
  Eq-unit-0-im = {!!}
```
