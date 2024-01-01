# The pointed unit type

```agda
module structured-types.pointed-unit-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

The pointed unit type is the initial pointed type.

## Definition

```agda
unit-Pointed-Type : Pointed-Type lzero
unit-Pointed-Type = {!!}
pr2 unit-Pointed-Type = {!!}
```

## Properties

```agda
module _
  {l : Level} (X : Pointed-Type l)
  where

  terminal-pointed-map : X →∗ unit-Pointed-Type
  terminal-pointed-map = {!!}

  map-terminal-pointed-map : type-Pointed-Type X → unit
  map-terminal-pointed-map = {!!}

  inclusion-point-Pointed-Type :
    unit-Pointed-Type →∗ X
  inclusion-point-Pointed-Type = {!!}

  is-initial-unit-Pointed-Type :
    ( f : unit-Pointed-Type →∗ X) → f ~∗ inclusion-point-Pointed-Type
  is-initial-unit-Pointed-Type = {!!}
```
