# Truncation images of maps

```agda
module foundation.truncation-images-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.truncated-maps
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.truncation-levels
```

</details>

## Idea

The **`k`-truncation image** of a map `f : A → B` is the type `trunc-im k f`
that fits in the (`k`-connected,`k`-truncated) factorization of `f`. It is
defined as the type

```text
  trunc-im k f := {!!}
```

## Definition

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  trunc-im : UU (l1 ⊔ l2)
  trunc-im = {!!}

  unit-trunc-im : A → trunc-im
  pr1 (unit-trunc-im x) = {!!}

  projection-trunc-im : trunc-im → B
  projection-trunc-im = {!!}
```

## Properties

### Characterization of the identity types of `k+1`-truncation images

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  Eq-unit-trunc-im : A → A → UU (l1 ⊔ l2)
  Eq-unit-trunc-im x y = {!!}

  extensionality-trunc-im :
    (x y : A) →
    ( unit-trunc-im (succ-𝕋 k) f x ＝ unit-trunc-im (succ-𝕋 k) f y) ≃
    ( Eq-unit-trunc-im x y)
  extensionality-trunc-im = {!!}
```

### The map projection-trunc-im k is k-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-trunc-map-projection-trunc-im : is-trunc-map k (projection-trunc-im k f)
  is-trunc-map-projection-trunc-im = {!!}
```

### The map unit-trunc-im k is k-connected

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-unit-trunc-im : is-connected-map k (unit-trunc-im k f)
  is-connected-map-unit-trunc-im = {!!}
```
