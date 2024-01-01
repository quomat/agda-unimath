# Cones over towers

```agda
module foundation.cones-over-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **cone over a [tower](foundation.towers.md) `A` with domain `X`** is a
[sequence](foundation.dependent-sequences.md) of functions from `X` into the
sequence of types of `A` such that the triangles

```text
     X
    / \
   /   \
  v     v
 Aₙ₊₁ -> Aₙ
```

[commute](foundation-core.commuting-triangles-of-maps.md) for all `n : ℕ`.

## Definitions

### Cones over towers

```agda
module _
  {l1 : Level} (A : tower l1)
  where

  cone-tower : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  cone-tower = {!!}

  map-cone-tower :
    {l2 : Level} {X : UU l2} → cone-tower X → (n : ℕ) → X → type-tower A n
  map-cone-tower = {!!}

  coherence-cone-tower :
    {l2 : Level} {X : UU l2} (c : cone-tower X) (n : ℕ) →
    coherence-triangle-maps
      ( map-cone-tower c n)
      ( map-tower A n)
      ( map-cone-tower c (succ-ℕ n))
  coherence-cone-tower = {!!}
```

### Identifications of cones over towers of types

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  coherence-htpy-cone-tower :
    (c c' : cone-tower A X) →
    ((n : ℕ) → map-cone-tower A c n ~ map-cone-tower A c' n) → UU (l1 ⊔ l2)
  coherence-htpy-cone-tower = {!!}

  htpy-cone-tower : cone-tower A X → cone-tower A X → UU (l1 ⊔ l2)
  htpy-cone-tower = {!!}

  refl-htpy-cone-tower : (c : cone-tower A X) → htpy-cone-tower c c
  refl-htpy-cone-tower = {!!}

  htpy-eq-cone-tower : (c c' : cone-tower A X) → c ＝ c' → htpy-cone-tower c c'
  htpy-eq-cone-tower = {!!}

  is-torsorial-htpy-cone-tower :
    (c : cone-tower A X) → is-torsorial (htpy-cone-tower c)
  is-torsorial-htpy-cone-tower = {!!}

  is-equiv-htpy-eq-cone-tower :
    (c c' : cone-tower A X) → is-equiv (htpy-eq-cone-tower c c')
  is-equiv-htpy-eq-cone-tower = {!!}

  extensionality-cone-tower :
    (c c' : cone-tower A X) → (c ＝ c') ≃ htpy-cone-tower c c'
  extensionality-cone-tower = {!!}

  eq-htpy-cone-tower : (c c' : cone-tower A X) → htpy-cone-tower c c' → c ＝ c'
  eq-htpy-cone-tower = {!!}
```

### Precomposing cones over towers with a map

```agda
module _
  {l1 l2 l3 : Level} (A : tower l1) {X : UU l2} {Y : UU l3}
  where

  cone-map-tower : cone-tower A X → (Y → X) → cone-tower A Y
  cone-map-tower = {!!}
```

### Postcomposition cones over postcomposition towers

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (A : tower l2) {Y : UU l3} (c : cone-tower A Y)
  where

  cone-postcomp-tower :
    cone-tower (postcomp-tower X A) (X → Y)
  cone-postcomp-tower = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
