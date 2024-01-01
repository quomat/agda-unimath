# Sequential limits

```agda
module foundation.sequential-limits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.cones-over-towers
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universal-property-sequential-limits
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given a [tower of types](foundation.towers.md)

```text
               fₙ                     f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀
```

we can form the **standard sequential limit** `limₙ Aₙ` satisfying
[the universal property of the sequential limit](foundation.universal-property-sequential-limits.md)
of `Aₙ` thus completing the diagram

```text
                           fₙ                     f₁      f₀
  limₙ Aₙ ---> ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

The standard sequential limit consists of "points at infinity", which can be
recorded as [sequences](foundation.dependent-sequences.md) of terms whose images
under `f` agree:

```text
  ⋯  ↦   xₙ₊₁  ↦   xₙ  ↦   ⋯  ↦   x₂  ↦   x₁  ↦   x₀
          ⫙        ⫙              ⫙       ⫙       ⫙
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

## Definitions

### The standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  standard-sequential-limit : UU l
  standard-sequential-limit = {!!}

module _
  {l : Level} (A : tower l)
  where

  sequence-standard-sequential-limit :
    standard-sequential-limit A → (n : ℕ) → type-tower A n
  sequence-standard-sequential-limit = {!!}

  coherence-standard-sequential-limit :
    (x : standard-sequential-limit A) (n : ℕ) →
    sequence-standard-sequential-limit x n ＝
    map-tower A n (sequence-standard-sequential-limit x (succ-ℕ n))
  coherence-standard-sequential-limit = {!!}
```

### The cone at the standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  cone-standard-sequential-limit : cone-tower A (standard-sequential-limit A)
  pr1 cone-standard-sequential-limit n x = {!!}
```

### The gap map into the standard sequential limit

The **gap map** of a [cone over a tower](foundation.cones-over-towers.md) is the
map from the domain of the cone into the standard sequential limit.

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  gap-tower : cone-tower A X → X → standard-sequential-limit A
  pr1 (gap-tower c x) n = {!!}
```

### The property of being a sequential limit

The [proposition](foundation-core.propositions.md) `is-sequential-limit` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation.universal-property-sequential-limits.md) is
a large proposition.

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  is-sequential-limit : cone-tower A X → UU (l1 ⊔ l2)
  is-sequential-limit c = {!!}

  is-property-is-sequential-limit :
    (c : cone-tower A X) → is-prop (is-sequential-limit c)
  is-property-is-sequential-limit = {!!}

  is-sequential-limit-Prop : (c : cone-tower A X) → Prop (l1 ⊔ l2)
  pr1 (is-sequential-limit-Prop c) = {!!}
```

## Properties

### Characterization of equality in the standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  Eq-standard-sequential-limit : (s t : standard-sequential-limit A) → UU l
  Eq-standard-sequential-limit s t = {!!}

  refl-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) → Eq-standard-sequential-limit s s
  refl-Eq-standard-sequential-limit = {!!}

  Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    s ＝ t → Eq-standard-sequential-limit s t
  Eq-eq-standard-sequential-limit = {!!}

  is-torsorial-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) →
    is-torsorial (Eq-standard-sequential-limit s)
  is-torsorial-Eq-standard-sequential-limit = {!!}

  is-equiv-Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    is-equiv (Eq-eq-standard-sequential-limit s t)
  is-equiv-Eq-eq-standard-sequential-limit = {!!}

  extensionality-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    (s ＝ t) ≃ Eq-standard-sequential-limit s t
  extensionality-standard-sequential-limit = {!!}

  eq-Eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    Eq-standard-sequential-limit s t → s ＝ t
  eq-Eq-standard-sequential-limit = {!!}
```

### The standard sequential limit satisfies the universal property of a sequential limit

```agda
module _
  {l1 : Level} (A : tower l1)
  where

  cone-map-standard-sequential-limit :
    {l : Level} {Y : UU l} → (Y → standard-sequential-limit A) → cone-tower A Y
  cone-map-standard-sequential-limit = {!!}

  is-retraction-gap-tower :
    {l : Level} {Y : UU l} →
    gap-tower A ∘ cone-map-standard-sequential-limit {Y = Y} ~ id
  is-retraction-gap-tower x = {!!}

  is-section-gap-tower :
    {l : Level} {Y : UU l} →
    cone-map-standard-sequential-limit {Y = Y} ∘ gap-tower A ~ id
  is-section-gap-tower x = {!!}

  universal-property-standard-sequential-limit :
    universal-property-sequential-limit A (cone-standard-sequential-limit A)
  universal-property-standard-sequential-limit = {!!}
```

### A cone over a tower is equal to the value of `cone-map-tower` at its own gap map

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  htpy-cone-up-pullback-standard-sequential-limit :
    (c : cone-tower A X) →
    htpy-cone-tower A
      ( cone-map-tower A (cone-standard-sequential-limit A) (gap-tower A c))
      ( c)
  htpy-cone-up-pullback-standard-sequential-limit = {!!}
```

### A cone satisfies the universal property of the limit if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  is-sequential-limit-universal-property-sequential-limit :
    (c : cone-tower A X) →
    universal-property-sequential-limit A c →
    is-sequential-limit A c
  is-sequential-limit-universal-property-sequential-limit = {!!}

  universal-property-is-sequential-limit :
    (c : cone-tower A X) → is-sequential-limit A c →
    universal-property-sequential-limit A c
  universal-property-is-sequential-limit = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
