# Decidable maps

```agda
module foundation.decidable-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Definition

A map is said to be decidable if its fibers are decidable types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map = {!!}
```

```agda
is-decidable-map-retraction :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → has-decidable-equality B →
  (i : A → B) → retraction i → is-decidable-map i
is-decidable-map-retraction = {!!}
```

## Properties

### The map on total spaces induced by a family of decidable embeddings is a decidable embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-decidable-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-decidable-map (f x)) → is-decidable-map (tot f)
  is-decidable-map-tot = {!!}
```
