# The universal property of truncations

```agda
module foundation-core.universal-property-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.sections
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

We say that a map `f : A → B` into a `k`-truncated type `B` is a
**`k`-truncation** of `A` -- or that it **satisfies the universal property of
the `k`-truncation** of `A` -- if any map `g : A → C` into a `k`-truncated type
`C` extends uniquely along `f` to a map `B → C`.

## Definition

### The condition on a map to be a truncation

```agda
precomp-Trunc :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  (C : Truncated-Type l3 k) →
  (B → type-Truncated-Type C) → (A → type-Truncated-Type C)
precomp-Trunc f C = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B)
  where

  is-truncation : UUω
  is-truncation = {!!}

  equiv-is-truncation :
    {l3 : Level} (H : is-truncation) (C : Truncated-Type l3 k) →
    ( type-Truncated-Type B → type-Truncated-Type C) ≃
    ( A → type-Truncated-Type C)
  pr1 (equiv-is-truncation H C) = {!!}
```

### The universal property of truncations

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B)
  where

  universal-property-truncation : UUω
  universal-property-truncation = {!!}
```

### The dependent universal property of truncations

```agda
precomp-Π-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  (C : B → Truncated-Type l3 k) →
  ((b : B) → type-Truncated-Type (C b)) →
  ((a : A) → type-Truncated-Type (C (f a)))
precomp-Π-Truncated-Type f C h a = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B)
  where

  dependent-universal-property-truncation : UUω
  dependent-universal-property-truncation = {!!}
```

## Properties

### Equivalences into `k`-truncated types are truncations

```agda
abstract
  is-truncation-id :
    {l1 : Level} {k : 𝕋} {A : UU l1} (H : is-trunc k A) →
    is-truncation (A , H) id
  is-truncation-id H B = {!!}

abstract
  is-truncation-equiv :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
    (e : A ≃ type-Truncated-Type B) →
    is-truncation B (map-equiv e)
  is-truncation-equiv B e C = {!!}
```

### A map into a truncated type is a truncation if and only if it satisfies the universal property of the truncation

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B)
  where

  abstract
    is-truncation-universal-property-truncation :
      universal-property-truncation B f → is-truncation B f
    is-truncation-universal-property-truncation H C = {!!}

  abstract
    universal-property-truncation-is-truncation :
      is-truncation B f → universal-property-truncation B f
    universal-property-truncation-is-truncation H C g = {!!}

  map-is-truncation :
    is-truncation B f →
    {l : Level} (C : Truncated-Type l k) (g : A → type-Truncated-Type C) →
    type-hom-Truncated-Type k B C
  map-is-truncation H C g = {!!}

  triangle-is-truncation :
    (H : is-truncation B f) →
    {l : Level} (C : Truncated-Type l k) (g : A → type-Truncated-Type C) →
    map-is-truncation H C g ∘ f ~ g
  triangle-is-truncation H C g = {!!}
```

### A map into a truncated type is a truncation if and only if it satisfies the dependent universal property of the truncation

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B)
  where

  abstract
    dependent-universal-property-truncation-is-truncation :
      is-truncation B f →
      dependent-universal-property-truncation B f
    dependent-universal-property-truncation-is-truncation H X = {!!}

  abstract
    is-truncation-dependent-universal-property-truncation :
      dependent-universal-property-truncation B f → is-truncation B f
    is-truncation-dependent-universal-property-truncation H X = {!!}

  section-is-truncation :
    is-truncation B f →
    {l3 : Level} (C : Truncated-Type l3 k)
    (h : A → type-Truncated-Type C) (g : type-hom-Truncated-Type k C B) →
    f ~ g ∘ h → section g
  section-is-truncation H C h g K = {!!}
```
