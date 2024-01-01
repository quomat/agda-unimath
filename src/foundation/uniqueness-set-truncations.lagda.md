# Uniqueness of set truncations

```agda
module foundation.uniqueness-set-truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.mere-equality
open import foundation.sets
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-truncation
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

The universal property of set truncation implies that set truncations are
uniquely unique.

## Properties

### A 3-for-2 property for set truncations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C) {h : hom-Set B C}
  (H : (h ∘ f) ~ g)
  where

  abstract
    is-equiv-is-set-truncation-is-set-truncation :
      is-set-truncation B f → is-set-truncation C g → is-equiv h
    is-equiv-is-set-truncation-is-set-truncation = {!!}

  abstract
    is-set-truncation-is-equiv-is-set-truncation :
      is-set-truncation C g → is-equiv h → is-set-truncation B f
    is-set-truncation-is-equiv-is-set-truncation = {!!}

  abstract
    is-set-truncation-is-set-truncation-is-equiv :
      is-equiv h → is-set-truncation B f → is-set-truncation C g
    is-set-truncation-is-set-truncation-is-equiv = {!!}
```

### The uniquely uniqueness of set truncations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C)
  (Sf : is-set-truncation B f)
  (Sg : is-set-truncation C g)
  where

  abstract
    uniqueness-set-truncation :
      is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ f) ~ g))
    uniqueness-set-truncation = {!!}

  equiv-uniqueness-set-truncation : type-Set B ≃ type-Set C
  equiv-uniqueness-set-truncation = {!!}

  map-equiv-uniqueness-set-truncation : type-Set B → type-Set C
  map-equiv-uniqueness-set-truncation = {!!}

  triangle-uniqueness-set-truncation :
    (map-equiv-uniqueness-set-truncation ∘ f) ~ g
  triangle-uniqueness-set-truncation = {!!}
```
