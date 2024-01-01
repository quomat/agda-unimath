# Pointed cartesian product types

```agda
module structured-types.pointed-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Given two pointed types `a : A` and `b : B`, their cartesian product is again
canonically pointed at `(a , b) : A × B`. We call this the **pointed cartesian
product** or **pointed product** of the two pointed types.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  prod-Pointed-Type :
    (A : Pointed-Type l1) (B : Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
  prod-Pointed-Type = {!!}

  infixr 15 _×∗_
  _×∗_ = {!!}
```

## Properties

### The pointed projections from the pointed product `A ×∗ B` onto `A` and `B`

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-pr1-prod-Pointed-Type : type-Pointed-Type (A ×∗ B) → type-Pointed-Type A
  map-pr1-prod-Pointed-Type = {!!}

  pr1-prod-Pointed-Type : (A ×∗ B) →∗ A
  pr1-prod-Pointed-Type = {!!}

  map-pr2-prod-Pointed-Type : type-Pointed-Type (A ×∗ B) → type-Pointed-Type B
  map-pr2-prod-Pointed-Type = {!!}

  pr2-prod-Pointed-Type : (A ×∗ B) →∗ B
  pr2-prod-Pointed-Type = {!!}
```

### The pointed product `A ×∗ B` comes equipped with pointed inclusion of `A` and `B`

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-inl-prod-Pointed-Type : type-Pointed-Type A → type-Pointed-Type (A ×∗ B)
  map-inl-prod-Pointed-Type = {!!}

  inl-prod-Pointed-Type : A →∗ (A ×∗ B)
  inl-prod-Pointed-Type = {!!}

  map-inr-prod-Pointed-Type : type-Pointed-Type B → type-Pointed-Type (A ×∗ B)
  map-inr-prod-Pointed-Type = {!!}

  inr-prod-Pointed-Type : B →∗ (A ×∗ B)
  inr-prod-Pointed-Type = {!!}
```

### The pointed inclusions into `A ×∗ B` are sections to the pointed projections

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  is-section-map-inl-prod-Pointed-Type :
    (map-pr1-prod-Pointed-Type A B ∘ map-inl-prod-Pointed-Type A B) ~ id
  is-section-map-inl-prod-Pointed-Type = {!!}

  is-section-map-inr-prod-Pointed-Type :
    (map-pr2-prod-Pointed-Type A B ∘ map-inr-prod-Pointed-Type A B) ~ id
  is-section-map-inr-prod-Pointed-Type = {!!}
```

### The pointed gap map for the pointed product

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-gap-prod-Pointed-Type :
    {l3 : Level} {S : Pointed-Type l3}
    (f : S →∗ A) (g : S →∗ B) →
    type-Pointed-Type S → type-Pointed-Type (A ×∗ B)
  map-gap-prod-Pointed-Type = {!!}

  gap-prod-Pointed-Type :
    {l3 : Level} {S : Pointed-Type l3}
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ×∗ B)
  gap-prod-Pointed-Type = {!!}
```
