# Type arithmetic with the unit type

```agda
module foundation.type-arithmetic-unit-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove arithmetical laws involving the unit type

## Laws

### Left unit law for dependent pair types

```agda
module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Σ : Σ unit A → A star
  map-left-unit-law-Σ = {!!}

  map-inv-left-unit-law-Σ : A star → Σ unit A
  map-inv-left-unit-law-Σ = {!!}

  is-section-map-inv-left-unit-law-Σ :
    ( map-left-unit-law-Σ ∘ map-inv-left-unit-law-Σ) ~ id
  is-section-map-inv-left-unit-law-Σ = {!!}

  is-retraction-map-inv-left-unit-law-Σ :
    ( map-inv-left-unit-law-Σ ∘ map-left-unit-law-Σ) ~ id
  is-retraction-map-inv-left-unit-law-Σ = {!!}

  is-equiv-map-left-unit-law-Σ : is-equiv map-left-unit-law-Σ
  is-equiv-map-left-unit-law-Σ = {!!}

  left-unit-law-Σ : Σ unit A ≃ A star
  left-unit-law-Σ = {!!}

  is-equiv-map-inv-left-unit-law-Σ : is-equiv map-inv-left-unit-law-Σ
  is-equiv-map-inv-left-unit-law-Σ = {!!}

  inv-left-unit-law-Σ : A star ≃ Σ unit A
  inv-left-unit-law-Σ = {!!}
```

### Left unit law for cartesian products

```agda
module _
  {l : Level} {A : UU l}
  where

  map-left-unit-law-prod : unit × A → A
  map-left-unit-law-prod = {!!}

  map-inv-left-unit-law-prod : A → unit × A
  map-inv-left-unit-law-prod = {!!}

  is-section-map-inv-left-unit-law-prod :
    ( map-left-unit-law-prod ∘ map-inv-left-unit-law-prod) ~ id
  is-section-map-inv-left-unit-law-prod = {!!}

  is-retraction-map-inv-left-unit-law-prod :
    ( map-inv-left-unit-law-prod ∘ map-left-unit-law-prod) ~ id
  is-retraction-map-inv-left-unit-law-prod = {!!}

  is-equiv-map-left-unit-law-prod : is-equiv map-left-unit-law-prod
  is-equiv-map-left-unit-law-prod = {!!}

  left-unit-law-prod : (unit × A) ≃ A
  left-unit-law-prod = {!!}

  is-equiv-map-inv-left-unit-law-prod : is-equiv map-inv-left-unit-law-prod
  is-equiv-map-inv-left-unit-law-prod = {!!}

  inv-left-unit-law-prod : A ≃ (unit × A)
  inv-left-unit-law-prod = {!!}
```

### Right unit law for cartesian products

```agda
  map-right-unit-law-prod : A × unit → A
  map-right-unit-law-prod = {!!}

  map-inv-right-unit-law-prod : A → A × unit
  map-inv-right-unit-law-prod = {!!}

  is-section-map-inv-right-unit-law-prod :
    (map-right-unit-law-prod ∘ map-inv-right-unit-law-prod) ~ id
  is-section-map-inv-right-unit-law-prod = {!!}

  is-retraction-map-inv-right-unit-law-prod :
    (map-inv-right-unit-law-prod ∘ map-right-unit-law-prod) ~ id
  is-retraction-map-inv-right-unit-law-prod = {!!}

  is-equiv-map-right-unit-law-prod : is-equiv map-right-unit-law-prod
  is-equiv-map-right-unit-law-prod = {!!}

  right-unit-law-prod : (A × unit) ≃ A
  right-unit-law-prod = {!!}
```

### Left unit law for dependent function types

```agda
module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Π : ((t : unit) → A t) → A star
  map-left-unit-law-Π = {!!}

  map-inv-left-unit-law-Π : A star → ((t : unit) → A t)
  map-inv-left-unit-law-Π = {!!}

  is-section-map-inv-left-unit-law-Π :
    ( map-left-unit-law-Π ∘ map-inv-left-unit-law-Π) ~ id
  is-section-map-inv-left-unit-law-Π = {!!}

  is-retraction-map-inv-left-unit-law-Π :
    ( map-inv-left-unit-law-Π ∘ map-left-unit-law-Π) ~ id
  is-retraction-map-inv-left-unit-law-Π = {!!}

  is-equiv-map-left-unit-law-Π : is-equiv map-left-unit-law-Π
  is-equiv-map-left-unit-law-Π = {!!}

  left-unit-law-Π : ((t : unit) → A t) ≃ A star
  left-unit-law-Π = {!!}

  is-equiv-map-inv-left-unit-law-Π : is-equiv map-inv-left-unit-law-Π
  is-equiv-map-inv-left-unit-law-Π = {!!}

  inv-left-unit-law-Π : A star ≃ ((t : unit) → A t)
  inv-left-unit-law-Π = {!!}
```

### Left unit law for non-dependent function types

```agda
module _
  {l : Level} (A : UU l)
  where

  map-left-unit-law-function-type : (unit → A) → A
  map-left-unit-law-function-type = {!!}

  map-inv-left-unit-law-function-type : A → (unit → A)
  map-inv-left-unit-law-function-type = {!!}

  is-equiv-map-left-unit-law-function-type :
    is-equiv map-left-unit-law-function-type
  is-equiv-map-left-unit-law-function-type = {!!}

  is-equiv-map-inv-left-unit-law-function-type :
    is-equiv map-inv-left-unit-law-function-type
  is-equiv-map-inv-left-unit-law-function-type = {!!}

  left-unit-law-function-type : (unit → A) ≃ A
  left-unit-law-function-type = {!!}

  inv-left-unit-law-function-type : A ≃ (unit → A)
  inv-left-unit-law-function-type = {!!}
```

## See also

- That `unit` is the terminal type is a corollary of `is-contr-Π`, which may be
  found in
  [`foundation-core.contractible-types`](foundation-core.contractible-types.md).
  This can be considered a _right zero law for function types_
  (`(A → unit) ≃ unit`).
