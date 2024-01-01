# Type arithmetic with the booleans

```agda
module foundation.type-arithmetic-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove arithmetical laws involving the booleans

## Laws

### Dependent pairs over booleans are equivalent to coproducts

```agda
module _
  {l : Level} (A : bool → UU l)
  where

  map-Σ-bool-coprod : Σ bool A → A true + A false
  map-Σ-bool-coprod (pair true a) = {!!}

  map-inv-Σ-bool-coprod : A true + A false → Σ bool A
  map-inv-Σ-bool-coprod (inl a) = {!!}

  is-section-map-inv-Σ-bool-coprod :
    ( map-Σ-bool-coprod ∘ map-inv-Σ-bool-coprod) ~ id
  is-section-map-inv-Σ-bool-coprod = {!!}

  is-retraction-map-inv-Σ-bool-coprod :
    ( map-inv-Σ-bool-coprod ∘ map-Σ-bool-coprod) ~ id
  is-retraction-map-inv-Σ-bool-coprod = {!!}

  is-equiv-map-Σ-bool-coprod : is-equiv map-Σ-bool-coprod
  is-equiv-map-Σ-bool-coprod = {!!}

  equiv-Σ-bool-coprod : Σ bool A ≃ (A true + A false)
  pr1 equiv-Σ-bool-coprod = {!!}

  is-equiv-map-inv-Σ-bool-coprod : is-equiv map-inv-Σ-bool-coprod
  is-equiv-map-inv-Σ-bool-coprod = {!!}

  inv-equiv-Σ-bool-coprod : (A true + A false) ≃ Σ bool A
  pr1 inv-equiv-Σ-bool-coprod = {!!}
```
