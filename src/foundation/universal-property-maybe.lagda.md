# The universal property of maybe

```agda
module foundation.universal-property-maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.maybe
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We combine the universal property of coproducts and the unit type to obtain a
universal property of the maybe modality.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2}
  where

  ev-Maybe :
    ((x : Maybe A) → B x) → ((x : A) → B (unit-Maybe x)) × B exception-Maybe
  ev-Maybe = {!!}

  ind-Maybe :
    ((x : A) → B (unit-Maybe x)) × (B exception-Maybe) → (x : Maybe A) → B x
  ind-Maybe = {!!}

  abstract
    is-section-ind-Maybe : (ev-Maybe ∘ ind-Maybe) ~ id
    is-section-ind-Maybe (pair h b) = {!!}

    is-retraction-ind-Maybe' :
      (h : (x : Maybe A) → B x) → (ind-Maybe (ev-Maybe h)) ~ h
    is-retraction-ind-Maybe' = {!!}

    is-retraction-ind-Maybe : (ind-Maybe ∘ ev-Maybe) ~ id
    is-retraction-ind-Maybe h = {!!}

    dependent-universal-property-Maybe :
      is-equiv ev-Maybe
    dependent-universal-property-Maybe = {!!}

equiv-dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} (B : Maybe A → UU l2) →
  ((x : Maybe A) → B x) ≃ (((x : A) → B (unit-Maybe x)) × B exception-Maybe)
equiv-dependent-universal-property-Maybe = {!!}

equiv-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (Maybe A → B) ≃ ((A → B) × B)
equiv-universal-property-Maybe = {!!}
```
