# The universal property of truncations

```agda
module foundation.universal-property-truncation where

open import foundation-core.universal-property-truncation public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### A map `f : A → B` is a `k+1`-truncation if and only if it is surjective and `ap f : (x ＝ y) → (f x ＝ f y)` is a `k`-truncation for all `x y : A`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 (succ-𝕋 k))
  {f : A → type-Truncated-Type B} (H : is-surjective f)
  ( K :
    (x y : A) → is-truncation (Id-Truncated-Type B (f x) (f y)) (ap f {x} {y}))
  where

  unique-extension-fiber-is-truncation-is-truncation-ap :
    {l : Level} (C : Truncated-Type l (succ-𝕋 k))
    (g : A → type-Truncated-Type C) (y : type-Truncated-Type B) →
    is-contr
      ( Σ ( type-Truncated-Type C)
          ( λ z → (t : fiber f y) → g (pr1 t) ＝ z))
  unique-extension-fiber-is-truncation-is-truncation-ap C g = {!!}

  is-truncation-is-truncation-ap :
    is-truncation B f
  is-truncation-is-truncation-ap C = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 (succ-𝕋 k))
  {f : A → type-Truncated-Type B}
  where

  is-surjective-is-truncation :
    is-truncation B f → is-surjective f
  is-surjective-is-truncation H = {!!}
```
