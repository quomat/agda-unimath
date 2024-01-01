# Descent for dependent pair types

```agda
module foundation.descent-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Theorem

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i))
  where

  cone-descent-Σ : cone (ind-Σ f) h (Σ I A')
  cone-descent-Σ = {!!}

  triangle-descent-Σ :
    (i : I) (a : A i) →
    ( map-fiber-cone (f i) h (c i) a) ~
    ( ( map-fiber-cone (ind-Σ f) h cone-descent-Σ (pair i a)) ∘
      ( map-inv-compute-fiber-tot (λ i → (pr1 (c i))) (pair i a)))
  triangle-descent-Σ = {!!}

  abstract
    descent-Σ :
      ((i : I) → is-pullback (f i) h (c i)) →
      is-pullback (ind-Σ f) h cone-descent-Σ
    descent-Σ = {!!}

  abstract
    descent-Σ' :
      is-pullback (ind-Σ f) h cone-descent-Σ →
      ((i : I) → is-pullback (f i) h (c i))
    descent-Σ' = {!!}
```
