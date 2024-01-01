# The dependent binomial theorem for types (distributivity of dependent function types over coproduct types)

```agda
module foundation.dependent-binomial-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-decompositions
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.raising-universe-levels
open import foundation.transport-along-identifications
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.univalence

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  fam-coprod :
    Fin 2 → UU (l1 ⊔ l2)
  fam-coprod = {!!}

  map-compute-total-fam-coprod :
    Σ (Fin 2) fam-coprod → A + B
  map-compute-total-fam-coprod = {!!}

  map-inv-compute-total-fam-coprod :
    A + B → Σ (Fin 2) fam-coprod
  map-inv-compute-total-fam-coprod = {!!}

  is-section-map-inv-compute-total-fam-coprod :
    (map-compute-total-fam-coprod ∘ map-inv-compute-total-fam-coprod) ~ id
  is-section-map-inv-compute-total-fam-coprod = {!!}

  is-retraction-map-inv-compute-total-fam-coprod :
    (map-inv-compute-total-fam-coprod ∘ map-compute-total-fam-coprod) ~ id
  is-retraction-map-inv-compute-total-fam-coprod = {!!}

  is-equiv-map-compute-total-fam-coprod :
    is-equiv map-compute-total-fam-coprod
  is-equiv-map-compute-total-fam-coprod = {!!}

  compute-total-fam-coprod :
    (Σ (Fin 2) fam-coprod) ≃ (A + B)
  compute-total-fam-coprod = {!!}

  inv-compute-total-fam-coprod :
    (A + B) ≃ Σ (Fin 2) fam-coprod
  inv-compute-total-fam-coprod = {!!}

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  type-distributive-Π-coprod : UU (l1 ⊔ l2 ⊔ l3)
  type-distributive-Π-coprod = {!!}

  distributive-Π-coprod :
    ((x : X) → A x + B x) ≃ type-distributive-Π-coprod
  distributive-Π-coprod = {!!}

  type-distributive-Π-coprod-binary-coproduct-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l1 ⊔ lsuc l1)
  type-distributive-Π-coprod-binary-coproduct-Decomposition = {!!}

  equiv-type-distributive-Π-coprod-binary-coproduct-Decomposition :
    type-distributive-Π-coprod ≃
    type-distributive-Π-coprod-binary-coproduct-Decomposition
  equiv-type-distributive-Π-coprod-binary-coproduct-Decomposition = {!!}

  distributive-Π-coprod-binary-coproduct-Decomposition :
    ((x : X) → A x + B x) ≃
    type-distributive-Π-coprod-binary-coproduct-Decomposition
  distributive-Π-coprod-binary-coproduct-Decomposition = {!!}
```
