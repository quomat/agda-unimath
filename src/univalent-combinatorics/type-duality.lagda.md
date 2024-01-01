# Type duality of finite types

```agda
module univalent-combinatorics.type-duality where

open import foundation.type-duality public
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.structure
open import foundation.structured-type-duality
open import foundation.surjective-maps
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Properties

### Subtype duality

```agda
equiv-surjection-𝔽-family-finite-inhabited-type :
  {l : Level} (A : 𝔽 l) (B : 𝔽 l) →
  ( (type-𝔽 A ↠ type-𝔽 B) ≃
    ( Σ ( (type-𝔽 B) → Inhabited-𝔽 l)
        ( λ Y → (type-𝔽 A) ≃ Σ (type-𝔽 B) (λ b → type-Inhabited-𝔽 (Y b)))))
equiv-surjection-𝔽-family-finite-inhabited-type = {!!}

Slice-Surjection-𝔽 : (l : Level) {l1 : Level} (A : 𝔽 l1) → UU (lsuc l ⊔ l1)
Slice-Surjection-𝔽 l A = {!!}

equiv-Fiber-trunc-Prop-𝔽 :
  (l : Level) {l1 : Level} (A : 𝔽 l1) →
  Slice-Surjection-𝔽 (l1 ⊔ l) A ≃ (type-𝔽 A → Inhabited-𝔽 (l1 ⊔ l))
equiv-Fiber-trunc-Prop-𝔽 = {!!}
```
