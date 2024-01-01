# Subtype duality

```agda
module foundation.subtype-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-maps
open import foundation.structured-type-duality
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
```

</details>

## Theorem

### Subtype duality

```agda
Slice-emb : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-emb = {!!}

equiv-Fiber-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-emb (l1 ⊔ l) A ≃ (A → Prop (l1 ⊔ l))
equiv-Fiber-Prop = {!!}

Slice-surjection : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-surjection = {!!}

equiv-Fiber-trunc-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-surjection (l1 ⊔ l) A ≃ (A → Inhabited-Type (l1 ⊔ l))
equiv-Fiber-trunc-Prop = {!!}
```
