# Choice of representatives for an equivalence relation

```agda
module foundation.choice-of-representatives-equivalence-relation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
```

</details>

## Idea

If we can construct a choice of representatives for each equivalence class, then
we can construct the set quotient as a retract of the original type.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-choice-of-representatives :
    (A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-choice-of-representatives P = {!!}

  representatives :
    {P : A → UU l3} → is-choice-of-representatives P → UU (l1 ⊔ l3)
  representatives {P} H = {!!}

  class-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H → equivalence-class R
  class-representatives H a = {!!}

  abstract
    is-surjective-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-surjective (class-representatives H)
    is-surjective-class-representatives H (pair Q K) = {!!}

  abstract
    is-emb-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-emb (class-representatives H)
    is-emb-class-representatives {P} H (pair a p) = {!!}

  abstract
    is-equiv-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-equiv (class-representatives H)
    is-equiv-class-representatives H = {!!}

  equiv-equivalence-class-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H ≃ equivalence-class R
  pr1 (equiv-equivalence-class-representatives H) = {!!}
```
