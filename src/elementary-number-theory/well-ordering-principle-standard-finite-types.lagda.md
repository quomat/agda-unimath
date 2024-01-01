# The well-ordering principle of the standard finite types

```agda
module elementary-number-theory.well-ordering-principle-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The standard finite types inherit a well-ordering principle from the natural
numbers.

## Properties

### For any decidable family `P` over `Fin n`, if `P x` doesn't hold for all `x` then there exists an `x` for which `P x` is false

```agda
exists-not-not-forall-Fin :
  {l : Level} (k : ℕ) {P : Fin k → UU l} → (is-decidable-fam P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-forall-Fin = {!!}
... | inr f = {!!}

exists-not-not-forall-count :
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) →
  (is-decidable-fam P) → count X →
  ¬ ((x : X) → P x) → Σ X (λ x → ¬ (P x))
exists-not-not-forall-count = {!!}
```

```agda
is-lower-bound-Fin :
  {l : Level} (k : ℕ) (P : Fin k → UU l) → Fin k → UU l
is-lower-bound-Fin = {!!}

abstract
  is-prop-is-lower-bound-Fin :
    {l : Level} (k : ℕ) {P : Fin k → UU l} (x : Fin k) →
    is-prop (is-lower-bound-Fin k P x)
  is-prop-is-lower-bound-Fin = {!!}

  is-lower-bound-fin-Prop :
    {l : Level} (k : ℕ) (P : Fin k → UU l) (x : Fin k) → Prop l
  is-lower-bound-fin-Prop = {!!}

minimal-element-Fin :
  {l : Level} (k : ℕ) (P : Fin k → UU l) → UU l
minimal-element-Fin = {!!}

abstract
  all-elements-equal-minimal-element-Fin :
    {l : Level} (k : ℕ) (P : subtype l (Fin k)) →
    all-elements-equal (minimal-element-Fin k (is-in-subtype P))
  all-elements-equal-minimal-element-Fin = {!!}

abstract
  is-prop-minimal-element-Fin :
    {l : Level} (k : ℕ) (P : subtype l (Fin k)) →
    is-prop (minimal-element-Fin k (is-in-subtype P))
  is-prop-minimal-element-Fin = {!!}

minimal-element-Fin-Prop :
  {l : Level} (k : ℕ) (P : subtype l (Fin k)) → Prop l
minimal-element-Fin-Prop = {!!}

is-lower-bound-inl-Fin :
  {l : Level} (k : ℕ) {P : Fin (succ-ℕ k) → UU l} {x : Fin k} →
  is-lower-bound-Fin k (P ∘ inl) x →
  is-lower-bound-Fin (succ-ℕ k) P (inl-Fin k x)
is-lower-bound-inl-Fin = {!!}

well-ordering-principle-Σ-Fin :
  {l : Level} (k : ℕ) {P : Fin k → UU l} → ((x : Fin k) → is-decidable (P x)) →
  Σ (Fin k) P → minimal-element-Fin k P
well-ordering-principle-Σ-Fin = {!!}
... | inr f = {!!}

well-ordering-principle-∃-Fin :
  {l : Level} (k : ℕ) (P : decidable-subtype l (Fin k)) →
  ∃ (Fin k) (is-in-decidable-subtype P) →
  minimal-element-Fin k (is-in-decidable-subtype P)
well-ordering-principle-∃-Fin = {!!}
```

### Hilbert's `ε`-operator for decidable subtypes of standard finite types

```agda
ε-operator-decidable-subtype-Fin :
  {l : Level} (k : ℕ) (P : decidable-subtype l (Fin k)) →
  ε-operator-Hilbert (type-decidable-subtype P)
ε-operator-decidable-subtype-Fin = {!!}
```

```agda
abstract
  elim-trunc-decidable-fam-Fin :
    {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
    ((x : Fin k) → is-decidable (B x)) →
    type-trunc-Prop (Σ (Fin k) B) → Σ (Fin k) B
  elim-trunc-decidable-fam-Fin = {!!}
```
