# Finite choice

```agda
module univalent-combinatorics.finite-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.empty-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Propositional truncations distributes over finite products.

## Theorems

```agda
abstract
  finite-choice-Fin :
    {l1 : Level} (k : ℕ) {Y : Fin k → UU l1} →
    ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
  finite-choice-Fin {l1} zero-ℕ {Y} H = {!!}

abstract
  finite-choice-count :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → count X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice-count {l1} {l2} {X} {Y} (pair k e) H = {!!}

abstract
  finite-choice :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → is-finite X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice {l1} {l2} {X} {Y} is-finite-X H = {!!}
```

```agda
abstract
  ε-operator-count :
    {l : Level} {A : UU l} → count A → ε-operator-Hilbert A
  ε-operator-count (pair zero-ℕ e) t = {!!}

abstract
  ε-operator-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) (P : decidable-subtype l2 A) →
    ε-operator-Hilbert (type-decidable-subtype P)
  ε-operator-decidable-subtype-count e P = {!!}
```

```agda
abstract
  ε-operator-emb-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} →
    (f : B ↪ᵈ A) → ε-operator-Hilbert B
  ε-operator-emb-count e f t = {!!}
```

```agda
abstract
  choice-count-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
  choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x = {!!}

abstract
  choice-is-finite-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
  choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H = {!!}
```
