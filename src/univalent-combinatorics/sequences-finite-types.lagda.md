# Sequences of elements in finite types

```agda
module univalent-combinatorics.sequences-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions-of-values
open import foundation.repetitions-sequences
open import foundation.sequences
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Sequences of elements in finite types must have repetitions. Furthermore, since
equality in finite types is decidable, there must be a first repetition in any
sequence of elements in a finite type.

## Properties

```agda
repetition-of-values-sequence-Fin :
  (k : ℕ) (f : ℕ → Fin k) → repetition-of-values f
repetition-of-values-sequence-Fin k f = {!!}

pair-of-distinct-elements-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → pair-of-distinct-elements ℕ
pair-of-distinct-elements-repetition-of-values-sequence-Fin k f = {!!}

first-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → ℕ
first-repetition-of-values-sequence-Fin k f = {!!}

second-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → ℕ
second-repetition-of-values-sequence-Fin k f = {!!}

distinction-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) →
  first-repetition-of-values-sequence-Fin k f ≠
  second-repetition-of-values-sequence-Fin k f
distinction-repetition-of-values-sequence-Fin k f = {!!}

is-repetition-pair-of-distinct-elements-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) →
  is-repetition-of-values f
    ( pair-of-distinct-elements-repetition-of-values-sequence-Fin k f)
is-repetition-pair-of-distinct-elements-repetition-of-values-sequence-Fin k f = {!!}

le-first-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) →
  le-ℕ (first-repetition-of-values-sequence-Fin k f) (succ-ℕ k)
le-first-repetition-of-values-sequence-Fin k f = {!!}
```

### Ordered repetitions of values of maps out of the natural numbers

```agda
repetition-of-values-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) → repetition-of-values f
repetition-of-values-nat-to-count e f = {!!}

ordered-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : ℕ → Fin k) → ordered-repetition-of-values-ℕ f
ordered-repetition-of-values-sequence-Fin k f = {!!}

ordered-repetition-of-values-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) →
  ordered-repetition-of-values-ℕ f
ordered-repetition-of-values-nat-to-count e f = {!!}

minimal-element-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : ℕ → Fin k) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (f y ＝ f x)))
minimal-element-repetition-of-values-sequence-Fin k f = {!!}

minimal-element-repetition-of-values-sequence-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (f y ＝ f x)))
minimal-element-repetition-of-values-sequence-count (k , e) f = {!!}
```
