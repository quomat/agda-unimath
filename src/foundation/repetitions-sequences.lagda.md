# Repetitions in sequences

```agda
module foundation.repetitions-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strictly-ordered-pairs-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions-of-values
open import foundation.sequences
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Idea

A repetition in a sequence `a : ℕ → A` consists of a pair of distinct natural
numbers `m` and `n` such that `a m = {!!}

## Definition

### Repetitions of values in a sequence

```agda
is-repetition-of-values-sequence :
  {l : Level} {A : UU l} (a : sequence A) (p : pair-of-distinct-elements ℕ) →
  UU l
is-repetition-of-values-sequence = {!!}

repetition-of-values-sequence :
  {l : Level} {A : UU l} → sequence A → UU l
repetition-of-values-sequence = {!!}

module _
  {l : Level} {A : UU l} (a : sequence A) (r : repetition-of-values-sequence a)
  where

  pair-of-distinct-elements-repetition-of-values-sequence :
    pair-of-distinct-elements ℕ
  pair-of-distinct-elements-repetition-of-values-sequence = {!!}

  first-repetition-of-values-sequence : ℕ
  first-repetition-of-values-sequence = {!!}

  second-repetition-of-values-sequence : ℕ
  second-repetition-of-values-sequence = {!!}

  distinction-repetition-of-values-sequence :
    first-repetition-of-values-sequence ≠ second-repetition-of-values-sequence
  distinction-repetition-of-values-sequence = {!!}

  is-repetition-of-values-repetition-of-values-sequence :
    is-repetition-of-values a
      pair-of-distinct-elements-repetition-of-values-sequence
  is-repetition-of-values-repetition-of-values-sequence = {!!}
```

### Ordered repetitions of values in a sequence

```agda
is-ordered-repetition-of-values-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) (x : strictly-ordered-pair-ℕ) → UU l1
is-ordered-repetition-of-values-ℕ = {!!}

ordered-repetition-of-values-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) → UU l1
ordered-repetition-of-values-ℕ = {!!}

ordered-repetition-of-values-comp-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : A → B) {f : ℕ → A} →
  ordered-repetition-of-values-ℕ f →
  ordered-repetition-of-values-ℕ (g ∘ f)
ordered-repetition-of-values-comp-ℕ = {!!}

ordered-repetition-of-values-right-factor-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {g : A → B} {f : ℕ → A} →
  is-emb g → ordered-repetition-of-values-ℕ (g ∘ f) →
  ordered-repetition-of-values-ℕ f
ordered-repetition-of-values-right-factor-ℕ = {!!}
```

### Any repetition of values in a sequence can be ordered

```agda
module _
  {l : Level} {A : UU l}
  where

  ordered-repetition-of-values-repetition-of-values-ℕ' :
    (f : ℕ → A) (a b : ℕ) → a ≠ b → f a ＝ f b →
    ordered-repetition-of-values-ℕ f
  ordered-repetition-of-values-repetition-of-values-ℕ' = {!!}

  ordered-repetition-of-values-repetition-of-values-ℕ :
    (f : ℕ → A) → repetition-of-values f → ordered-repetition-of-values-ℕ f
  ordered-repetition-of-values-repetition-of-values-ℕ = {!!}
```
