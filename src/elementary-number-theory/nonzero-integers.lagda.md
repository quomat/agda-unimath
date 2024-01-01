# Nonzero integers

```agda
module elementary-number-theory.nonzero-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An [integer](elementary-number-theory.integers.md) `k` is said to be **nonzero**
if the [proposition](foundation.propositions.md)

```text
  k ≠ 0
```

holds.

## Definition

### The predicate of being a nonzero integer

```agda
is-nonzero-prop-ℤ : ℤ → Prop lzero
is-nonzero-prop-ℤ k = {!!}

is-nonzero-ℤ : ℤ → UU lzero
is-nonzero-ℤ k = {!!}

is-prop-is-nonzero-ℤ : (k : ℤ) → is-prop (is-nonzero-ℤ k)
is-prop-is-nonzero-ℤ k = {!!}
```

### The nonzero integers

```agda
nonzero-ℤ : UU lzero
nonzero-ℤ = {!!}

module _
  (k : nonzero-ℤ)
  where

  int-nonzero-ℤ : ℤ
  int-nonzero-ℤ = {!!}

  is-nonzero-nonzero-ℤ : is-nonzero-ℤ int-nonzero-ℤ
  is-nonzero-nonzero-ℤ = {!!}
```

### The nonzero integer `1`

```agda
is-nonzero-one-ℤ : is-nonzero-ℤ one-ℤ
is-nonzero-one-ℤ ()

one-nonzero-ℤ : nonzero-ℤ
pr1 one-nonzero-ℤ = {!!}
pr2 one-nonzero-ℤ = {!!}
```

## Properties

### The inclusion of natural numbers into integers maps nonzero natural numbers to nonzero integers

```agda
is-nonzero-int-ℕ : (n : ℕ) → is-nonzero-ℕ n → is-nonzero-ℤ (int-ℕ n)
is-nonzero-int-ℕ zero-ℕ H p = {!!}
```

### Positive integers are nonzero

```agda
is-nonzero-is-positive-ℤ : (x : ℤ) → is-positive-ℤ x → is-nonzero-ℤ x
is-nonzero-is-positive-ℤ (inr (inr x)) H ()
```
