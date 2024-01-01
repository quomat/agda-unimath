# Strictly ordered pairs of natural numbers

```agda
module elementary-number-theory.strictly-ordered-pairs-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A strictly ordered pair of natural numbers consists of `x y : ℕ` such that
`x < y`.

## Definition

```agda
strictly-ordered-pair-ℕ : UU lzero
strictly-ordered-pair-ℕ = {!!}

module _
  (p : strictly-ordered-pair-ℕ)
  where

  first-strictly-ordered-pair-ℕ : ℕ
  first-strictly-ordered-pair-ℕ = {!!}

  second-strictly-ordered-pair-ℕ : ℕ
  second-strictly-ordered-pair-ℕ = {!!}

  strict-inequality-strictly-ordered-pair-ℕ :
    le-ℕ first-strictly-ordered-pair-ℕ second-strictly-ordered-pair-ℕ
  strict-inequality-strictly-ordered-pair-ℕ = {!!}
```

## Properties

### Strictly ordered pairs of natural numbers are pairs of distinct elements

```agda
pair-of-distinct-elements-strictly-ordered-pair-ℕ :
  strictly-ordered-pair-ℕ → pair-of-distinct-elements ℕ
pair-of-distinct-elements-strictly-ordered-pair-ℕ = {!!}
```

### Any pair of distinct elements of natural numbers can be strictly ordered

```agda
strictly-ordered-pair-pair-of-distinct-elements-ℕ' :
  (a b : ℕ) → a ≠ b → strictly-ordered-pair-ℕ
strictly-ordered-pair-pair-of-distinct-elements-ℕ' = {!!}

strictly-ordered-pair-pair-of-distinct-elements-ℕ :
  pair-of-distinct-elements ℕ → strictly-ordered-pair-ℕ
strictly-ordered-pair-pair-of-distinct-elements-ℕ = {!!}
```
