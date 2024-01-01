# Squares in the natural numbers

```agda
module elementary-number-theory.squares-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The {{#concept "square" Disambiguation="natural number"}} `n²` of a
[natural number](elementary-number-theory.natural-numbers.md) `n` is the
[product](elementary-number-theory.multiplication-natural-numbers.md)

```text
  n² := {!!}
```

of `n` with itself.

## Definition

### Squares of natural numbers

```agda
square-ℕ : ℕ → ℕ
square-ℕ n = {!!}
```

### The predicate of being a square of a natural number

```agda
is-square-ℕ : ℕ → UU lzero
is-square-ℕ n = {!!}
```

### The square root of a square natural number

```agda
square-root-ℕ : (n : ℕ) → is-square-ℕ n → ℕ
square-root-ℕ _ (root , _) = {!!}
```

## Properties

### Squares of successors

```agda
square-succ-ℕ :
  (n : ℕ) →
  square-ℕ (succ-ℕ n) ＝ succ-ℕ ((succ-ℕ (succ-ℕ n)) *ℕ n)
square-succ-ℕ n = {!!}

square-succ-succ-ℕ :
  (n : ℕ) →
  square-ℕ (succ-ℕ (succ-ℕ n)) ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ n +ℕ 4
square-succ-succ-ℕ n = {!!}
```

### `n > √n` for `n > 1`

The idea is to assume `n = {!!}
contradiction by squaring both sides of the inequality

```agda
greater-than-square-root-ℕ :
  (n root : ℕ) → ¬ ((n +ℕ 2 ≤-ℕ root) × (n +ℕ 2 ＝ square-ℕ root))
greater-than-square-root-ℕ n root (pf-leq , pf-eq) = {!!}
```

### Squareness in ℕ is decidable

```agda
is-decidable-big-root :
  (n : ℕ) → is-decidable (Σ ℕ (λ root → (n ≤-ℕ root) × (n ＝ square-ℕ root)))
is-decidable-big-root 0 = {!!}
is-decidable-big-root 1 = {!!}
is-decidable-big-root (succ-ℕ (succ-ℕ n)) = {!!}

is-decidable-is-square-ℕ : (n : ℕ) → is-decidable (is-square-ℕ n)
is-decidable-is-square-ℕ n = {!!}
```

## See also

- [Cubes of natural numbers](elementary-number-theory.cubes-natural-numbers.md)
