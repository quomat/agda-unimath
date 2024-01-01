# Nonzero natural numbers

```agda
module elementary-number-theory.nonzero-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A [natural number](elementary-number-theory.natural-numbers.md) `n` is said to
be **nonzero** if the [proposition](foundation.propositions.md)

```text
  n ≠ 0
```

holds. This condition was already defined in the file
[`elementary-number-theory.natural-numbers`](elementary-number-theory.natural-numbers.md).
The type of nonzero natural numbers consists of natural numbers equipped with a
proof that they are nonzero.

## Definitions

### The type of nonzero natural numbers

```agda
nonzero-ℕ : UU lzero
nonzero-ℕ = {!!}

nat-nonzero-ℕ : nonzero-ℕ → ℕ
nat-nonzero-ℕ = {!!}

is-nonzero-nat-nonzero-ℕ : (n : nonzero-ℕ) → is-nonzero-ℕ (nat-nonzero-ℕ n)
is-nonzero-nat-nonzero-ℕ = {!!}
```

### The nonzero natural number `1`

```agda
one-nonzero-ℕ : nonzero-ℕ
one-nonzero-ℕ = {!!}
pr2 one-nonzero-ℕ = {!!}
```

### The successor function on the nonzero natural numbers

```agda
succ-nonzero-ℕ : nonzero-ℕ → nonzero-ℕ
succ-nonzero-ℕ = {!!}
pr2 (succ-nonzero-ℕ (pair x _)) = {!!}
```

### The successor function from the natural numbers to the nonzero natural numbers

```agda
succ-nonzero-ℕ' : ℕ → nonzero-ℕ
succ-nonzero-ℕ' = {!!}
pr2 (succ-nonzero-ℕ' n) = {!!}
```

### The quotient of a nonzero natural number by a divisor

```agda
quotient-div-nonzero-ℕ :
  (d : ℕ) (x : nonzero-ℕ) (H : div-ℕ d (pr1 x)) → nonzero-ℕ
quotient-div-nonzero-ℕ = {!!}
```
