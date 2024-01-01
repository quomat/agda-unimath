# The binomial coefficients

```agda
module elementary-number-theory.binomial-coefficients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial coefficient `(n choose k)` measures how many decidable subsets of
`Fin n` there are of size `k`.

## Definition

### Binomial coefficients of natural numbers

```agda
binomial-coefficient-ℕ : ℕ → ℕ → ℕ
binomial-coefficient-ℕ zero-ℕ zero-ℕ = {!!}
binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) = {!!}
binomial-coefficient-ℕ (succ-ℕ n) zero-ℕ = {!!}
binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) = {!!}
```

### Binomial coefficients indexed by elements of standard finite types

```agda
binomial-coefficient-Fin : (n : ℕ) → Fin (succ-ℕ n) → ℕ
binomial-coefficient-Fin n x = {!!}
```

## Properties

### If `k > n` then `binomial-coefficient-ℕ n k ＝ 0`

```agda
is-zero-binomial-coefficient-ℕ :
  (n k : ℕ) → le-ℕ n k → is-zero-ℕ (binomial-coefficient-ℕ n k)
is-zero-binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) _ = {!!}
is-zero-binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) H = {!!}
```

### `binomial-coefficient-ℕ n n ＝ 1`

```agda
is-one-on-diagonal-binomial-coefficient-ℕ :
  (n : ℕ) → is-one-ℕ (binomial-coefficient-ℕ n n)
is-one-on-diagonal-binomial-coefficient-ℕ zero-ℕ = {!!}
is-one-on-diagonal-binomial-coefficient-ℕ (succ-ℕ n) = {!!}
```
