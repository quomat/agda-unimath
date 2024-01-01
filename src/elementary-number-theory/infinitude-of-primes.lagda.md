# The infinitude of primes

```agda
module elementary-number-theory.infinitude-of-primes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.proper-divisors-natural-numbers
open import elementary-number-theory.sieve-of-eratosthenes
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.negation
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We show, using the sieve of Eratosthenes and the well-ordering principle of `ℕ`,
that there are infinitely many primes. Consequently we obtain the function that
returns for each `n` the `n`-th prime, and we obtain the function that counts
the number of primes below a number `n`.

## Definition

We begin by stating the infinitude of primes in type theory.

```agda
Infinitude-Of-Primes-ℕ : UU lzero
Infinitude-Of-Primes-ℕ = {!!}
```

## Theorem

### The infinitude of primes

```agda
minimal-element-in-sieve-of-eratosthenes-ℕ :
  (n : ℕ) → minimal-element-ℕ (in-sieve-of-eratosthenes-ℕ n)
minimal-element-in-sieve-of-eratosthenes-ℕ n = {!!}

larger-prime-ℕ : ℕ → ℕ
larger-prime-ℕ n = {!!}

in-sieve-of-eratosthenes-larger-prime-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (larger-prime-ℕ n)
in-sieve-of-eratosthenes-larger-prime-ℕ n = {!!}

is-one-is-divisor-below-larger-prime-ℕ :
  (n : ℕ) → is-one-is-divisor-below-ℕ n (larger-prime-ℕ n)
is-one-is-divisor-below-larger-prime-ℕ n = {!!}

le-larger-prime-ℕ : (n : ℕ) → le-ℕ n (larger-prime-ℕ n)
le-larger-prime-ℕ n = {!!}

is-nonzero-larger-prime-ℕ : (n : ℕ) → is-nonzero-ℕ (larger-prime-ℕ n)
is-nonzero-larger-prime-ℕ n = {!!}

is-lower-bound-larger-prime-ℕ :
  (n : ℕ) → is-lower-bound-ℕ (in-sieve-of-eratosthenes-ℕ n) (larger-prime-ℕ n)
is-lower-bound-larger-prime-ℕ n = {!!}

is-not-one-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-not-one-ℕ (larger-prime-ℕ n)
is-not-one-larger-prime-ℕ n H p with is-successor-is-nonzero-ℕ H
... | pair k refl = {!!}

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ :
  (n x : ℕ) → is-proper-divisor-ℕ (larger-prime-ℕ n) x →
  ¬ (in-sieve-of-eratosthenes-ℕ n x)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x H K = {!!}

is-one-is-proper-divisor-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-one-is-proper-divisor-ℕ (larger-prime-ℕ n)
is-one-is-proper-divisor-larger-prime-ℕ n H x (pair f K) = {!!}

is-prime-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-prime-ℕ (larger-prime-ℕ n)
is-prime-larger-prime-ℕ n H = {!!}

infinitude-of-primes-ℕ : Infinitude-Of-Primes-ℕ
infinitude-of-primes-ℕ n with is-decidable-is-zero-ℕ n
... | inl refl = {!!}
... | inr H = {!!}
```

## Consequences

### The function that returns the `n`-th prime

The function `prime-ℕ` is defined to start at `prime-ℕ 0 := {!!}

```agda
prime-ℕ : ℕ → ℕ
prime-ℕ n = {!!}

is-prime-prime-ℕ : (n : ℕ) → is-prime-ℕ (prime-ℕ n)
is-prime-prime-ℕ zero-ℕ = {!!}
is-prime-prime-ℕ (succ-ℕ n) = {!!}
```

### The prime counting function

The prime counting function is defined such that `prime-counting-ℕ n` is the
number of primes `≤ n`

```agda
prime-counting-succ-ℕ :
  (n : ℕ) → is-decidable (is-prime-ℕ (succ-ℕ n)) → ℕ → ℕ
prime-counting-succ-ℕ n (inl d) x = {!!}
prime-counting-succ-ℕ n (inr d) x = {!!}

prime-counting-ℕ : ℕ → ℕ
prime-counting-ℕ zero-ℕ = {!!}
prime-counting-ℕ (succ-ℕ n) = {!!}
```
