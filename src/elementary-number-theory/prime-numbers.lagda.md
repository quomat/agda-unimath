# Prime numbers

```agda
module elementary-number-theory.prime-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.proper-divisors-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A prime number is a natural number of which 1 is the only proper divisor.

## Definition

### The main definition of prime numbers

This is a direct interpretation of what it means to be prime.

```agda
is-prime-ℕ : ℕ → UU lzero
is-prime-ℕ = {!!}

Prime-ℕ : UU lzero
Prime-ℕ = {!!}

module _
  (p : Prime-ℕ)
  where

  nat-Prime-ℕ : ℕ
  nat-Prime-ℕ = {!!}

  is-prime-Prime-ℕ : is-prime-ℕ nat-Prime-ℕ
  is-prime-Prime-ℕ = {!!}
```

### Second definition of prime numbers

This is an implementation of the idea of being prime, which is usually taken as
the definition.

```agda
is-one-is-proper-divisor-ℕ : ℕ → UU lzero
is-one-is-proper-divisor-ℕ = {!!}

is-prime-easy-ℕ : ℕ → UU lzero
is-prime-easy-ℕ = {!!}
```

### Third definition of prime numbers

```agda
has-unique-proper-divisor-ℕ : ℕ → UU lzero
has-unique-proper-divisor-ℕ = {!!}
```

## Properties

### The number `0` is not a prime

```agda
is-nonzero-is-prime-ℕ :
  (n : ℕ) → is-prime-ℕ n → is-nonzero-ℕ n
is-nonzero-is-prime-ℕ = {!!}
```

### The number `1` is not a prime

```agda
is-not-one-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-not-one-ℕ n
is-not-one-is-prime-ℕ = {!!}
```

### A prime is strictly greater than `1`

```agda
le-one-is-prime-ℕ :
  (n : ℕ) → is-prime-ℕ n → le-ℕ 1 n
le-one-is-prime-ℕ = {!!}
```

### Being a prime is a proposition

```agda
is-prop-is-prime-ℕ :
  (n : ℕ) → is-prop (is-prime-ℕ n)
is-prop-is-prime-ℕ = {!!}

is-prime-ℕ-Prop :
  (n : ℕ) → Prop lzero
is-prime-ℕ-Prop = {!!}

is-prop-has-unique-proper-divisor-ℕ :
  (n : ℕ) → is-prop (has-unique-proper-divisor-ℕ n)
is-prop-has-unique-proper-divisor-ℕ = {!!}
```

### The three definitions of primes are equivalent

```agda
is-prime-easy-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-prime-easy-ℕ n
is-prime-easy-is-prime-ℕ = {!!}
pr2 (is-prime-easy-is-prime-ℕ n H) x = {!!}

is-prime-is-prime-easy-ℕ : (n : ℕ) → is-prime-easy-ℕ n → is-prime-ℕ n
is-prime-is-prime-easy-ℕ = {!!}
pr1 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) q = {!!}
pr2 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) = {!!}

has-unique-proper-divisor-is-prime-ℕ :
  (n : ℕ) → is-prime-ℕ n → has-unique-proper-divisor-ℕ n
has-unique-proper-divisor-is-prime-ℕ = {!!}

is-prime-has-unique-proper-divisor-ℕ :
  (n : ℕ) → has-unique-proper-divisor-ℕ n → is-prime-ℕ n
is-prime-has-unique-proper-divisor-ℕ = {!!}
```

### Being a prime is decidable

```agda
is-decidable-is-prime-easy-ℕ : (n : ℕ) → is-decidable (is-prime-easy-ℕ n)
is-decidable-is-prime-easy-ℕ = {!!}
is-decidable-is-prime-easy-ℕ (succ-ℕ n) = {!!}

is-decidable-is-prime-ℕ : (n : ℕ) → is-decidable (is-prime-ℕ n)
is-decidable-is-prime-ℕ = {!!}
```

### The number `2` is a prime

```agda
is-one-is-proper-divisor-two-ℕ : is-one-is-proper-divisor-ℕ 2
is-one-is-proper-divisor-two-ℕ = {!!}
is-one-is-proper-divisor-two-ℕ (succ-ℕ zero-ℕ) (pair f H) = {!!}
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (pair f H) = {!!}
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) (pair f H) = {!!}

is-prime-easy-two-ℕ : is-prime-easy-ℕ 2
is-prime-easy-two-ℕ = {!!}
pr2 is-prime-easy-two-ℕ = {!!}

is-prime-two-ℕ : is-prime-ℕ 2
is-prime-two-ℕ = {!!}
```

### If a prime number `p` divides a nonzero number `x`, then `x/p < x`

```agda
le-quotient-div-is-prime-ℕ :
  (p x : ℕ) → is-nonzero-ℕ x → is-prime-ℕ p →
  (H : div-ℕ p x) → le-ℕ (quotient-div-ℕ p x H) x
le-quotient-div-is-prime-ℕ = {!!}
```

### If a prime number `p` divides a number `x + 1`, then `(x + 1)/p ≤ x`

```agda
leq-quotient-div-is-prime-ℕ :
  (p x : ℕ) → is-prime-ℕ p →
  (H : div-ℕ p (succ-ℕ x)) → leq-ℕ (quotient-div-ℕ p (succ-ℕ x) H) x
leq-quotient-div-is-prime-ℕ = {!!}
```

## See also

- The fundamental theorem of arithmetic asserts that every positive natural
  number can be written uniquely as a product of primes. This theorem is proven
  in
  [`fundamental-theorem-of-arithmetic`](elementary-number-theory.fundamental-theorem-of-arithmetic.md).
