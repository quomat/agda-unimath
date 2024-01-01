# Pisano periods

```agda
module elementary-number-theory.pisano-periods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.repetitions-sequences
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.sequences-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sequence `P : ℕ → ℕ` of **Pisano periods** is the sequence where `P n` is
the period of the Fibonacci sequence modulo `n`. This sequence is listed as
[A001175](https://oeis.org/A001175) in the OEIS.

## Definitions

### The Fibonacci sequence on `Fin (k + 1) × Fin (k + 1)`

```agda
generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
generating-map-fibonacci-pair-Fin = {!!}

inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
inv-generating-map-fibonacci-pair-Fin = {!!}

is-section-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id
    ( generating-map-fibonacci-pair-Fin k
      ( inv-generating-map-fibonacci-pair-Fin k p))
    ( p)
is-section-inv-generating-map-fibonacci-pair-Fin = {!!}

is-retraction-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id
    ( inv-generating-map-fibonacci-pair-Fin k
      ( generating-map-fibonacci-pair-Fin k p))
    ( p)
is-retraction-inv-generating-map-fibonacci-pair-Fin = {!!}

is-equiv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → is-equiv (generating-map-fibonacci-pair-Fin k)
is-equiv-generating-map-fibonacci-pair-Fin = {!!}

fibonacci-pair-Fin :
  (k : ℕ) → ℕ → Fin (succ-ℕ k) × Fin (succ-ℕ k)
fibonacci-pair-Fin = {!!}
fibonacci-pair-Fin k (succ-ℕ n) = {!!}

compute-fibonacci-pair-Fin :
  (k : ℕ) (n : ℕ) →
  Id
    ( fibonacci-pair-Fin k n)
    ( mod-succ-ℕ k (Fibonacci-ℕ n) , mod-succ-ℕ k (Fibonacci-ℕ (succ-ℕ n)))
compute-fibonacci-pair-Fin = {!!}
compute-fibonacci-pair-Fin k (succ-ℕ zero-ℕ) = {!!}
compute-fibonacci-pair-Fin k (succ-ℕ (succ-ℕ n)) = {!!}
```

### Repetitions in the Fibonacci sequence on `Fin (k + 1) × Fin (k + 1)`

```agda
has-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) → ordered-repetition-of-values-ℕ (fibonacci-pair-Fin k)
has-ordered-repetition-fibonacci-pair-Fin = {!!}

is-ordered-repetition-fibonacci-pair-Fin : ℕ → ℕ → UU lzero
is-ordered-repetition-fibonacci-pair-Fin = {!!}

minimal-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) → minimal-element-ℕ (is-ordered-repetition-fibonacci-pair-Fin k)
minimal-ordered-repetition-fibonacci-pair-Fin = {!!}
```

### The Pisano periods

```agda
pisano-period : ℕ → ℕ
pisano-period = {!!}

is-ordered-repetition-pisano-period :
  (k : ℕ) → is-ordered-repetition-fibonacci-pair-Fin k (pisano-period k)
is-ordered-repetition-pisano-period = {!!}

is-lower-bound-pisano-period :
  (k : ℕ) →
  is-lower-bound-ℕ
    ( is-ordered-repetition-fibonacci-pair-Fin k)
    ( pisano-period k)
is-lower-bound-pisano-period = {!!}

cases-is-repetition-of-zero-pisano-period :
  (k x y : ℕ) → Id (pr1 (is-ordered-repetition-pisano-period k)) x →
  Id (pisano-period k) y → is-zero-ℕ x
cases-is-repetition-of-zero-pisano-period = {!!}
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) zero-ℕ p q = {!!}
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) (succ-ℕ y) p q = {!!}

is-repetition-of-zero-pisano-period :
  (k : ℕ) → is-zero-ℕ (pr1 (is-ordered-repetition-pisano-period k))
is-repetition-of-zero-pisano-period = {!!}

compute-fibonacci-pair-Fin-pisano-period :
  (k : ℕ) →
  Id (fibonacci-pair-Fin k (pisano-period k)) (fibonacci-pair-Fin k zero-ℕ)
compute-fibonacci-pair-Fin-pisano-period = {!!}
```

## Properties

### Pisano periods are nonzero

```agda
le-zero-pisano-period :
  (k : ℕ) → le-ℕ zero-ℕ (pisano-period k)
le-zero-pisano-period = {!!}

is-nonzero-pisano-period :
  (k : ℕ) → is-nonzero-ℕ (pisano-period k)
is-nonzero-pisano-period = {!!}
```

### `k + 1` divides the Fibonacci number at `pisano-period k`

```agda
div-fibonacci-pisano-period :
  (k : ℕ) → div-ℕ (succ-ℕ k) (Fibonacci-ℕ (pisano-period k))
div-fibonacci-pisano-period = {!!}
```
