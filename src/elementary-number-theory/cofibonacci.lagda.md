# The cofibonacci sequence

```agda
module elementary-number-theory.cofibonacci where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.pisano-periods
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The [**cofibonacci sequence**][1] is the unique function G : ℕ → ℕ satisfying
the property that

```text
  div-ℕ (G m) n ↔ div-ℕ m (Fibonacci-ℕ n).
```

## Definitions

### The predicate of being a multiple of the `m`-th cofibonacci number

```agda
is-multiple-of-cofibonacci : (m x : ℕ) → UU lzero
is-multiple-of-cofibonacci = {!!}

is-decidable-is-multiple-of-cofibonacci :
  (m x : ℕ) → is-decidable (is-multiple-of-cofibonacci m x)
is-decidable-is-multiple-of-cofibonacci = {!!}

cofibonacci-multiple : (m : ℕ) → Σ ℕ (is-multiple-of-cofibonacci m)
cofibonacci-multiple = {!!}
cofibonacci-multiple (succ-ℕ m) = {!!}
```

### The cofibonacci sequence

```agda
least-multiple-of-cofibonacci :
  (m : ℕ) → minimal-element-ℕ (is-multiple-of-cofibonacci m)
least-multiple-of-cofibonacci = {!!}

cofibonacci : ℕ → ℕ
cofibonacci = {!!}

is-multiple-of-cofibonacci-cofibonacci :
  (m : ℕ) → is-multiple-of-cofibonacci m (cofibonacci m)
is-multiple-of-cofibonacci-cofibonacci = {!!}

is-lower-bound-cofibonacci :
  (m x : ℕ) → is-multiple-of-cofibonacci m x →
  cofibonacci m ≤-ℕ x
is-lower-bound-cofibonacci = {!!}
```

## Properties

### The `0`-th cofibonacci number is `0`

```agda
is-zero-cofibonacci-zero-ℕ : is-zero-ℕ (cofibonacci zero-ℕ)
is-zero-cofibonacci-zero-ℕ = {!!}
```

### The cofibonacci sequence is left adjoint to the Fibonacci sequence

```agda
forward-is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n → div-ℕ m (Fibonacci-ℕ n)
forward-is-left-adjoint-cofibonacci = {!!}

{-
converse-is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ m (Fibonacci-ℕ n) → div-ℕ (cofibonacci m) n
converse-is-left-adjoint-cofibonacci = {!!}

is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n ↔ div-ℕ m (Fibonacci-ℕ n)
is-left-adjoint-cofibonacci = {!!}
-}
```

## References

[1]: https://oeis.org/A001177
