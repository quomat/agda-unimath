# The Fibonacci sequence

```agda
module elementary-number-theory.fibonacci-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Definitions

### The standard definition using pattern matching

```agda
Fibonacci-ℕ : ℕ → ℕ
Fibonacci-ℕ 0 = {!!}
Fibonacci-ℕ (succ-ℕ 0) = {!!}
Fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = {!!}
```

### A definition using the induction principle of `ℕ`

The above definition of the Fibonacci sequence uses Agda's powerful pattern
matching definitions. Below, we will give a definition of the Fibonacci sequence
in terms of `ind-ℕ`.

The problem with defining the Fibonacci sequence using `ind-ℕ`, is that `ind-ℕ`
doesn't give us a way to refer to both `(F n)` and `(F (succ-ℕ n))`. So, we have
to give a workaround, where we store two values in the Fibonacci sequence at
once.

The basic idea is that we define a sequence of pairs of integers, which will be
consecutive Fibonacci numbers. This would be a function of type $ℕ → ℕ²$.

Such a function is easy to give with induction, using the map $ℕ² → ℕ²$ that
takes a pair `(m,n)` to the pair `(n,n+m)`. Starting the iteration with `(0,1)`
we obtain the Fibonacci sequence by taking the first projection.

However, we haven't defined cartesian products or booleans yet. Therefore we
mimic the above idea, using $ℕ → ℕ$ instead of $ℕ²$.

```agda
shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = {!!}

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = {!!}

Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = {!!}

Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f = {!!}

Fibo-function : ℕ → ℕ → ℕ
Fibo-function = {!!}

Fibo : ℕ → ℕ
Fibo k = {!!}
```

## Properties

### `F(m+n+1) ＝ F(m+1)F(n+1) + F(m)F(n)`

```agda
Fibonacci-add-ℕ :
  (m n : ℕ) →
  Fibonacci-ℕ (m +ℕ (succ-ℕ n)) ＝
  ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ (succ-ℕ n))) +ℕ
  ( (Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ n))
Fibonacci-add-ℕ m zero-ℕ = {!!}
Fibonacci-add-ℕ m (succ-ℕ n) = {!!}
```

### Consecutive Fibonacci numbers are relatively prime

```agda
is-one-div-fibonacci-succ-div-fibonacci-ℕ :
  (d n : ℕ) → div-ℕ d (Fibonacci-ℕ n) → div-ℕ d (Fibonacci-ℕ (succ-ℕ n)) →
  is-one-ℕ d
is-one-div-fibonacci-succ-div-fibonacci-ℕ d zero-ℕ H K = {!!}
is-one-div-fibonacci-succ-div-fibonacci-ℕ d (succ-ℕ n) H K = {!!}

relatively-prime-fibonacci-fibonacci-succ-ℕ :
  (n : ℕ) → is-relatively-prime-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n))
relatively-prime-fibonacci-fibonacci-succ-ℕ n = {!!}
```

### A 3-for-2 property of divisibility of Fibonacci numbers

We prove that if an two of the following three properties hold, then so does the
third:

1. `d | Fibonacci-ℕ m`
2. `d | Fibonacci-ℕ n`
3. `d | Fibonacci-ℕ (m +ℕ n)`.

```agda
div-Fibonacci-add-ℕ :
  (d m n : ℕ) → div-ℕ d (Fibonacci-ℕ m) → div-ℕ d (Fibonacci-ℕ n) →
  div-ℕ d (Fibonacci-ℕ (m +ℕ n))
div-Fibonacci-add-ℕ d m zero-ℕ H1 H2 = {!!}
div-Fibonacci-add-ℕ d m (succ-ℕ n) H1 H2 = {!!}
```

### If `m | n`, then `d | F(m)` implies `d | F(n)`

```agda
div-Fibonacci-div-ℕ :
  (d m n : ℕ) → div-ℕ m n → div-ℕ d (Fibonacci-ℕ m) → div-ℕ d (Fibonacci-ℕ n)
div-Fibonacci-div-ℕ d m .zero-ℕ (zero-ℕ , refl) H = {!!}
div-Fibonacci-div-ℕ d zero-ℕ .(k *ℕ zero-ℕ) (succ-ℕ k , refl) H = {!!}
div-Fibonacci-div-ℕ d (succ-ℕ m) ._ (succ-ℕ k , refl) H = {!!}
```

### Fibonacci-ℕ is an order preserving map on ℕ ordered by divisibility

```agda
preserves-div-Fibonacci-ℕ :
  (m n : ℕ) → div-ℕ m n → div-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ n)
preserves-div-Fibonacci-ℕ m n H = {!!}
```
