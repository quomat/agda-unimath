# The natural numbers base `k`

```agda
module elementary-number-theory.finitary-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

### The finitary natural numbers

```agda
data based-ℕ : ℕ → UU lzero where
  constant-based-ℕ : (k : ℕ) → Fin k → based-ℕ k
  unary-op-based-ℕ : (k : ℕ) → Fin k → based-ℕ k → based-ℕ k
```

### Converting a `k`-ary natural number to a natural number

```agda
constant-ℕ : (k : ℕ) → Fin k → ℕ
constant-ℕ k x = {!!}

unary-op-ℕ : (k : ℕ) → Fin k → ℕ → ℕ
unary-op-ℕ k x n = {!!}

convert-based-ℕ : (k : ℕ) → based-ℕ k → ℕ
convert-based-ℕ k (constant-based-ℕ .k x) = {!!}
convert-based-ℕ k (unary-op-based-ℕ .k x n) = {!!}
```

### The type of `0`-ary natural numbers is empty

```agda
is-empty-based-zero-ℕ : is-empty (based-ℕ zero-ℕ)
is-empty-based-zero-ℕ (constant-based-ℕ .zero-ℕ ())
is-empty-based-zero-ℕ (unary-op-based-ℕ .zero-ℕ () n)
```

### The function `convert-based-ℕ` is injective

```agda
cong-unary-op-ℕ :
  (k : ℕ) (x : Fin k) (n : ℕ) →
  cong-ℕ k (unary-op-ℕ k x n) (nat-Fin k x)
cong-unary-op-ℕ (succ-ℕ k) x n = {!!}
```

### Any natural number of the form `constant-ℕ k x` is strictly less than any natural number of the form `unary-op-ℕ k y m`

```agda
le-constant-unary-op-ℕ :
  (k : ℕ) (x y : Fin k) (m : ℕ) → le-ℕ (constant-ℕ k x) (unary-op-ℕ k y m)
le-constant-unary-op-ℕ k x y m = {!!}

is-injective-convert-based-ℕ :
  (k : ℕ) → is-injective (convert-based-ℕ k)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { constant-based-ℕ .(succ-ℕ k) y} p = {!!}
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p = {!!}
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { constant-based-ℕ .(succ-ℕ k) y} p = {!!}
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p with
  is-injective-nat-Fin (succ-ℕ k) {x} {y}
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) x)
      ( nat-Fin (succ-ℕ k) y)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) x)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) y)
      ( concatenate-cong-eq-cong-ℕ
        { succ-ℕ k}
        { nat-Fin (succ-ℕ k) x}
        { unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)}
        { unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m)}
        { nat-Fin (succ-ℕ k) y}
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n))
          ( nat-Fin (succ-ℕ k) x)
          ( cong-unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)))
        ( p)
        ( cong-unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m))))
... | refl = {!!}
```

### The zero-element of the `k+1`-ary natural numbers

```agda
zero-based-ℕ : (k : ℕ) → based-ℕ (succ-ℕ k)
zero-based-ℕ k = {!!}
```

### The successor function on the `k`-ary natural numbers

```agda
succ-based-ℕ : (k : ℕ) → based-ℕ k → based-ℕ k
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) = {!!}
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr _)) = {!!}
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) = {!!}
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr x) n) = {!!}
```

### The inverse map of `convert-based-ℕ`

```agda
inv-convert-based-ℕ : (k : ℕ) → ℕ → based-ℕ (succ-ℕ k)
inv-convert-based-ℕ k zero-ℕ = {!!}
inv-convert-based-ℕ k (succ-ℕ n) = {!!}

convert-based-succ-based-ℕ :
  (k : ℕ) (x : based-ℕ k) →
  convert-based-ℕ k (succ-based-ℕ k x) ＝ succ-ℕ (convert-based-ℕ k x)
convert-based-succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) = {!!}
convert-based-succ-based-ℕ
  ( succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr _)) = {!!}
convert-based-succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) = {!!}
convert-based-succ-based-ℕ
  (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr _) n) = {!!}

is-section-inv-convert-based-ℕ :
  (k n : ℕ) → convert-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n) ＝ n
is-section-inv-convert-based-ℕ k zero-ℕ = {!!}
is-section-inv-convert-based-ℕ k (succ-ℕ n) = {!!}

is-retraction-inv-convert-based-ℕ :
  (k : ℕ) (x : based-ℕ (succ-ℕ k)) →
  inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x) ＝ x
is-retraction-inv-convert-based-ℕ k x = {!!}
```
