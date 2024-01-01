# Exponentiation of natural numbers

```agda
module elementary-number-theory.exponentiation-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
```

</details>

## Idea

The exponent `m^n` is the number obtained by multiplying `m` with itself `n`
times.

## Definition

```agda
exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ m 0 = {!!}
exp-ℕ m (succ-ℕ n) = {!!}

infixr 45 _^ℕ_
_^ℕ_ = {!!}
```

```agda
power-ℕ : ℕ → ℕ → ℕ
power-ℕ = {!!}
```

## Properties

### Tarski's high school arithmetic laws for exponentiation

```agda
annihilation-law-exp-ℕ : (n : ℕ) → 1 ^ℕ n ＝ 1
annihilation-law-exp-ℕ zero-ℕ = {!!}
annihilation-law-exp-ℕ (succ-ℕ n) = {!!}

left-distributive-exp-add-ℕ :
  (x y z : ℕ) → x ^ℕ (y +ℕ z) ＝ (x ^ℕ y) *ℕ (x ^ℕ z)
left-distributive-exp-add-ℕ = {!!}

right-distributive-exp-mul-ℕ :
  (x y z : ℕ) → (x *ℕ y) ^ℕ z ＝ (x ^ℕ z) *ℕ (y ^ℕ z)
right-distributive-exp-mul-ℕ = {!!}

exp-mul-ℕ : (x y z : ℕ) → x ^ℕ (y *ℕ z) ＝ (x ^ℕ y) ^ℕ z
exp-mul-ℕ x zero-ℕ z = {!!}
exp-mul-ℕ x (succ-ℕ y) z = {!!}
```

### The exponent `m^n` is always nonzero

```agda
is-nonzero-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ m → is-nonzero-ℕ (m ^ℕ n)
is-nonzero-exp-ℕ = {!!}
```
