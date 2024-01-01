# The greatest common divisor of integers

```agda
module elementary-number-theory.greatest-common-divisor-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Definition

### The predicate `is-gcd-ℤ`

```agda
is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ x y d = {!!}

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d = {!!}
```

### The greatest common divisor of two integers

```agda
nat-gcd-ℤ : ℤ → ℤ → ℕ
nat-gcd-ℤ x y = {!!}

gcd-ℤ : ℤ → ℤ → ℤ
gcd-ℤ x y = {!!}
```

## Properties

### A natural number `d` is a common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a common divisor of `int-ℕ x` and `ind-ℕ y`

```agda
is-common-divisor-int-is-common-divisor-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℕ x y d → is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
is-common-divisor-int-is-common-divisor-ℕ = {!!}

is-common-divisor-is-common-divisor-int-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-common-divisor-ℕ x y d
is-common-divisor-is-common-divisor-int-ℕ {x} {y} {d} = {!!}
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a common divisor of `x` and `y` if and only if `d` is a common divisor of `x'` and `y'`

```agda
is-common-divisor-sim-unit-ℤ :
  {x x' y y' d d' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' → sim-unit-ℤ d d' →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x' y' d'
is-common-divisor-sim-unit-ℤ H K L = {!!}
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a greatest common divisor of `x` and `y` if and only if `c` is a greatest common divisor of `x'` and `y'`

```agda
is-gcd-sim-unit-ℤ :
  {x x' y y' d : ℤ} →
  sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  is-gcd-ℤ x y d → is-gcd-ℤ x' y' d
pr1 (is-gcd-sim-unit-ℤ H K (pair x _)) = {!!}
pr1 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) = {!!}
pr2 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) = {!!}
```

### An integer `d` is a common divisor of `x` and `y` if and only if `|d|` is a common divisor of `x` and `y`

```agda
is-common-divisor-int-abs-is-common-divisor-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x y (int-abs-ℤ d)
is-common-divisor-int-abs-is-common-divisor-ℤ = {!!}

is-common-divisor-is-common-divisor-int-abs-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y (int-abs-ℤ d) → is-common-divisor-ℤ x y d
is-common-divisor-is-common-divisor-int-abs-ℤ = {!!}

is-common-divisor-is-gcd-ℤ :
  (a b d : ℤ) → is-gcd-ℤ a b d → is-common-divisor-ℤ a b d
is-common-divisor-is-gcd-ℤ a b d H = {!!}
```

### A natural number `d` is a greatest common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a greatest common divisor of `int-ℕ x` and `int-ℕ y`

```agda
is-gcd-int-is-gcd-ℕ :
  {x y d : ℕ} → is-gcd-ℕ x y d → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
pr1 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) = {!!}
pr1 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) = {!!}
pr2 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) = {!!}

is-gcd-is-gcd-int-ℕ :
  {x y d : ℕ} → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-gcd-ℕ x y d
pr1 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) = {!!}
pr2 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) = {!!}
```

### `gcd-ℤ x y` is a greatest common divisor of `x` and `y`

```agda
is-nonnegative-gcd-ℤ : (x y : ℤ) → is-nonnegative-ℤ (gcd-ℤ x y)
is-nonnegative-gcd-ℤ x y = {!!}

gcd-nonnegative-ℤ : ℤ → ℤ → nonnegative-ℤ
pr1 (gcd-nonnegative-ℤ x y) = {!!}
pr2 (gcd-nonnegative-ℤ x y) = {!!}

is-gcd-gcd-ℤ : (x y : ℤ) → is-gcd-ℤ x y (gcd-ℤ x y)
pr1 (is-gcd-gcd-ℤ x y) = {!!}
pr1 (pr2 (is-gcd-gcd-ℤ x y) k) = {!!}
pr2 (pr2 (is-gcd-gcd-ℤ x y) k) = {!!}
```

### The gcd in `ℕ` of `x` and `y` is equal to the gcd in `ℤ` of `int-ℕ x` and `int-ℕ y`

```agda
eq-gcd-gcd-int-ℕ :
  (x y : ℕ) → gcd-ℤ (int-ℕ x) (int-ℕ y) ＝ int-ℕ (gcd-ℕ x y)
eq-gcd-gcd-int-ℕ x y = {!!}
```

### The gcd of `x` and `y` divides both `x` and `y`

```agda
is-common-divisor-gcd-ℤ :
  (x y : ℤ) → is-common-divisor-ℤ x y (gcd-ℤ x y)
is-common-divisor-gcd-ℤ x y = {!!}

div-left-gcd-ℤ : (x y : ℤ) → div-ℤ (gcd-ℤ x y) x
div-left-gcd-ℤ x y = {!!}

div-right-gcd-ℤ : (x y : ℤ) → div-ℤ (gcd-ℤ x y) y
div-right-gcd-ℤ x y = {!!}
```

### Any common divisor of `x` and `y` divides the greatest common divisor

```agda
div-gcd-is-common-divisor-ℤ :
  (x y k : ℤ) → is-common-divisor-ℤ x y k → div-ℤ k (gcd-ℤ x y)
div-gcd-is-common-divisor-ℤ x y k H = {!!}
```

### If either `x` or `y` is a positive integer, then `gcd-ℤ x y` is positive

```agda
is-positive-gcd-is-positive-left-ℤ :
  (x y : ℤ) → is-positive-ℤ x → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-left-ℤ x y H = {!!}

is-positive-gcd-is-positive-right-ℤ :
  (x y : ℤ) → is-positive-ℤ y → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-right-ℤ x y H = {!!}

is-positive-gcd-ℤ :
  (x y : ℤ) → (is-positive-ℤ x) + (is-positive-ℤ y) →
  is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-ℤ x y (inl H) = {!!}
is-positive-gcd-ℤ x y (inr H) = {!!}
```

### `gcd-ℤ a b` is zero if and only if both `a` and `b` are zero

```agda
is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ a → is-zero-ℤ b → is-zero-ℤ (gcd-ℤ a b)
is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl = {!!}

is-zero-left-is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ (gcd-ℤ a b) → is-zero-ℤ a
is-zero-left-is-zero-gcd-ℤ a b = {!!}

is-zero-right-is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ (gcd-ℤ a b) → is-zero-ℤ b
is-zero-right-is-zero-gcd-ℤ a b = {!!}
```

### `gcd-ℤ` is commutative

```agda
is-commutative-gcd-ℤ : (x y : ℤ) → gcd-ℤ x y ＝ gcd-ℤ y x
is-commutative-gcd-ℤ x y = {!!}
```

### `gcd-ℕ 1 b ＝ 1`

```agda
is-one-is-gcd-one-ℤ : {b x : ℤ} → is-gcd-ℤ one-ℤ b x → is-one-ℤ x
is-one-is-gcd-one-ℤ {b} {x} H with
  ( is-one-or-neg-one-is-unit-ℤ x
    ( pr1 (is-common-divisor-is-gcd-ℤ one-ℤ b x H)))
... | inl p = {!!}
... | inr p = {!!}

is-one-gcd-one-ℤ : (b : ℤ) → is-one-ℤ (gcd-ℤ one-ℤ b)
is-one-gcd-one-ℤ b = {!!}
```

### `gcd-ℤ a 1 ＝ 1`

```agda
is-one-is-gcd-one-ℤ' : {a x : ℤ} → is-gcd-ℤ a one-ℤ x → is-one-ℤ x
is-one-is-gcd-one-ℤ' {a} {x} H with
  ( is-one-or-neg-one-is-unit-ℤ x
    ( pr2 (is-common-divisor-is-gcd-ℤ a one-ℤ x H)))
... | inl p = {!!}
... | inr p = {!!}

is-one-gcd-one-ℤ' : (a : ℤ) → is-one-ℤ (gcd-ℤ a one-ℤ)
is-one-gcd-one-ℤ' a = {!!}
```

### `gcd-ℤ 0 b ＝ abs-ℤ b`

```agda
is-sim-id-is-gcd-zero-ℤ : {b x : ℤ} → gcd-ℤ zero-ℤ b ＝ x → sim-unit-ℤ x b
is-sim-id-is-gcd-zero-ℤ {b} {x} H = {!!}

is-id-is-gcd-zero-ℤ : {b x : ℤ} → gcd-ℤ zero-ℤ b ＝ x → x ＝ int-ℕ (abs-ℤ b)
is-id-is-gcd-zero-ℤ {inl b} {x} H
  with (is-plus-or-minus-sim-unit-ℤ (is-sim-id-is-gcd-zero-ℤ {inl b} {x} H))
... | inl p = {!!}
... | inr p = {!!}
is-id-is-gcd-zero-ℤ {inr (inl star)} {x} H = {!!}
is-id-is-gcd-zero-ℤ {inr (inr b)} {x} H
  with
  is-plus-or-minus-sim-unit-ℤ (is-sim-id-is-gcd-zero-ℤ {inr (inr b)} {x} H)
... | inl p = {!!}
... | inr p = {!!}
```

### `gcd-ℤ a 0 ＝ abs-ℤ a`

```agda
is-sim-id-is-gcd-zero-ℤ' : {a x : ℤ} → gcd-ℤ a zero-ℤ ＝ x → sim-unit-ℤ x a
is-sim-id-is-gcd-zero-ℤ' {a} {x} H = {!!}

is-id-is-gcd-zero-ℤ' : {a x : ℤ} → gcd-ℤ a zero-ℤ ＝ x → x ＝ int-ℕ (abs-ℤ a)
is-id-is-gcd-zero-ℤ' {a} {x} H = {!!}
```
