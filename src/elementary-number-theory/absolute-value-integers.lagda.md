# The absolute value function on the integers

```agda
module elementary-number-theory.absolute-value-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
```

</details>

## Idea

The absolute value of an integer is the natural number with the same distance
from `0`.

## Definition

```agda
abs-ℤ : ℤ → ℕ
abs-ℤ = {!!}
abs-ℤ (inr (inl star)) = {!!}
abs-ℤ (inr (inr x)) = {!!}

int-abs-ℤ : ℤ → ℤ
int-abs-ℤ = {!!}
```

## Properties

### The absolute value of `int-ℕ n` is `n` itself

```agda
abs-int-ℕ : (n : ℕ) → abs-ℤ (int-ℕ n) ＝ n
abs-int-ℕ = {!!}
abs-int-ℕ (succ-ℕ n) = {!!}
```

### `|-x| ＝ |x|`

```agda
abs-neg-ℤ : (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
abs-neg-ℤ = {!!}
abs-neg-ℤ (inr (inl star)) = {!!}
abs-neg-ℤ (inr (inr x)) = {!!}
```

### If `x` is nonnegative, then `int-abs-ℤ x ＝ x`

```agda
int-abs-is-nonnegative-ℤ : (x : ℤ) → is-nonnegative-ℤ x → int-abs-ℤ x ＝ x
int-abs-is-nonnegative-ℤ = {!!}
int-abs-is-nonnegative-ℤ (inr (inr x)) h = {!!}
```

### `|x| ＝ 0` if and only if `x ＝ 0`

```agda
eq-abs-ℤ : (x : ℤ) → is-zero-ℕ (abs-ℤ x) → is-zero-ℤ x
eq-abs-ℤ = {!!}

abs-eq-ℤ : (x : ℤ) → is-zero-ℤ x → is-zero-ℕ (abs-ℤ x)
abs-eq-ℤ = {!!}
```

### `|x - 1| ≤ |x| + 1`

```agda
predecessor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (pred-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
predecessor-law-abs-ℤ = {!!}
predecessor-law-abs-ℤ (inr (inl star)) = {!!}
predecessor-law-abs-ℤ (inr (inr zero-ℕ)) = {!!}
predecessor-law-abs-ℤ (inr (inr (succ-ℕ x))) = {!!}
```

### `|x + 1| ≤ |x| + 1`

```agda
successor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (succ-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
successor-law-abs-ℤ = {!!}
successor-law-abs-ℤ (inl (succ-ℕ x)) = {!!}
successor-law-abs-ℤ (inr (inl star)) = {!!}
successor-law-abs-ℤ (inr (inr x)) = {!!}
```

### The absolute value function is subadditive

```agda
subadditive-abs-ℤ :
  (x y : ℤ) → (abs-ℤ (x +ℤ y)) ≤-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))
subadditive-abs-ℤ = {!!}
subadditive-abs-ℤ x (inl (succ-ℕ y)) = {!!}
subadditive-abs-ℤ x (inr (inl star)) = {!!}
subadditive-abs-ℤ x (inr (inr zero-ℕ)) = {!!}
subadditive-abs-ℤ x (inr (inr (succ-ℕ y))) = {!!}
```

### `|-x| ＝ |x|`

```agda
negative-law-abs-ℤ :
  (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
negative-law-abs-ℤ = {!!}
negative-law-abs-ℤ (inr (inl star)) = {!!}
negative-law-abs-ℤ (inr (inr x)) = {!!}
```

### If `x` is positive then `|x|` is positive

```agda
is-positive-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-positive-ℤ (int-abs-ℤ x)
is-positive-abs-ℤ = {!!}
```

### If `x` is nonzero then `|x|` is nonzero

```agda
is-nonzero-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-nonzero-ℕ (abs-ℤ x)
is-nonzero-abs-ℤ = {!!}
```

### The absolute value function is multiplicative

```agda
multiplicative-abs-ℤ' :
  (x y : ℤ) → abs-ℤ (explicit-mul-ℤ x y) ＝ (abs-ℤ x) *ℕ (abs-ℤ y)
multiplicative-abs-ℤ' = {!!}
multiplicative-abs-ℤ' (inl x) (inr (inl star)) = {!!}
multiplicative-abs-ℤ' (inl x) (inr (inr y)) = {!!}
multiplicative-abs-ℤ' (inr (inl star)) (inl y) = {!!}
multiplicative-abs-ℤ' (inr (inr x)) (inl y) = {!!}
multiplicative-abs-ℤ' (inr (inl star)) (inr (inl star)) = {!!}
multiplicative-abs-ℤ' (inr (inl star)) (inr (inr x)) = {!!}
multiplicative-abs-ℤ' (inr (inr x)) (inr (inl star)) = {!!}
multiplicative-abs-ℤ' (inr (inr x)) (inr (inr y)) = {!!}

multiplicative-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ (abs-ℤ x) *ℕ (abs-ℤ y)
multiplicative-abs-ℤ = {!!}
```

### `|(-x)y| ＝ |xy|`

```agda
left-negative-law-mul-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ ((neg-ℤ x) *ℤ y)
left-negative-law-mul-abs-ℤ = {!!}
```

### `|x(-y)| ＝ |xy|`

```agda
right-negative-law-mul-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ (x *ℤ (neg-ℤ y))
right-negative-law-mul-abs-ℤ = {!!}
```

### `|(-x)(-y)| ＝ |xy|`

```agda
double-negative-law-mul-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ ((neg-ℤ x) *ℤ (neg-ℤ y))
double-negative-law-mul-abs-ℤ = {!!}
```
