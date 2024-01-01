# Multiplication of integers

```agda
module elementary-number-theory.multiplication-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Definitions

### The standard definition of multiplication on ℤ

```agda
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = {!!}
mul-ℤ (inl (succ-ℕ x)) l = {!!}
mul-ℤ (inr (inl star)) l = {!!}
mul-ℤ (inr (inr zero-ℕ)) l = {!!}
mul-ℤ (inr (inr (succ-ℕ x))) l = {!!}

infixl 40 _*ℤ_
_*ℤ_ = {!!}

mul-ℤ' : ℤ → ℤ → ℤ
mul-ℤ' x y = {!!}

ap-mul-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → x *ℤ y ＝ x' *ℤ y'
ap-mul-ℤ p q = {!!}
```

### A definition of multiplication that connects with multiplication on ℕ

```agda
explicit-mul-ℤ : ℤ → ℤ → ℤ
explicit-mul-ℤ (inl x) (inl y) = {!!}
explicit-mul-ℤ (inl x) (inr (inl star)) = {!!}
explicit-mul-ℤ (inl x) (inr (inr y)) = {!!}
explicit-mul-ℤ (inr (inl star)) (inl y) = {!!}
explicit-mul-ℤ (inr (inr x)) (inl y) = {!!}
explicit-mul-ℤ (inr (inl star)) (inr (inl star)) = {!!}
explicit-mul-ℤ (inr (inl star)) (inr (inr y)) = {!!}
explicit-mul-ℤ (inr (inr x)) (inr (inl star)) = {!!}
explicit-mul-ℤ (inr (inr x)) (inr (inr y)) = {!!}

explicit-mul-ℤ' : ℤ → ℤ → ℤ
explicit-mul-ℤ' x y = {!!}
```

### A definition of being equal up to sign

```agda
is-plus-or-minus-ℤ : ℤ → ℤ → UU lzero
is-plus-or-minus-ℤ x y = {!!}
```

## Properties

### Laws for multiplication on ℤ

```agda
left-zero-law-mul-ℤ : (k : ℤ) → zero-ℤ *ℤ k ＝ zero-ℤ
left-zero-law-mul-ℤ k = {!!}

right-zero-law-mul-ℤ : (k : ℤ) → k *ℤ zero-ℤ ＝ zero-ℤ
right-zero-law-mul-ℤ (inl zero-ℕ) = {!!}
right-zero-law-mul-ℤ (inl (succ-ℕ n)) = {!!}
right-zero-law-mul-ℤ (inr (inl star)) = {!!}
right-zero-law-mul-ℤ (inr (inr zero-ℕ)) = {!!}
right-zero-law-mul-ℤ (inr (inr (succ-ℕ n))) = {!!}

left-unit-law-mul-ℤ : (k : ℤ) → one-ℤ *ℤ k ＝ k
left-unit-law-mul-ℤ k = {!!}

right-unit-law-mul-ℤ : (k : ℤ) → k *ℤ one-ℤ ＝ k
right-unit-law-mul-ℤ (inl zero-ℕ) = {!!}
right-unit-law-mul-ℤ (inl (succ-ℕ n)) = {!!}
right-unit-law-mul-ℤ (inr (inl star)) = {!!}
right-unit-law-mul-ℤ (inr (inr zero-ℕ)) = {!!}
right-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) = {!!}

left-neg-unit-law-mul-ℤ : (k : ℤ) → neg-one-ℤ *ℤ k ＝ neg-ℤ k
left-neg-unit-law-mul-ℤ k = {!!}

right-neg-unit-law-mul-ℤ : (k : ℤ) → k *ℤ neg-one-ℤ ＝ neg-ℤ k
right-neg-unit-law-mul-ℤ (inl zero-ℕ) = {!!}
right-neg-unit-law-mul-ℤ (inl (succ-ℕ n)) = {!!}
right-neg-unit-law-mul-ℤ (inr (inl star)) = {!!}
right-neg-unit-law-mul-ℤ (inr (inr zero-ℕ)) = {!!}
right-neg-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) = {!!}

left-successor-law-mul-ℤ :
  (k l : ℤ) → (succ-ℤ k) *ℤ l ＝ l +ℤ (k *ℤ l)
left-successor-law-mul-ℤ (inl zero-ℕ) l = {!!}
left-successor-law-mul-ℤ (inl (succ-ℕ n)) l = {!!}
left-successor-law-mul-ℤ (inr (inl star)) l = {!!}
left-successor-law-mul-ℤ (inr (inr n)) l = {!!}

left-predecessor-law-mul-ℤ :
  (k l : ℤ) → (pred-ℤ k) *ℤ l ＝ (neg-ℤ l) +ℤ (k *ℤ l)
left-predecessor-law-mul-ℤ (inl n) l = {!!}
left-predecessor-law-mul-ℤ (inr (inl star)) l = {!!}
left-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = {!!}
left-predecessor-law-mul-ℤ (inr (inr (succ-ℕ x))) l = {!!}

right-successor-law-mul-ℤ :
  (k l : ℤ) → k *ℤ (succ-ℤ l) ＝ k +ℤ (k *ℤ l)
right-successor-law-mul-ℤ (inl zero-ℕ) l = {!!}
right-successor-law-mul-ℤ (inl (succ-ℕ n)) l = {!!}
right-successor-law-mul-ℤ (inr (inl star)) l = {!!}
right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = {!!}
right-successor-law-mul-ℤ (inr (inr (succ-ℕ n))) l = {!!}

right-predecessor-law-mul-ℤ :
  (k l : ℤ) → k *ℤ (pred-ℤ l) ＝ (neg-ℤ k) +ℤ (k *ℤ l)
right-predecessor-law-mul-ℤ (inl zero-ℕ) l = {!!}
right-predecessor-law-mul-ℤ (inl (succ-ℕ n)) l = {!!}
right-predecessor-law-mul-ℤ (inr (inl star)) l = {!!}
right-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = {!!}
right-predecessor-law-mul-ℤ (inr (inr (succ-ℕ n))) l = {!!}

right-distributive-mul-add-ℤ :
  (k l m : ℤ) → (k +ℤ l) *ℤ m ＝ (k *ℤ m) +ℤ (l *ℤ m)
right-distributive-mul-add-ℤ (inl zero-ℕ) l m = {!!}
right-distributive-mul-add-ℤ (inl (succ-ℕ x)) l m = {!!}
right-distributive-mul-add-ℤ (inr (inl star)) l m = {!!}
right-distributive-mul-add-ℤ (inr (inr zero-ℕ)) l m = {!!}
right-distributive-mul-add-ℤ (inr (inr (succ-ℕ n))) l m = {!!}

left-negative-law-mul-ℤ :
  (k l : ℤ) → (neg-ℤ k) *ℤ l ＝ neg-ℤ (k *ℤ l)
left-negative-law-mul-ℤ (inl zero-ℕ) l = {!!}
left-negative-law-mul-ℤ (inl (succ-ℕ n)) l = {!!}
left-negative-law-mul-ℤ (inr (inl star)) l = {!!}
left-negative-law-mul-ℤ (inr (inr zero-ℕ)) l = {!!}
left-negative-law-mul-ℤ (inr (inr (succ-ℕ n))) l = {!!}

associative-mul-ℤ :
  (k l m : ℤ) → (k *ℤ l) *ℤ m ＝ k *ℤ (l *ℤ m)
associative-mul-ℤ (inl zero-ℕ) l m = {!!}
associative-mul-ℤ (inl (succ-ℕ n)) l m = {!!}
associative-mul-ℤ (inr (inl star)) l m = {!!}
associative-mul-ℤ (inr (inr zero-ℕ)) l m = {!!}
associative-mul-ℤ (inr (inr (succ-ℕ n))) l m = {!!}

commutative-mul-ℤ :
  (k l : ℤ) → k *ℤ l ＝ l *ℤ k
commutative-mul-ℤ (inl zero-ℕ) l = {!!}
commutative-mul-ℤ (inl (succ-ℕ n)) l = {!!}
commutative-mul-ℤ (inr (inl star)) l = {!!}
commutative-mul-ℤ (inr (inr zero-ℕ)) l = {!!}
commutative-mul-ℤ (inr (inr (succ-ℕ n))) l = {!!}

left-distributive-mul-add-ℤ :
  (m k l : ℤ) → m *ℤ (k +ℤ l) ＝ (m *ℤ k) +ℤ (m *ℤ l)
left-distributive-mul-add-ℤ m k l = {!!}

right-negative-law-mul-ℤ :
  (k l : ℤ) → k *ℤ (neg-ℤ l) ＝ neg-ℤ (k *ℤ l)
right-negative-law-mul-ℤ k l = {!!}

interchange-law-mul-mul-ℤ : interchange-law mul-ℤ mul-ℤ
interchange-law-mul-mul-ℤ = {!!}

is-left-mul-neg-one-neg-ℤ : (x : ℤ) → neg-ℤ x ＝ neg-one-ℤ *ℤ x
is-left-mul-neg-one-neg-ℤ x = {!!}

is-right-mul-neg-one-neg-ℤ : (x : ℤ) → neg-ℤ x ＝ x *ℤ neg-one-ℤ
is-right-mul-neg-one-neg-ℤ x = {!!}

double-negative-law-mul-ℤ : (k l : ℤ) → (neg-ℤ k) *ℤ (neg-ℤ l) ＝ k *ℤ l
double-negative-law-mul-ℤ k l = {!!}
```

### Positivity of multiplication

```agda
is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x *ℤ y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = {!!}
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K = {!!}
```

### Computing multiplication of integers that come from natural numbers

```agda
mul-int-ℕ : (x y : ℕ) → (int-ℕ x) *ℤ (int-ℕ y) ＝ int-ℕ (x *ℕ y)
mul-int-ℕ zero-ℕ y = {!!}
mul-int-ℕ (succ-ℕ x) y = {!!}

compute-mul-ℤ : (x y : ℤ) → x *ℤ y ＝ explicit-mul-ℤ x y
compute-mul-ℤ (inl zero-ℕ) (inl y) = {!!}
compute-mul-ℤ (inl (succ-ℕ x)) (inl y) = {!!}
compute-mul-ℤ (inl zero-ℕ) (inr (inl star)) = {!!}
compute-mul-ℤ (inl zero-ℕ) (inr (inr x)) = {!!}
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inl star)) = {!!}
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inr y)) = {!!}
compute-mul-ℤ (inr (inl star)) (inl y) = {!!}
compute-mul-ℤ (inr (inr zero-ℕ)) (inl y) = {!!}
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inl y) = {!!}
compute-mul-ℤ (inr (inl star)) (inr (inl star)) = {!!}
compute-mul-ℤ (inr (inl star)) (inr (inr y)) = {!!}
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inl star)) = {!!}
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inl star)) = {!!}
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inr y)) = {!!}
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inr y)) = {!!}
```

### Linearity of the difference

```agda
linear-diff-left-mul-ℤ :
  (z x y : ℤ) → (z *ℤ x) -ℤ (z *ℤ y) ＝ z *ℤ (x -ℤ y)
linear-diff-left-mul-ℤ z x y = {!!}

linear-diff-right-mul-ℤ :
  (x y z : ℤ) → (x *ℤ z) -ℤ (y *ℤ z) ＝ (x -ℤ y) *ℤ z
linear-diff-right-mul-ℤ x y z = {!!}
```

```agda
is-zero-is-zero-mul-ℤ :
  (x y : ℤ) → is-zero-ℤ (x *ℤ y) → (is-zero-ℤ x) + (is-zero-ℤ y)
is-zero-is-zero-mul-ℤ (inl x) (inl y) H = {!!}
is-zero-is-zero-mul-ℤ (inl x) (inr (inl star)) H = {!!}
is-zero-is-zero-mul-ℤ (inl x) (inr (inr y)) H = {!!}
is-zero-is-zero-mul-ℤ (inr (inl star)) y H = {!!}
is-zero-is-zero-mul-ℤ (inr (inr x)) (inl y) H = {!!}
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inl star)) H = {!!}
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inr y)) H = {!!}
```

### Injectivity of multiplication

```agda
is-injective-left-mul-ℤ :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (x *ℤ_)
is-injective-left-mul-ℤ x f {y} {z} p = {!!}

is-injective-right-mul-ℤ :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (_*ℤ x)
is-injective-right-mul-ℤ x f {y} {z} p = {!!}
```

### Multiplication by a nonzero integer is an embedding

```agda
is-emb-left-mul-ℤ : (x : ℤ) → is-nonzero-ℤ x → is-emb (x *ℤ_)
is-emb-left-mul-ℤ x f = {!!}

is-emb-right-mul-ℤ : (x : ℤ) → is-nonzero-ℤ x → is-emb (_*ℤ x)
is-emb-right-mul-ℤ x f = {!!}
```

```agda
is-positive-left-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (x *ℤ y) → is-positive-ℤ y → is-positive-ℤ x
is-positive-left-factor-mul-ℤ {inl x} {inr (inr y)} H K = {!!}
is-positive-left-factor-mul-ℤ {inr (inl star)} {inr (inr y)} H K = {!!}
is-positive-left-factor-mul-ℤ {inr (inr x)} {inr (inr y)} H K = {!!}

is-positive-right-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (x *ℤ y) → is-positive-ℤ x → is-positive-ℤ y
is-positive-right-factor-mul-ℤ {x} {y} H = {!!}
```

### Lemmas about nonnegative integers

```agda
is-nonnegative-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ y →
  is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-ℤ {inr (inl star)} {y} H K = {!!}
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inl star)} H K = {!!}
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inr y)} H K = {!!}

is-nonnegative-left-factor-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ y → is-nonnegative-ℤ x
is-nonnegative-left-factor-mul-ℤ {inl x} {inr (inr y)} H K = {!!}
is-nonnegative-left-factor-mul-ℤ {inr x} {inr y} H K = {!!}

is-nonnegative-right-factor-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ x → is-nonnegative-ℤ y
is-nonnegative-right-factor-mul-ℤ {x} {y} H = {!!}
```

```agda
preserves-leq-left-mul-ℤ :
  (x y z : ℤ) → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (z *ℤ x) (z *ℤ y)
preserves-leq-left-mul-ℤ x y (inr (inl star)) star K = {!!}
preserves-leq-left-mul-ℤ x y (inr (inr zero-ℕ)) star K = {!!}
preserves-leq-left-mul-ℤ x y (inr (inr (succ-ℕ n))) star K = {!!}

preserves-leq-right-mul-ℤ :
  (x y z : ℤ) → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (x *ℤ z) (y *ℤ z)
preserves-leq-right-mul-ℤ x y z H K = {!!}
```
