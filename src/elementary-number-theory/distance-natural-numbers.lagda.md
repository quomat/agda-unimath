# The distance between natural numbers

```agda
module elementary-number-theory.distance-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The distance function between natural numbers measures how far two natural
numbers are apart. In the agda-unimath library we often prefer to work with
`dist-ℕ` over the partially defined subtraction operation.

## Definition

```agda
dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ n = {!!}
dist-ℕ (succ-ℕ m) zero-ℕ = {!!}
dist-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}

dist-ℕ' : ℕ → ℕ → ℕ
dist-ℕ' m n = {!!}

ap-dist-ℕ :
  {m n m' n' : ℕ} → m ＝ m' → n ＝ n' → dist-ℕ m n ＝ dist-ℕ m' n'
ap-dist-ℕ p q = {!!}
```

## Properties

### Two natural numbers are equal if and only if their distance is zero

```agda
eq-dist-ℕ : (m n : ℕ) → is-zero-ℕ (dist-ℕ m n) → m ＝ n
eq-dist-ℕ zero-ℕ zero-ℕ p = {!!}
eq-dist-ℕ (succ-ℕ m) (succ-ℕ n) p = {!!}

dist-eq-ℕ' : (n : ℕ) → is-zero-ℕ (dist-ℕ n n)
dist-eq-ℕ' zero-ℕ = {!!}
dist-eq-ℕ' (succ-ℕ n) = {!!}

dist-eq-ℕ : (m n : ℕ) → m ＝ n → is-zero-ℕ (dist-ℕ m n)
dist-eq-ℕ m .m refl = {!!}

is-one-dist-succ-ℕ : (x : ℕ) → is-one-ℕ (dist-ℕ x (succ-ℕ x))
is-one-dist-succ-ℕ zero-ℕ = {!!}
is-one-dist-succ-ℕ (succ-ℕ x) = {!!}

is-one-dist-succ-ℕ' : (x : ℕ) → is-one-ℕ (dist-ℕ (succ-ℕ x) x)
is-one-dist-succ-ℕ' zero-ℕ = {!!}
is-one-dist-succ-ℕ' (succ-ℕ x) = {!!}
```

### The distance function is symmetric

```agda
symmetric-dist-ℕ :
  (m n : ℕ) → dist-ℕ m n ＝ dist-ℕ n m
symmetric-dist-ℕ zero-ℕ zero-ℕ = {!!}
symmetric-dist-ℕ zero-ℕ (succ-ℕ n) = {!!}
symmetric-dist-ℕ (succ-ℕ m) zero-ℕ = {!!}
symmetric-dist-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}
```

### The distance from zero

```agda
left-unit-law-dist-ℕ :
  (n : ℕ) → dist-ℕ zero-ℕ n ＝ n
left-unit-law-dist-ℕ zero-ℕ = {!!}
left-unit-law-dist-ℕ (succ-ℕ n) = {!!}

right-unit-law-dist-ℕ :
  (n : ℕ) → dist-ℕ n zero-ℕ ＝ n
right-unit-law-dist-ℕ zero-ℕ = {!!}
right-unit-law-dist-ℕ (succ-ℕ n) = {!!}
```

## The triangle inequality

```agda
triangle-inequality-dist-ℕ :
  (m n k : ℕ) → (dist-ℕ m n) ≤-ℕ ((dist-ℕ m k) +ℕ (dist-ℕ k n))
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = {!!}
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = {!!}
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = {!!}
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) = {!!}
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = {!!}
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) = {!!}
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = {!!}
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) = {!!}
```

### `dist-ℕ x y` is a solution in `z` to `x + z ＝ y`

```agda
is-additive-right-inverse-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → x +ℕ (dist-ℕ x y) ＝ y
is-additive-right-inverse-dist-ℕ zero-ℕ zero-ℕ H = {!!}
is-additive-right-inverse-dist-ℕ zero-ℕ (succ-ℕ y) star = {!!}
is-additive-right-inverse-dist-ℕ (succ-ℕ x) (succ-ℕ y) H = {!!}

rewrite-left-add-dist-ℕ :
  (x y z : ℕ) → x +ℕ y ＝ z → x ＝ dist-ℕ y z
rewrite-left-add-dist-ℕ zero-ℕ zero-ℕ .zero-ℕ refl = {!!}
rewrite-left-add-dist-ℕ zero-ℕ (succ-ℕ y) .(succ-ℕ (zero-ℕ +ℕ y)) refl = {!!}
rewrite-left-add-dist-ℕ (succ-ℕ x) zero-ℕ .(succ-ℕ x) refl = {!!}
rewrite-left-add-dist-ℕ (succ-ℕ x) (succ-ℕ y) ._ refl = {!!}

rewrite-left-dist-add-ℕ :
  (x y z : ℕ) → y ≤-ℕ z → x ＝ dist-ℕ y z → x +ℕ y ＝ z
rewrite-left-dist-add-ℕ .(dist-ℕ y z) y z H refl = {!!}

rewrite-right-add-dist-ℕ :
  (x y z : ℕ) → x +ℕ y ＝ z → y ＝ dist-ℕ x z
rewrite-right-add-dist-ℕ x y z p = {!!}

rewrite-right-dist-add-ℕ :
  (x y z : ℕ) → x ≤-ℕ z → y ＝ dist-ℕ x z → x +ℕ y ＝ z
rewrite-right-dist-add-ℕ x .(dist-ℕ x z) z H refl = {!!}

is-difference-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → x +ℕ (dist-ℕ x y) ＝ y
is-difference-dist-ℕ zero-ℕ zero-ℕ H = {!!}
is-difference-dist-ℕ zero-ℕ (succ-ℕ y) H = {!!}
is-difference-dist-ℕ (succ-ℕ x) (succ-ℕ y) H = {!!}

is-difference-dist-ℕ' :
  (x y : ℕ) → x ≤-ℕ y → (dist-ℕ x y) +ℕ x ＝ y
is-difference-dist-ℕ' x y H = {!!}
```

### The distance from `n` to `n + m` is `m`

```agda
dist-add-ℕ : (x y : ℕ) → dist-ℕ x (x +ℕ y) ＝ y
dist-add-ℕ x y = {!!}

dist-add-ℕ' : (x y : ℕ) → dist-ℕ (x +ℕ y) x ＝ y
dist-add-ℕ' x y = {!!}
```

### If three elements are ordered linearly, then their distances add up

```agda
triangle-equality-dist-ℕ :
  (x y z : ℕ) → (x ≤-ℕ y) → (y ≤-ℕ z) →
  (dist-ℕ x y) +ℕ (dist-ℕ y z) ＝ dist-ℕ x z
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = {!!}
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star = {!!}
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 = {!!}
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 = {!!}

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = {!!}

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) = {!!}
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = {!!}
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) = {!!}
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) = {!!}
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) = {!!}
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) = {!!}
```

### If `x ≤ y` then the distance between `x` and `y` is less than `y`

```agda
leq-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → dist-ℕ x y ≤-ℕ y
leq-dist-ℕ zero-ℕ zero-ℕ H = {!!}
leq-dist-ℕ zero-ℕ (succ-ℕ y) H = {!!}
leq-dist-ℕ (succ-ℕ x) (succ-ℕ y) H = {!!}
```

### If `x < b` and `y < b`, then `dist-ℕ x y < b`

```agda
strict-upper-bound-dist-ℕ :
  (b x y : ℕ) → le-ℕ x b → le-ℕ y b → le-ℕ (dist-ℕ x y) b
strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = {!!}
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = {!!}
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K = {!!}
```

### If `x < y` then `dist-ℕ x (succ-ℕ y) = {!!}

```agda
right-successor-law-dist-ℕ :
  (x y : ℕ) → leq-ℕ x y → dist-ℕ x (succ-ℕ y) ＝ succ-ℕ (dist-ℕ x y)
right-successor-law-dist-ℕ zero-ℕ zero-ℕ star = {!!}
right-successor-law-dist-ℕ zero-ℕ (succ-ℕ y) star = {!!}
right-successor-law-dist-ℕ (succ-ℕ x) (succ-ℕ y) H = {!!}

left-successor-law-dist-ℕ :
  (x y : ℕ) → leq-ℕ y x → dist-ℕ (succ-ℕ x) y ＝ succ-ℕ (dist-ℕ x y)
left-successor-law-dist-ℕ zero-ℕ zero-ℕ star = {!!}
left-successor-law-dist-ℕ (succ-ℕ x) zero-ℕ star = {!!}
left-successor-law-dist-ℕ (succ-ℕ x) (succ-ℕ y) H = {!!}
```

### `dist-ℕ` is translation invariant

```agda
translation-invariant-dist-ℕ :
  (k m n : ℕ) → dist-ℕ (k +ℕ m) (k +ℕ n) ＝ dist-ℕ m n
translation-invariant-dist-ℕ zero-ℕ m n = {!!}
translation-invariant-dist-ℕ (succ-ℕ k) m n = {!!}

translation-invariant-dist-ℕ' :
  (k m n : ℕ) → dist-ℕ (m +ℕ k) (n +ℕ k) ＝ dist-ℕ m n
translation-invariant-dist-ℕ' k m n = {!!}
```

### `dist-ℕ` is linear with respect to scalar multiplication

```agda
left-distributive-mul-dist-ℕ :
  (m n k : ℕ) → k *ℕ (dist-ℕ m n) ＝ dist-ℕ (k *ℕ m) (k *ℕ n)
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = {!!}
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = {!!}
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = {!!}
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) = {!!}
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = {!!}
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) = {!!}
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = {!!}
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) = {!!}

right-distributive-mul-dist-ℕ :
  (x y k : ℕ) → (dist-ℕ x y) *ℕ k ＝ dist-ℕ (x *ℕ k) (y *ℕ k)
right-distributive-mul-dist-ℕ x y k = {!!}
```
