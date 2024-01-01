# Minimum on the natural numbers

```agda
module elementary-number-theory.minimum-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type

open import order-theory.greatest-lower-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the natural
numbers.

## Definition

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = {!!}
min-ℕ (succ-ℕ m) 0 = {!!}
min-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}

ap-min-ℕ : {x x' y y' : ℕ} → x ＝ x' → y ＝ y' → min-ℕ x y ＝ min-ℕ x' y'
ap-min-ℕ p q = {!!}

min-Fin-ℕ : (n : ℕ) → (Fin (succ-ℕ n) → ℕ) → ℕ
min-Fin-ℕ zero-ℕ f = {!!}
min-Fin-ℕ (succ-ℕ n) f = {!!}
```

## Properties

### The minimum of two natural numbers is a greatest lower bound

```agda
leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ m → k ≤-ℕ n → k ≤-ℕ (min-ℕ m n)
leq-min-ℕ = {!!}

leq-left-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ m
leq-left-leq-min-ℕ = {!!}

leq-right-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ n
leq-right-leq-min-ℕ = {!!}

is-greatest-lower-bound-min-ℕ :
  (l m : ℕ) → is-greatest-binary-lower-bound-Poset ℕ-Poset l m (min-ℕ l m)
is-greatest-lower-bound-min-ℕ = {!!}
```

### Associativity of `min-ℕ`

```agda
associative-min-ℕ :
  (x y z : ℕ) → min-ℕ (min-ℕ x y) z ＝ min-ℕ x (min-ℕ y z)
associative-min-ℕ = {!!}
```

### Zero laws for `min-ℕ`

```agda
left-zero-law-min-ℕ : (x : ℕ) → min-ℕ 0 x ＝ 0
left-zero-law-min-ℕ x = {!!}

right-zero-law-min-ℕ : (x : ℕ) → min-ℕ x 0 ＝ 0
right-zero-law-min-ℕ zero-ℕ = {!!}
right-zero-law-min-ℕ (succ-ℕ x) = {!!}
```

### Commutativity of `min-ℕ`

```agda
commutative-min-ℕ : (x y : ℕ) → min-ℕ x y ＝ min-ℕ y x
commutative-min-ℕ zero-ℕ zero-ℕ = {!!}
commutative-min-ℕ zero-ℕ (succ-ℕ y) = {!!}
commutative-min-ℕ (succ-ℕ x) zero-ℕ = {!!}
commutative-min-ℕ (succ-ℕ x) (succ-ℕ y) = {!!}
```

### `min-ℕ` is idempotent

```agda
idempotent-min-ℕ : (x : ℕ) → min-ℕ x x ＝ x
idempotent-min-ℕ zero-ℕ = {!!}
idempotent-min-ℕ (succ-ℕ x) = {!!}
```

### Addition distributes over `min-ℕ`

```agda
left-distributive-add-min-ℕ :
  (x y z : ℕ) → x +ℕ (min-ℕ y z) ＝ min-ℕ (x +ℕ y) (x +ℕ z)
left-distributive-add-min-ℕ = {!!}

right-distributive-add-min-ℕ :
  (x y z : ℕ) → (min-ℕ x y) +ℕ z ＝ min-ℕ (x +ℕ z) (y +ℕ z)
right-distributive-add-min-ℕ = {!!}
```
