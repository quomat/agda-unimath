# Maximum on the natural numbers

```agda
module elementary-number-theory.maximum-natural-numbers where
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

open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of maximum (least upper bound) for the natural numbers.

## Definition

### Maximum of natural numbers

```agda
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = {!!}
max-ℕ (succ-ℕ m) 0 = {!!}
max-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}

ap-max-ℕ : {x x' y y' : ℕ} → x ＝ x' → y ＝ y' → max-ℕ x y ＝ max-ℕ x' y'
ap-max-ℕ p q = {!!}

max-ℕ' : ℕ → (ℕ → ℕ)
max-ℕ' x y = {!!}
```

### Maximum of elements of standard finite types

```agda
max-Fin-ℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
max-Fin-ℕ zero-ℕ f = {!!}
max-Fin-ℕ (succ-ℕ n) f = {!!}
```

## Properties

### Maximum is a least upper bound

```agda
leq-max-ℕ :
  (k m n : ℕ) → m ≤-ℕ k → n ≤-ℕ k → (max-ℕ m n) ≤-ℕ k
leq-max-ℕ = {!!}

leq-left-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → m ≤-ℕ k
leq-left-leq-max-ℕ = {!!}

leq-right-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → n ≤-ℕ k
leq-right-leq-max-ℕ = {!!}

is-least-upper-bound-max-ℕ :
  (m n : ℕ) → is-least-binary-upper-bound-Poset ℕ-Poset m n (max-ℕ m n)
is-least-upper-bound-max-ℕ = {!!}
```

### Associativity of `max-ℕ`

```agda
associative-max-ℕ :
  (x y z : ℕ) → max-ℕ (max-ℕ x y) z ＝ max-ℕ x (max-ℕ y z)
associative-max-ℕ = {!!}
```

### Unit laws for `max-ℕ`

```agda
left-unit-law-max-ℕ : (x : ℕ) → max-ℕ 0 x ＝ x
left-unit-law-max-ℕ x = {!!}

right-unit-law-max-ℕ : (x : ℕ) → max-ℕ x 0 ＝ x
right-unit-law-max-ℕ zero-ℕ = {!!}
right-unit-law-max-ℕ (succ-ℕ x) = {!!}
```

### Commutativity of `max-ℕ`

```agda
commutative-max-ℕ : (x y : ℕ) → max-ℕ x y ＝ max-ℕ y x
commutative-max-ℕ zero-ℕ zero-ℕ = {!!}
commutative-max-ℕ zero-ℕ (succ-ℕ y) = {!!}
commutative-max-ℕ (succ-ℕ x) zero-ℕ = {!!}
commutative-max-ℕ (succ-ℕ x) (succ-ℕ y) = {!!}
```

### `max-ℕ` is idempotent

```agda
idempotent-max-ℕ : (x : ℕ) → max-ℕ x x ＝ x
idempotent-max-ℕ zero-ℕ = {!!}
idempotent-max-ℕ (succ-ℕ x) = {!!}
```

### Successor diagonal laws for `max-ℕ`

```agda
left-successor-diagonal-law-max-ℕ : (x : ℕ) → max-ℕ (succ-ℕ x) x ＝ succ-ℕ x
left-successor-diagonal-law-max-ℕ zero-ℕ = {!!}
left-successor-diagonal-law-max-ℕ (succ-ℕ x) = {!!}

right-successor-diagonal-law-max-ℕ : (x : ℕ) → max-ℕ x (succ-ℕ x) ＝ succ-ℕ x
right-successor-diagonal-law-max-ℕ zero-ℕ = {!!}
right-successor-diagonal-law-max-ℕ (succ-ℕ x) = {!!}
```

### Addition distributes over `max-ℕ`

```agda
left-distributive-add-max-ℕ :
  (x y z : ℕ) → x +ℕ (max-ℕ y z) ＝ max-ℕ (x +ℕ y) (x +ℕ z)
left-distributive-add-max-ℕ = {!!}

right-distributive-add-max-ℕ :
  (x y z : ℕ) → (max-ℕ x y) +ℕ z ＝ max-ℕ (x +ℕ z) (y +ℕ z)
right-distributive-add-max-ℕ = {!!}
```
