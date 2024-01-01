# Modular arithmetic on the standard finite types

```agda
module elementary-number-theory.modular-arithmetic-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### The congruence class of a natural number modulo a successor

```agda
mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ = {!!}
mod-succ-ℕ k (succ-ℕ n) = {!!}

mod-two-ℕ : ℕ → Fin 2
mod-two-ℕ = {!!}

mod-three-ℕ : ℕ → Fin 3
mod-three-ℕ = {!!}
```

## Properties

### `nat-Fin k (succ-Fin k x)` and `succ-ℕ (nat-Fin k x)` are congruent modulo `k`

```agda
cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  cong-ℕ k (nat-Fin k (succ-Fin k x)) (succ-ℕ (nat-Fin k x))
cong-nat-succ-Fin = {!!}
cong-nat-succ-Fin (succ-ℕ k) (inr _) = {!!}

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ = {!!}
cong-nat-mod-succ-ℕ k (succ-ℕ x) = {!!}
```

### If the congruence classes of `x` and `y` modulo `k + 1` are equal, then `x` and `y` are congruent modulo `k + 1`

```agda
cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → mod-succ-ℕ k x ＝ mod-succ-ℕ k y → cong-ℕ (succ-ℕ k) x y
cong-eq-mod-succ-ℕ = {!!}
```

### If `x` and `y` are congruent modulo `k + 1` then their congruence classes modulo `k + 1` are equal

```agda
eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → mod-succ-ℕ k x ＝ mod-succ-ℕ k y
eq-mod-succ-cong-ℕ = {!!}
```

### `k + 1` divides `x` if and only if `x ≡ 0` modulo `k + 1`

```agda
is-zero-mod-succ-ℕ :
  (k x : ℕ) → div-ℕ (succ-ℕ k) x → is-zero-Fin (succ-ℕ k) (mod-succ-ℕ k x)
is-zero-mod-succ-ℕ = {!!}

div-is-zero-mod-succ-ℕ :
  (k x : ℕ) → is-zero-Fin (succ-ℕ k) (mod-succ-ℕ k x) → div-ℕ (succ-ℕ k) x
div-is-zero-mod-succ-ℕ = {!!}
```

### The inclusion of `Fin k` into `ℕ` is a section of `mod-succ-ℕ`

```agda
is-section-nat-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mod-succ-ℕ k (nat-Fin (succ-ℕ k) x) ＝ x
is-section-nat-Fin = {!!}
```

### `mod-succ-ℕ` is split surjective

```agda
is-split-surjective-mod-succ-ℕ :
  (k : ℕ) → is-split-surjective (mod-succ-ℕ k)
is-split-surjective-mod-succ-ℕ = {!!}
pr2 (is-split-surjective-mod-succ-ℕ k x) = {!!}
```

### `mod-succ-ℕ` is surjective

```agda
is-surjective-mod-succ-ℕ :
  (k : ℕ) → is-surjective (mod-succ-ℕ k)
is-surjective-mod-succ-ℕ = {!!}
```

### The residue of `x` modulo `k + 1` is less than or equal to `x`

```agda
leq-nat-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
leq-nat-mod-succ-ℕ = {!!}
leq-nat-mod-succ-ℕ k (succ-ℕ x) = {!!}
```

## Operations

### Addition on the standard finite sets

```agda
add-Fin : (k : ℕ) → Fin k → Fin k → Fin k
add-Fin = {!!}

add-Fin' : (k : ℕ) → Fin k → Fin k → Fin k
add-Fin' = {!!}

ap-add-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → add-Fin k x y ＝ add-Fin k x' y'
ap-add-Fin = {!!}

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin k (add-Fin k x y)) ((nat-Fin k x) +ℕ (nat-Fin k y))
cong-add-Fin = {!!}

cong-add-ℕ :
  {k : ℕ} (x y : ℕ) →
  cong-ℕ
    ( succ-ℕ k)
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)))
    ( x +ℕ y)
cong-add-ℕ = {!!}

congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (x +ℕ y) (x' +ℕ y')
congruence-add-ℕ = {!!}

mod-succ-add-ℕ :
  (k x y : ℕ) →
  mod-succ-ℕ k (x +ℕ y) ＝
  add-Fin (succ-ℕ k) (mod-succ-ℕ k x) (mod-succ-ℕ k y)
mod-succ-add-ℕ = {!!}
```

### Distance on the standard finite sets

```agda
dist-Fin : (k : ℕ) → Fin k → Fin k → Fin k
dist-Fin = {!!}

dist-Fin' : (k : ℕ) → Fin k → Fin k → Fin k
dist-Fin' = {!!}

ap-dist-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → dist-Fin k x y ＝ dist-Fin k x' y'
ap-dist-Fin = {!!}

cong-dist-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin k (dist-Fin k x y)) (dist-ℕ (nat-Fin k x) (nat-Fin k y))
cong-dist-Fin = {!!}
```

### The negative of an element of a standard finite set

```agda
neg-Fin :
  (k : ℕ) → Fin k → Fin k
neg-Fin = {!!}

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin k (neg-Fin k x)) (dist-ℕ (nat-Fin k x) k)
cong-neg-Fin = {!!}
```

### Multiplication on the standard finite sets

```agda
mul-Fin :
  (k : ℕ) → Fin k → Fin k → Fin k
mul-Fin = {!!}

mul-Fin' :
  (k : ℕ) → Fin k → Fin k → Fin k
mul-Fin' = {!!}

ap-mul-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → mul-Fin k x y ＝ mul-Fin k x' y'
ap-mul-Fin = {!!}

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin k (mul-Fin k x y)) ((nat-Fin k x) *ℕ (nat-Fin k y))
cong-mul-Fin = {!!}
```

## Laws

### Laws for addition

```agda
commutative-add-Fin : (k : ℕ) (x y : Fin k) → add-Fin k x y ＝ add-Fin k y x
commutative-add-Fin = {!!}

associative-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  add-Fin k (add-Fin k x y) z ＝ add-Fin k x (add-Fin k y z)
associative-add-Fin = {!!}

right-unit-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → add-Fin (succ-ℕ k) x (zero-Fin k) ＝ x
right-unit-law-add-Fin = {!!}

left-unit-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → add-Fin (succ-ℕ k) (zero-Fin k) x ＝ x
left-unit-law-add-Fin = {!!}

left-inverse-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  is-zero-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x) x)
left-inverse-law-add-Fin = {!!}

right-inverse-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  is-zero-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) x))
right-inverse-law-add-Fin = {!!}
```

### The successor function on a standard finite set adds one

```agda
is-add-one-succ-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) x (one-Fin k)
is-add-one-succ-Fin' = {!!}
is-add-one-succ-Fin' (succ-ℕ k) x = {!!}

is-add-one-succ-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) (one-Fin k) x
is-add-one-succ-Fin = {!!}
```

### Successor laws for addition on Fin k

```agda
right-successor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k x (succ-Fin k y) ＝ succ-Fin k (add-Fin k x y)
right-successor-law-add-Fin = {!!}

left-successor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k (succ-Fin k x) y ＝ succ-Fin k (add-Fin k x y)
left-successor-law-add-Fin = {!!}
```

### Laws for multiplication on the standard finite types

```agda
associative-mul-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k (mul-Fin k x y) z ＝ mul-Fin k x (mul-Fin k y z)
associative-mul-Fin = {!!}

commutative-mul-Fin :
  (k : ℕ) (x y : Fin k) → mul-Fin k x y ＝ mul-Fin k y x
commutative-mul-Fin = {!!}

left-unit-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) (one-Fin k) x ＝ x
left-unit-law-mul-Fin = {!!}
left-unit-law-mul-Fin (succ-ℕ k) x = {!!}

right-unit-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) x (one-Fin k) ＝ x
right-unit-law-mul-Fin = {!!}

left-zero-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) (zero-Fin k) x ＝ zero-Fin k
left-zero-law-mul-Fin = {!!}

right-zero-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) x (zero-Fin k) ＝ zero-Fin k
right-zero-law-mul-Fin = {!!}

left-distributive-mul-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k x (add-Fin k y z) ＝ add-Fin k (mul-Fin k x y) (mul-Fin k x z)
left-distributive-mul-add-Fin = {!!}

right-distributive-mul-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k (add-Fin k x y) z ＝ add-Fin k (mul-Fin k x z) (mul-Fin k y z)
right-distributive-mul-add-Fin = {!!}
```

## Properties

### Addition on `Fin k` is a binary equivalence

```agda
add-add-neg-Fin :
  (k : ℕ) (x y : Fin k) → add-Fin k x (add-Fin k (neg-Fin k x) y) ＝ y
add-add-neg-Fin = {!!}

add-neg-add-Fin :
  (k : ℕ) (x y : Fin k) → add-Fin k (neg-Fin k x) (add-Fin k x y) ＝ y
add-neg-add-Fin = {!!}

is-equiv-add-Fin :
  (k : ℕ) (x : Fin k) → is-equiv (add-Fin k x)
is-equiv-add-Fin = {!!}
pr2 (pr1 (is-equiv-add-Fin k x)) = {!!}
pr1 (pr2 (is-equiv-add-Fin k x)) = {!!}
pr2 (pr2 (is-equiv-add-Fin k x)) = {!!}

equiv-add-Fin :
  (k : ℕ) (x : Fin k) → Fin k ≃ Fin k
equiv-add-Fin = {!!}
pr2 (equiv-add-Fin k x) = {!!}

add-add-neg-Fin' :
  (k : ℕ) (x y : Fin k) → add-Fin' k x (add-Fin' k (neg-Fin k x) y) ＝ y
add-add-neg-Fin' = {!!}

add-neg-add-Fin' :
  (k : ℕ) (x y : Fin k) → add-Fin' k (neg-Fin k x) (add-Fin' k x y) ＝ y
add-neg-add-Fin' = {!!}

is-equiv-add-Fin' :
  (k : ℕ) (x : Fin k) → is-equiv (add-Fin' k x)
is-equiv-add-Fin' = {!!}
pr2 (pr1 (is-equiv-add-Fin' k x)) = {!!}
pr1 (pr2 (is-equiv-add-Fin' k x)) = {!!}
pr2 (pr2 (is-equiv-add-Fin' k x)) = {!!}

equiv-add-Fin' :
  (k : ℕ) (x : Fin k) → Fin k ≃ Fin k
equiv-add-Fin' = {!!}
pr2 (equiv-add-Fin' k x) = {!!}

is-injective-add-Fin :
  (k : ℕ) (x : Fin k) → is-injective (add-Fin k x)
is-injective-add-Fin = {!!}

is-injective-add-Fin' :
  (k : ℕ) (x : Fin k) → is-injective (add-Fin' k x)
is-injective-add-Fin' = {!!}
```

### `neg-Fin` multiplies by `-1`

```agda
mul-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  mul-Fin (succ-ℕ k) (neg-one-Fin k) x ＝ neg-Fin (succ-ℕ k) x
mul-neg-one-Fin = {!!}
```

### The negative of `-1` is `1`

```agda
is-one-neg-neg-one-Fin :
  (k : ℕ) → is-one-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) (neg-one-Fin k))
is-one-neg-neg-one-Fin = {!!}
```

### The negative of `1` is `-1`

```agda
is-neg-one-neg-one-Fin :
  (k : ℕ) → neg-Fin (succ-ℕ k) (one-Fin k) ＝ (neg-one-Fin k)
is-neg-one-neg-one-Fin = {!!}
```

### The predecessor function adds `-1`

```agda
is-add-neg-one-pred-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  pred-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) x (neg-one-Fin k)
is-add-neg-one-pred-Fin' = {!!}

is-add-neg-one-pred-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  pred-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) (neg-one-Fin k) x
is-add-neg-one-pred-Fin = {!!}
```

### `neg-Fin` multiplies by `-1`

```agda
is-mul-neg-one-neg-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  neg-Fin (succ-ℕ k) x ＝ mul-Fin (succ-ℕ k) (neg-one-Fin k) x
is-mul-neg-one-neg-Fin = {!!}

is-mul-neg-one-neg-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  neg-Fin (succ-ℕ k) x ＝ mul-Fin (succ-ℕ k) x (neg-one-Fin k)
is-mul-neg-one-neg-Fin' = {!!}
```

### The negative of `0` is `0`

```agda
neg-zero-Fin : (k : ℕ) → neg-Fin (succ-ℕ k) (zero-Fin k) ＝ zero-Fin k
neg-zero-Fin = {!!}
```

### The negative of a successor is the predecessor of the negative

```agda
neg-succ-Fin :
  (k : ℕ) (x : Fin k) → neg-Fin k (succ-Fin k x) ＝ pred-Fin k (neg-Fin k x)
neg-succ-Fin = {!!}
```

### The negative of a predecessor is the successor of a negative

```agda
neg-pred-Fin :
  (k : ℕ) (x : Fin k) → neg-Fin k (pred-Fin k x) ＝ succ-Fin k (neg-Fin k x)
neg-pred-Fin = {!!}
```

### Taking negatives distributes over addition

```agda
distributive-neg-add-Fin :
  (k : ℕ) (x y : Fin k) →
  neg-Fin k (add-Fin k x y) ＝ add-Fin k (neg-Fin k x) (neg-Fin k y)
distributive-neg-add-Fin = {!!}
```

### Predecessor laws of addition

```agda
left-predecessor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k (pred-Fin k x) y ＝ pred-Fin k (add-Fin k x y)
left-predecessor-law-add-Fin = {!!}

right-predecessor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k x (pred-Fin k y) ＝ pred-Fin k (add-Fin k x y)
right-predecessor-law-add-Fin = {!!}
```

### Negative laws of multiplication

```agda
left-negative-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k (neg-Fin k x) y ＝ neg-Fin k (mul-Fin k x y)
left-negative-law-mul-Fin = {!!}

right-negative-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k x (neg-Fin k y) ＝ neg-Fin k (mul-Fin k x y)
right-negative-law-mul-Fin = {!!}
```

### Successor laws of multiplication

```agda
left-successor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k (succ-Fin k x) y ＝ add-Fin k y (mul-Fin k x y)
left-successor-law-mul-Fin = {!!}

right-successor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k x (succ-Fin k y) ＝ add-Fin k x (mul-Fin k x y)
right-successor-law-mul-Fin = {!!}
```

### Predecessor laws of multiplication

```agda
left-predecessor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k (pred-Fin k x) y ＝ add-Fin k (neg-Fin k y) (mul-Fin k x y)
left-predecessor-law-mul-Fin = {!!}

right-predecessor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k x (pred-Fin k y) ＝ add-Fin k (neg-Fin k x) (mul-Fin k x y)
right-predecessor-law-mul-Fin = {!!}
```

### Taking negatives is an involution

```agda
neg-neg-Fin :
  (k : ℕ) (x : Fin k) → neg-Fin k (neg-Fin k x) ＝ x
neg-neg-Fin = {!!}

is-equiv-neg-Fin :
  (k : ℕ) → is-equiv (neg-Fin k)
is-equiv-neg-Fin = {!!}
pr2 (pr1 (is-equiv-neg-Fin k)) = {!!}
pr1 (pr2 (is-equiv-neg-Fin k)) = {!!}
pr2 (pr2 (is-equiv-neg-Fin k)) = {!!}

equiv-neg-Fin :
  (k : ℕ) → Fin k ≃ Fin k
equiv-neg-Fin = {!!}
pr2 (equiv-neg-Fin k) = {!!}
```

## Properties

### Divisibility is a decidable relation on `ℕ`

```agda
is-decidable-div-ℕ : (d x : ℕ) → is-decidable (div-ℕ d x)
is-decidable-div-ℕ = {!!}
is-decidable-div-ℕ (succ-ℕ d) x = {!!}

div-ℕ-Decidable-Prop : (d x : ℕ) → is-nonzero-ℕ d → Decidable-Prop lzero
div-ℕ-Decidable-Prop = {!!}
pr1 (pr2 (div-ℕ-Decidable-Prop d x H)) = {!!}
pr2 (pr2 (div-ℕ-Decidable-Prop d x H)) = {!!}
```
