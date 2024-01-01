# The congruence relations on the integers

```agda
module elementary-number-theory.congruence-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Definitions

```agda
cong-ℤ : ℤ → ℤ → ℤ → UU lzero
cong-ℤ = {!!}

is-cong-zero-ℤ : ℤ → ℤ → UU lzero
is-cong-zero-ℤ = {!!}
```

## Properties

```agda
is-cong-zero-div-ℤ : (k x : ℤ) → div-ℤ k x → is-cong-zero-ℤ k x
is-cong-zero-div-ℤ = {!!}
pr2 (is-cong-zero-div-ℤ k x (pair d p)) = {!!}

div-is-cong-zero-ℤ : (k x : ℤ) → is-cong-zero-ℤ k x → div-ℤ k x
div-is-cong-zero-ℤ = {!!}
pr2 (div-is-cong-zero-ℤ k x (pair d p)) = {!!}

is-indiscrete-cong-ℤ : (k : ℤ) → is-unit-ℤ k → (x y : ℤ) → cong-ℤ k x y
is-indiscrete-cong-ℤ = {!!}

is-discrete-cong-ℤ : (k : ℤ) → is-zero-ℤ k → (x y : ℤ) → cong-ℤ k x y → x ＝ y
is-discrete-cong-ℤ = {!!}

is-unit-cong-succ-ℤ : (k x : ℤ) → cong-ℤ k x (succ-ℤ x) → is-unit-ℤ k
is-unit-cong-succ-ℤ = {!!}
pr2 (is-unit-cong-succ-ℤ k x (pair y p)) = {!!}

is-unit-cong-pred-ℤ : (k x : ℤ) → cong-ℤ k x (pred-ℤ x) → is-unit-ℤ k
is-unit-cong-pred-ℤ = {!!}
pr2 (is-unit-cong-pred-ℤ k x (pair y p)) = {!!}

refl-cong-ℤ : (k : ℤ) → is-reflexive (cong-ℤ k)
refl-cong-ℤ = {!!}
pr2 (refl-cong-ℤ k x) = {!!}

symmetric-cong-ℤ : (k : ℤ) → is-symmetric (cong-ℤ k)
symmetric-cong-ℤ = {!!}
pr2 (symmetric-cong-ℤ k x y (pair d p)) = {!!}

transitive-cong-ℤ : (k : ℤ) → is-transitive (cong-ℤ k)
transitive-cong-ℤ = {!!}
pr2 (transitive-cong-ℤ k x y z (pair e q) (pair d p)) = {!!}

concatenate-eq-cong-ℤ :
  (k x x' y : ℤ) → x ＝ x' → cong-ℤ k x' y → cong-ℤ k x y
concatenate-eq-cong-ℤ = {!!}

concatenate-cong-eq-ℤ :
  (k x y y' : ℤ) → cong-ℤ k x y → y ＝ y' → cong-ℤ k x y'
concatenate-cong-eq-ℤ = {!!}

concatenate-eq-cong-eq-ℤ :
  (k x x' y' y : ℤ) → x ＝ x' → cong-ℤ k x' y' → y' ＝ y → cong-ℤ k x y
concatenate-eq-cong-eq-ℤ = {!!}

concatenate-cong-eq-cong-ℤ :
  (k x y y' z : ℤ) → cong-ℤ k x y → y ＝ y' → cong-ℤ k y' z → cong-ℤ k x z
concatenate-cong-eq-cong-ℤ = {!!}

concatenate-cong-cong-cong-ℤ :
  (k x y z w : ℤ) → cong-ℤ k x y → cong-ℤ k y z → cong-ℤ k z w → cong-ℤ k x w
concatenate-cong-cong-cong-ℤ = {!!}

cong-cong-neg-ℤ : (k x y : ℤ) → cong-ℤ k (neg-ℤ x) (neg-ℤ y) → cong-ℤ k x y
cong-cong-neg-ℤ = {!!}
pr2 (cong-cong-neg-ℤ k x y (pair d p)) = {!!}

cong-neg-cong-ℤ : (k x y : ℤ) → cong-ℤ k x y → cong-ℤ k (neg-ℤ x) (neg-ℤ y)
cong-neg-cong-ℤ = {!!}
pr2 (cong-neg-cong-ℤ k x y (pair d p)) = {!!}
```

```agda
cong-int-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℤ (int-ℕ k) (int-ℕ x) (int-ℕ y)
cong-int-cong-ℕ = {!!}

cong-cong-int-ℕ :
  (k x y : ℕ) → cong-ℤ (int-ℕ k) (int-ℕ x) (int-ℕ y) → cong-ℕ k x y
cong-cong-int-ℕ = {!!}
```
