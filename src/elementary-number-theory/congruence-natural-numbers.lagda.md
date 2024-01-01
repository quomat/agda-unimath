# The congruence relations on the natural numbers

```agda
module elementary-number-theory.congruence-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Properties

### The congruence relations on the natural numbers

```agda
cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ = {!!}

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = {!!}

concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  x1 ＝ x2 → cong-ℕ k x2 x3 → x3 ＝ x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ = {!!}

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  x1 ＝ x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ = {!!}

concatenate-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  cong-ℕ k x1 x2 → x2 ＝ x3 → cong-ℕ k x1 x3
concatenate-cong-eq-ℕ = {!!}

is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → cong-ℕ 1 x y
is-indiscrete-cong-one-ℕ = {!!}

is-discrete-cong-zero-ℕ :
  (x y : ℕ) → cong-ℕ zero-ℕ x y → x ＝ y
is-discrete-cong-zero-ℕ = {!!}

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
cong-zero-ℕ = {!!}
pr2 (cong-zero-ℕ k) = {!!}

refl-cong-ℕ : (k : ℕ) → is-reflexive (cong-ℕ k)
refl-cong-ℕ = {!!}
pr2 (refl-cong-ℕ k x) = {!!}

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → x ＝ y → cong-ℕ k x y
cong-identification-ℕ = {!!}

symmetric-cong-ℕ : (k : ℕ) → is-symmetric (cong-ℕ k)
symmetric-cong-ℕ = {!!}
pr2 (symmetric-cong-ℕ k x y (pair d p)) = {!!}

cong-zero-ℕ' : (k : ℕ) → cong-ℕ k zero-ℕ k
cong-zero-ℕ' = {!!}

transitive-cong-ℕ : (k : ℕ) → is-transitive (cong-ℕ k)
transitive-cong-ℕ k x y z e d with is-total-dist-ℕ x y z
transitive-cong-ℕ k x y z e d | inl α = {!!}
transitive-cong-ℕ k x y z e d | inr (inl α) = {!!}
transitive-cong-ℕ k x y z e d | inr (inr α) = {!!}

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → x2 ＝ x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ = {!!}

concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  x1 ＝ x2 → cong-ℕ k x2 x3 → x3 ＝ x4 →
  cong-ℕ k x4 x5 → x5 ＝ x6 → cong-ℕ k x1 x6
concatenate-eq-cong-eq-cong-eq-ℕ = {!!}
```

```agda
eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → x ＝ y
eq-cong-le-dist-ℕ = {!!}
```

```agda
eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → x ＝ y
eq-cong-le-ℕ = {!!}
```

```agda
eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin k x) (nat-Fin k y) → x ＝ y
eq-cong-nat-Fin = {!!}
```

```agda
cong-is-zero-nat-zero-Fin :
  {k : ℕ} → cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (zero-Fin k)) zero-ℕ
cong-is-zero-nat-zero-Fin = {!!}
```

```agda
eq-cong-zero-ℕ : (x y : ℕ) → cong-ℕ zero-ℕ x y → x ＝ y
eq-cong-zero-ℕ = {!!}

is-one-cong-succ-ℕ : {k : ℕ} (x : ℕ) → cong-ℕ k x (succ-ℕ x) → is-one-ℕ k
is-one-cong-succ-ℕ = {!!}
```

### Congruence is invariant under scalar multiplication

```agda
scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (z *ℕ x) (z *ℕ y)
scalar-invariant-cong-ℕ = {!!}
pr2 (scalar-invariant-cong-ℕ k x y z (pair d p)) = {!!}

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (x *ℕ z) (y *ℕ z)
scalar-invariant-cong-ℕ' = {!!}
```

### Multiplication respects the congruence relation

```agda
congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (x *ℕ y) (x' *ℕ y')
congruence-mul-ℕ = {!!}
```

### The congruence is translation invariant

```agda
translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (z +ℕ x) (z +ℕ y)
translation-invariant-cong-ℕ = {!!}
pr2 (translation-invariant-cong-ℕ k x y z (pair d p)) = {!!}

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (x +ℕ z) (y +ℕ z)
translation-invariant-cong-ℕ' = {!!}

step-invariant-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k (succ-ℕ x) (succ-ℕ y)
step-invariant-cong-ℕ = {!!}

reflects-cong-add-ℕ :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (x +ℕ y) (x +ℕ z) → cong-ℕ k y z
reflects-cong-add-ℕ = {!!}
pr2 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) = {!!}

reflects-cong-add-ℕ' :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (add-ℕ' x y) (add-ℕ' x z) → cong-ℕ k y z
reflects-cong-add-ℕ' = {!!}
```
