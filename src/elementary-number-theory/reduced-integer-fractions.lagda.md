# Reduced integer fractions

```agda
module elementary-number-theory.reduced-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bezouts-lemma-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A reduced fraction is a fraction in which its numerator and denominator are
coprime.

## Definitions

### Reduced fraction

```agda
is-reduced-fraction-ℤ : fraction-ℤ → UU lzero
is-reduced-fraction-ℤ = {!!}
```

## Properties and constructions

### Being a reduced fraction is a proposition

```agda
is-prop-is-reduced-fraction-ℤ :
  (x : fraction-ℤ) → is-prop (is-reduced-fraction-ℤ x)
is-prop-is-reduced-fraction-ℤ = {!!}
```

### Any fraction can be reduced

```agda
reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( numerator-fraction-ℤ x)
reduce-numerator-fraction-ℤ = {!!}

int-reduce-numerator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-numerator-fraction-ℤ = {!!}

eq-reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( numerator-fraction-ℤ x)
eq-reduce-numerator-fraction-ℤ = {!!}

reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( denominator-fraction-ℤ x)
reduce-denominator-fraction-ℤ = {!!}

int-reduce-denominator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-denominator-fraction-ℤ = {!!}

eq-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-denominator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( denominator-fraction-ℤ x)
eq-reduce-denominator-fraction-ℤ = {!!}

is-positive-int-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (int-reduce-denominator-fraction-ℤ x)
is-positive-int-reduce-denominator-fraction-ℤ = {!!}

reduce-fraction-ℤ : fraction-ℤ → fraction-ℤ
reduce-fraction-ℤ = {!!}

is-reduced-reduce-fraction-ℤ :
  (x : fraction-ℤ) → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
is-reduced-reduce-fraction-ℤ = {!!}

sim-reduced-fraction-ℤ :
  (x : fraction-ℤ) → (sim-fraction-ℤ x (reduce-fraction-ℤ x))
sim-reduced-fraction-ℤ = {!!}

reduce-preserves-sim-ℤ :
  (x y : fraction-ℤ) (H : sim-fraction-ℤ x y) →
  sim-fraction-ℤ (reduce-fraction-ℤ x) (reduce-fraction-ℤ y)
reduce-preserves-sim-ℤ = {!!}
```

### Two similar fractions have equal reduced form

```agda
sim-unique-numerator-reduce-fraction-ℤ :
  ( x y : fraction-ℤ) →
  ( H : sim-fraction-ℤ x y) →
  sim-unit-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( int-reduce-numerator-fraction-ℤ y)
sim-unique-numerator-reduce-fraction-ℤ = {!!}

unique-numerator-reduce-fraction-ℤ :
  ( x y : fraction-ℤ) →
  ( H : sim-fraction-ℤ x y) →
  int-reduce-numerator-fraction-ℤ x ＝
  int-reduce-numerator-fraction-ℤ y
unique-numerator-reduce-fraction-ℤ = {!!}

      reduced-eqn :
        mul-ℤ
          ( int-reduce-numerator-fraction-ℤ x)
          ( int-reduce-denominator-fraction-ℤ y) ＝
        mul-ℤ
          ( int-reduce-numerator-fraction-ℤ x)
          ( neg-one-ℤ *ℤ (int-reduce-denominator-fraction-ℤ x))
      reduced-eqn = {!!}

      x-nat : ℕ
      x-nat = {!!}

      y-nat : ℕ
      y-nat = {!!}

      contra : inr (inr y-nat) ＝ neg-ℤ (inr (inr x-nat))
      contra = {!!}

sim-unique-denominator-reduce-fraction-ℤ :
  ( x y : fraction-ℤ) →
  ( H : sim-fraction-ℤ x y) →
  sim-unit-ℤ
    ( int-reduce-denominator-fraction-ℤ x)
    ( int-reduce-denominator-fraction-ℤ y)
sim-unique-denominator-reduce-fraction-ℤ = {!!}

unique-denominator-reduce-fraction-ℤ :
  (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
  int-reduce-denominator-fraction-ℤ x ＝ int-reduce-denominator-fraction-ℤ y
unique-denominator-reduce-fraction-ℤ = {!!}

unique-reduce-fraction-ℤ :
  (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
  reduce-fraction-ℤ x ＝ reduce-fraction-ℤ y
unique-reduce-fraction-ℤ = {!!}
```
