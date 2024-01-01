# Integer fractions

```agda
module elementary-number-theory.integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonzero-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The type of integer fractions is the type of pairs `n/m` consisting of an
integer `n` and a positive integer `m`. The type of rational numbers is a
retract of the type of fractions.

## Definitions

### The type of fractions

```agda
fraction-ℤ : UU lzero
fraction-ℤ = {!!}
```

### The numerator of a fraction

```agda
numerator-fraction-ℤ : fraction-ℤ → ℤ
numerator-fraction-ℤ x = {!!}
```

### The denominator of a fraction

```agda
positive-denominator-fraction-ℤ : fraction-ℤ → positive-ℤ
positive-denominator-fraction-ℤ x = {!!}

denominator-fraction-ℤ : fraction-ℤ → ℤ
denominator-fraction-ℤ x = {!!}

is-positive-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (denominator-fraction-ℤ x)
is-positive-denominator-fraction-ℤ x = {!!}
```

### Inclusion of the integers

```agda
in-fraction-ℤ-ℤ : ℤ → fraction-ℤ
pr1 (in-fraction-ℤ-ℤ x) = {!!}
pr2 (in-fraction-ℤ-ℤ x) = {!!}
```

### Negative one, zero and one

```agda
neg-one-fraction-ℤ : fraction-ℤ
neg-one-fraction-ℤ = {!!}

is-neg-one-fraction-ℤ : fraction-ℤ → UU lzero
is-neg-one-fraction-ℤ x = {!!}

zero-fraction-ℤ : fraction-ℤ
zero-fraction-ℤ = {!!}

is-zero-fraction-ℤ : fraction-ℤ → UU lzero
is-zero-fraction-ℤ x = {!!}

is-nonzero-fraction-ℤ : fraction-ℤ → UU lzero
is-nonzero-fraction-ℤ k = {!!}

one-fraction-ℤ : fraction-ℤ
one-fraction-ℤ = {!!}

is-one-fraction-ℤ : fraction-ℤ → UU lzero
is-one-fraction-ℤ x = {!!}
```

## Properties

### Denominators are nonzero

```agda
is-nonzero-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-nonzero-ℤ (denominator-fraction-ℤ x)
is-nonzero-denominator-fraction-ℤ x = {!!}
```

### The type of fractions is a set

```agda
is-set-fraction-ℤ : is-set fraction-ℤ
is-set-fraction-ℤ = {!!}
```

```agda
sim-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
sim-fraction-ℤ-Prop x y = {!!}

sim-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
sim-fraction-ℤ x y = {!!}

is-prop-sim-fraction-ℤ : (x y : fraction-ℤ) → is-prop (sim-fraction-ℤ x y)
is-prop-sim-fraction-ℤ x y = {!!}

refl-sim-fraction-ℤ : is-reflexive sim-fraction-ℤ
refl-sim-fraction-ℤ x = {!!}

symmetric-sim-fraction-ℤ : is-symmetric sim-fraction-ℤ
symmetric-sim-fraction-ℤ x y r = {!!}

transitive-sim-fraction-ℤ : is-transitive sim-fraction-ℤ
transitive-sim-fraction-ℤ x y z s r = {!!}

equivalence-relation-sim-fraction-ℤ : equivalence-relation lzero fraction-ℤ
pr1 equivalence-relation-sim-fraction-ℤ = {!!}
pr1 (pr2 equivalence-relation-sim-fraction-ℤ) = {!!}
pr1 (pr2 (pr2 equivalence-relation-sim-fraction-ℤ)) = {!!}
pr2 (pr2 (pr2 equivalence-relation-sim-fraction-ℤ)) = {!!}
```

### The greatest common divisor of the numerator and a denominator of a fraction is always a positive integer

```agda
is-positive-gcd-numerator-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  is-positive-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
is-positive-gcd-numerator-denominator-fraction-ℤ x = {!!}

is-nonzero-gcd-numerator-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  is-nonzero-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
is-nonzero-gcd-numerator-denominator-fraction-ℤ x = {!!}
```
