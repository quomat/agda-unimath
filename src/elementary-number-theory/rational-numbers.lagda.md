# The rational numbers

```agda
module elementary-number-theory.rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The type of rational numbers is the quotient of the type of fractions, by the
equivalence relation given by `(n/m) ~ (n'/m') := {!!}

## Definitions

### The type of rationals

```agda
ℚ : UU lzero
ℚ = {!!}

fraction-ℚ : ℚ → fraction-ℤ
fraction-ℚ = {!!}

is-reduced-fraction-ℚ : (x : ℚ) → is-reduced-fraction-ℤ (fraction-ℚ x)
is-reduced-fraction-ℚ = {!!}
```

### Inclusion of fractions

```agda
in-fraction-ℤ : fraction-ℤ → ℚ
in-fraction-ℤ = {!!}
pr2 (in-fraction-ℤ x) = {!!}
```

### Inclusion of the integers

```agda
in-int : ℤ → ℚ
in-int = {!!}
```

### Negative one, zero and one

```agda
neg-one-ℚ : ℚ
neg-one-ℚ = {!!}

is-neg-one-ℚ : ℚ → UU lzero
is-neg-one-ℚ = {!!}

zero-ℚ : ℚ
zero-ℚ = {!!}

is-zero-ℚ : ℚ → UU lzero
is-zero-ℚ = {!!}

is-nonzero-ℚ : ℚ → UU lzero
is-nonzero-ℚ = {!!}

one-ℚ : ℚ
one-ℚ = {!!}

is-one-ℚ : ℚ → UU lzero
is-one-ℚ = {!!}
```

## Properties

### If two fractions are related by `sim-fraction-ℤ`, then their embeddings into `ℚ` are equal

```agda
eq-ℚ-sim-fractions-ℤ :
  (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
  in-fraction-ℤ x ＝ in-fraction-ℤ y
eq-ℚ-sim-fractions-ℤ = {!!}
```

### The type of rationals is a set

```agda
is-set-ℚ : is-set ℚ
is-set-ℚ = {!!}

ℚ-Set : Set lzero
ℚ-Set = {!!}
pr2 ℚ-Set = {!!}

in-fraction-fraction-ℚ : (x : ℚ) → in-fraction-ℤ (fraction-ℚ x) ＝ x
in-fraction-fraction-ℚ = {!!}
```

### The reflecting map from ℤ to ℚ

```agda
reflecting-map-sim-fraction :
  reflecting-map-equivalence-relation equivalence-relation-sim-fraction-ℤ ℚ
reflecting-map-sim-fraction = {!!}
```
