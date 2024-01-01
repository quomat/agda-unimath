# Divisibility of integers

```agda
module elementary-number-theory.divisibility-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An integer `m` is said to **divide** an integer `n` if there exists an integer
`k` equipped with an identification `km ＝ n`. Using the Curry-Howard
interpretation of logic into type theory, we express divisibility as follows:

```text
  div-ℤ m n := {!!}
```

If `n` is a nonzero integer, then `div-ℤ m n` is always a proposition in the
sense that the type `div-ℤ m n` contains at most one element.

We also introduce **unit integers**, which are integers that divide the integer
`1`, and an equivalence relation `sim-unit-ℤ` on the integers in which two
integers `x` and `y` are equivalent if there exists a unit integer `u` such that
`ux ＝ y`. These two concepts help establish further properties of the
divisibility relation on the integers.

## Definitions

```agda
div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = {!!}

quotient-div-ℤ : (x y : ℤ) → div-ℤ x y → ℤ
quotient-div-ℤ x y H = {!!}

eq-quotient-div-ℤ :
  (x y : ℤ) (H : div-ℤ x y) → (quotient-div-ℤ x y H) *ℤ x ＝ y
eq-quotient-div-ℤ x y H = {!!}

eq-quotient-div-ℤ' :
  (x y : ℤ) (H : div-ℤ x y) → x *ℤ (quotient-div-ℤ x y H) ＝ y
eq-quotient-div-ℤ' x y H = {!!}

div-quotient-div-ℤ :
  (d x : ℤ) (H : div-ℤ d x) → div-ℤ (quotient-div-ℤ d x H) x
pr1 (div-quotient-div-ℤ d x (u , p)) = {!!}
pr2 (div-quotient-div-ℤ d x (u , p)) = {!!}

concatenate-eq-div-ℤ :
  {x y z : ℤ} → x ＝ y → div-ℤ y z → div-ℤ x z
concatenate-eq-div-ℤ refl p = {!!}

concatenate-div-eq-ℤ :
  {x y z : ℤ} → div-ℤ x y → y ＝ z → div-ℤ x z
concatenate-div-eq-ℤ p refl = {!!}

concatenate-eq-div-eq-ℤ :
  {x y z w : ℤ} → x ＝ y → div-ℤ y z → z ＝ w → div-ℤ x w
concatenate-eq-div-eq-ℤ refl p refl = {!!}
```

### Unit integers

```agda
is-unit-ℤ : ℤ → UU lzero
is-unit-ℤ x = {!!}

unit-ℤ : UU lzero
unit-ℤ = {!!}

int-unit-ℤ : unit-ℤ → ℤ
int-unit-ℤ = {!!}

is-unit-int-unit-ℤ : (x : unit-ℤ) → is-unit-ℤ (int-unit-ℤ x)
is-unit-int-unit-ℤ = {!!}

div-is-unit-ℤ :
  (x y : ℤ) → is-unit-ℤ x → div-ℤ x y
pr1 (div-is-unit-ℤ x y (pair d p)) = {!!}
pr2 (div-is-unit-ℤ x y (pair d p)) = {!!}
```

### The equivalence relation `sim-unit-ℤ`

We define the equivalence relation `sim-unit-ℤ` in such a way that
`sim-unit-ℤ x y` is always a proposition.

```agda
presim-unit-ℤ : ℤ → ℤ → UU lzero
presim-unit-ℤ x y = {!!}

sim-unit-ℤ : ℤ → ℤ → UU lzero
sim-unit-ℤ x y = {!!}
```

## Properties

### Divisibility by a nonzero integer is a property

```agda
is-prop-div-ℤ : (d x : ℤ) → is-nonzero-ℤ d → is-prop (div-ℤ d x)
is-prop-div-ℤ d x f = {!!}
```

### The divisibility relation is a preorder

Note that the divisibility relation on the integers is not antisymmetric.

```agda
refl-div-ℤ : is-reflexive div-ℤ
pr1 (refl-div-ℤ x) = {!!}
pr2 (refl-div-ℤ x) = {!!}

transitive-div-ℤ : is-transitive div-ℤ
pr1 (transitive-div-ℤ x y z (pair e q) (pair d p)) = {!!}
pr2 (transitive-div-ℤ x y z (pair e q) (pair d p)) = {!!}
```

### Every integer is divisible by `1`

```agda
div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
pr1 (div-one-ℤ x) = {!!}
pr2 (div-one-ℤ x) = {!!}
```

### Every integer divides `0`

```agda
div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
pr1 (div-zero-ℤ x) = {!!}
pr2 (div-zero-ℤ x) = {!!}
```

### Every integer that is divisible by `0` is `0`

```agda
is-zero-div-zero-ℤ :
  (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
is-zero-div-zero-ℤ x (pair d p) = {!!}
```

### The quotient of `x` by one is `x`

```agda
eq-quotient-div-is-one-ℤ :
  (k x : ℤ) → is-one-ℤ k → (H : div-ℤ k x) → quotient-div-ℤ k x H ＝ x
eq-quotient-div-is-one-ℤ .one-ℤ x refl H = {!!}
```

### If `k` divides `x` and `k` is `0` then `x` is `0`

```agda
is-zero-is-zero-div-ℤ : (x k : ℤ) → div-ℤ k x → is-zero-ℤ k → is-zero-ℤ x
is-zero-is-zero-div-ℤ x .zero-ℤ k-div-x refl = {!!}
```

### If `x` divides both `y` and `z`, then it divides `y + z`

```agda
div-add-ℤ : (x y z : ℤ) → div-ℤ x y → div-ℤ x z → div-ℤ x (y +ℤ z)
pr1 (div-add-ℤ x y z (pair d p) (pair e q)) = {!!}
pr2 (div-add-ℤ x y z (pair d p) (pair e q)) = {!!}
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ x (k *ℤ y)
div-mul-ℤ k x y = {!!}
```

### If `x` divides `y` then it divides `-y`

```agda
div-neg-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ x (neg-ℤ y)
pr1 (div-neg-ℤ x y (pair d p)) = {!!}
pr2 (div-neg-ℤ x y (pair d p)) = {!!}
```

### If `x` divides `y` then `-x` divides `y`

```agda
neg-div-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ (neg-ℤ x) y
pr1 (neg-div-ℤ x y (pair d p)) = {!!}
pr2 (neg-div-ℤ x y (pair d p)) = {!!}
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ (k *ℤ x) (k *ℤ y)
pr1 (preserves-div-mul-ℤ k x y (pair q p)) = {!!}
pr2 (preserves-div-mul-ℤ k x y (pair q p)) = {!!}
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℤ :
  (k x y : ℤ) → is-nonzero-ℤ k → div-ℤ (k *ℤ x) (k *ℤ y) → div-ℤ x y
pr1 (reflects-div-mul-ℤ k x y H (pair q p)) = {!!}
pr2 (reflects-div-mul-ℤ k x y H (pair q p)) = {!!}
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) → is-nonzero-ℤ d →
  div-ℤ (d *ℤ x) y → div-ℤ x (quotient-div-ℤ d y H)
div-quotient-div-div-ℤ x y d H f K = {!!}

div-div-quotient-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) →
  div-ℤ x (quotient-div-ℤ d y H) → div-ℤ (d *ℤ x) y
div-div-quotient-div-ℤ x y d H K = {!!}
```

### Comparison of divisibility on `ℕ` and on `ℤ`

```agda
div-int-div-ℕ :
  {x y : ℕ} → div-ℕ x y → div-ℤ (int-ℕ x) (int-ℕ y)
pr1 (div-int-div-ℕ {x} {y} (pair d p)) = {!!}
pr2 (div-int-div-ℕ {x} {y} (pair d p)) = {!!}

div-div-int-ℕ :
  {x y : ℕ} → div-ℤ (int-ℕ x) (int-ℕ y) → div-ℕ x y
div-div-int-ℕ {zero-ℕ} {y} (pair d p) = {!!}
pr1 (div-div-int-ℕ {succ-ℕ x} {y} (pair d p)) = {!!}
pr2 (div-div-int-ℕ {succ-ℕ x} {y} (pair d p)) = {!!}
```

### An integer is a unit if and only if it is `1` or `-1`

```agda
is-one-or-neg-one-ℤ : ℤ → UU lzero
is-one-or-neg-one-ℤ x = {!!}

is-unit-one-ℤ : is-unit-ℤ one-ℤ
is-unit-one-ℤ = {!!}

one-unit-ℤ : unit-ℤ
pr1 one-unit-ℤ = {!!}
pr2 one-unit-ℤ = {!!}

is-unit-is-one-ℤ :
  (x : ℤ) → is-one-ℤ x → is-unit-ℤ x
is-unit-is-one-ℤ .one-ℤ refl = {!!}

is-unit-neg-one-ℤ : is-unit-ℤ neg-one-ℤ
pr1 is-unit-neg-one-ℤ = {!!}
pr2 is-unit-neg-one-ℤ = {!!}

neg-one-unit-ℤ : unit-ℤ
pr1 neg-one-unit-ℤ = {!!}
pr2 neg-one-unit-ℤ = {!!}

is-unit-is-neg-one-ℤ :
  (x : ℤ) → is-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-neg-one-ℤ .neg-one-ℤ refl = {!!}

is-unit-is-one-or-neg-one-ℤ :
  (x : ℤ) → is-one-or-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-one-or-neg-one-ℤ x (inl p) = {!!}
is-unit-is-one-or-neg-one-ℤ x (inr p) = {!!}

is-one-or-neg-one-is-unit-ℤ :
  (x : ℤ) → is-unit-ℤ x → is-one-or-neg-one-ℤ x
is-one-or-neg-one-is-unit-ℤ (inl zero-ℕ) (pair d p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl zero-ℕ) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl (succ-ℕ d)) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inl star)) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr zero-ℕ)) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr (succ-ℕ d))) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inr (inl star)) (pair d p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inr (inr zero-ℕ)) (pair d p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl zero-ℕ) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl (succ-ℕ d)) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inl star)) p) = {!!}
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inr zero-ℕ)) p) = {!!}
is-one-or-neg-one-is-unit-ℤ
  (inr (inr (succ-ℕ x))) (pair (inr (inr (succ-ℕ d))) p) = {!!}
```

### Units are idempotent

```agda
idempotent-is-unit-ℤ : {x : ℤ} → is-unit-ℤ x → x *ℤ x ＝ one-ℤ
idempotent-is-unit-ℤ {x} H = {!!}

abstract
  is-one-is-unit-int-ℕ : (x : ℕ) → is-unit-ℤ (int-ℕ x) → is-one-ℕ x
  is-one-is-unit-int-ℕ x H with is-one-or-neg-one-is-unit-ℤ (int-ℕ x) H
  ... | inl p = {!!}
```

### The product `xy` is a unit if and only if both `x` and `y` are units

```agda
is-unit-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ x → is-unit-ℤ y → is-unit-ℤ (x *ℤ y)
pr1 (is-unit-mul-ℤ x y (pair d p) (pair e q)) = {!!}
pr2 (is-unit-mul-ℤ x y (pair d p) (pair e q)) = {!!}

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
pr1 (mul-unit-ℤ (pair x H) (pair y K)) = {!!}
pr2 (mul-unit-ℤ (pair x H) (pair y K)) = {!!}

is-unit-left-factor-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ (x *ℤ y) → is-unit-ℤ x
pr1 (is-unit-left-factor-mul-ℤ x y (pair d p)) = {!!}
pr2 (is-unit-left-factor-mul-ℤ x y (pair d p)) = {!!}

is-unit-right-factor-ℤ :
  (x y : ℤ) → is-unit-ℤ (x *ℤ y) → is-unit-ℤ y
is-unit-right-factor-ℤ x y (pair d p) = {!!}
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are logically equivalent

```agda
sim-unit-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → sim-unit-ℤ x y
sim-unit-presim-unit-ℤ {x} {y} H f = {!!}

presim-unit-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → presim-unit-ℤ x y
presim-unit-sim-unit-ℤ {inl x} {inl y} H = {!!}
presim-unit-sim-unit-ℤ {inl x} {inr y} H = {!!}
presim-unit-sim-unit-ℤ {inr x} {inl y} H = {!!}
pr1 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = {!!}
pr2 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = {!!}
presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inr y)} H = {!!}
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inl star)} H = {!!}
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inr y)} H = {!!}
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` relate `zero-ℤ` only to itself

```agda
is-nonzero-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-presim-unit-ℤ {x} {y} (pair (pair v (pair u α)) β) f p = {!!}

is-nonzero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-sim-unit-ℤ H f = {!!}

is-zero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ x → is-zero-ℤ y
is-zero-sim-unit-ℤ {x} {y} H p = {!!}
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are equivalence relations

```agda
refl-presim-unit-ℤ : is-reflexive presim-unit-ℤ
pr1 (refl-presim-unit-ℤ x) = {!!}
pr2 (refl-presim-unit-ℤ x) = {!!}

refl-sim-unit-ℤ : is-reflexive sim-unit-ℤ
refl-sim-unit-ℤ x f = {!!}

presim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → presim-unit-ℤ x y
presim-unit-eq-ℤ {x} refl = {!!}

sim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → sim-unit-ℤ x y
sim-unit-eq-ℤ {x} refl = {!!}

symmetric-presim-unit-ℤ : is-symmetric presim-unit-ℤ
symmetric-presim-unit-ℤ x y (pair (pair u H) p) = {!!}

symmetric-sim-unit-ℤ : is-symmetric sim-unit-ℤ
symmetric-sim-unit-ℤ x y H f = {!!}

is-nonzero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ y → is-nonzero-ℤ x
is-nonzero-sim-unit-ℤ' {x} {y} H = {!!}

is-zero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ y → is-zero-ℤ x
is-zero-sim-unit-ℤ' {x} {y} H = {!!}

transitive-presim-unit-ℤ : is-transitive presim-unit-ℤ
transitive-presim-unit-ℤ x y z (pair (pair v K) q) (pair (pair u H) p) = {!!}

transitive-sim-unit-ℤ : is-transitive sim-unit-ℤ
transitive-sim-unit-ℤ x y z K H f = {!!}
```

### `sim-unit-ℤ x y` holds if and only if `x|y` and `y|x`

```agda
antisymmetric-div-ℤ :
  (x y : ℤ) → div-ℤ x y → div-ℤ y x → sim-unit-ℤ x y
antisymmetric-div-ℤ x y (pair d p) (pair e q) H = {!!}
```

### `sim-unit-ℤ |x| x` holds

```agda
sim-unit-abs-ℤ : (x : ℤ) → sim-unit-ℤ (int-abs-ℤ x) x
pr1 (sim-unit-abs-ℤ (inl x) f) = {!!}
pr2 (sim-unit-abs-ℤ (inl x) f) = {!!}
sim-unit-abs-ℤ (inr (inl star)) = {!!}
sim-unit-abs-ℤ (inr (inr x)) = {!!}

div-presim-unit-ℤ :
  {x y x' y' : ℤ} → presim-unit-ℤ x x' → presim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
pr1 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) = {!!}
pr2 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) = {!!}

div-sim-unit-ℤ :
  {x y x' y' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
div-sim-unit-ℤ {x} {y} {x'} {y'} H K = {!!}

div-int-abs-div-ℤ :
  {x y : ℤ} → div-ℤ x y → div-ℤ (int-abs-ℤ x) y
div-int-abs-div-ℤ {x} {y} = {!!}

div-div-int-abs-ℤ :
  {x y : ℤ} → div-ℤ (int-abs-ℤ x) y → div-ℤ x y
div-div-int-abs-ℤ {x} {y} = {!!}
```

### If we have that `sim-unit-ℤ x y`, then they must differ only by sign

```agda
is-plus-or-minus-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-plus-or-minus-ℤ x y
is-plus-or-minus-sim-unit-ℤ {x} {y} H with ( is-decidable-is-zero-ℤ x)
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inl z = {!!}
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz
  with
  ( is-one-or-neg-one-is-unit-ℤ
    ( int-unit-ℤ (pr1 (H (λ u → nz (pr1 u)))))
    ( is-unit-int-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))))
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inl pos = {!!}
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inr p = {!!}
```

### If `sim-unit-ℤ x y` holds and both `x` and `y` have the same sign, then `x ＝ y`

```agda
eq-sim-unit-is-nonnegative-ℤ :
  {a b : ℤ} → is-nonnegative-ℤ a → is-nonnegative-ℤ b → sim-unit-ℤ a b → a ＝ b
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K
  with is-plus-or-minus-sim-unit-ℤ K
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inl pos = {!!}
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inr neg
  with is-decidable-is-zero-ℤ a
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inr neg | inl z = {!!}
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inr neg | inr nz = {!!}
```
