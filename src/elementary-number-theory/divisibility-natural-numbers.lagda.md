# Divisibility of natural numbers

```agda
module elementary-number-theory.divisibility-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A natural number `m` is said to **divide** a natural number `n` if there exists
a natural number `k` equipped with an identification `km ＝ n`. Using the
Curry-Howard interpretation of logic into type theory, we express divisibility
as follows:

```text
  div-ℕ m n := {!!}
```

If `n` is a nonzero natural number, then `div-ℕ m n` is always a proposition in
the sense that the type `div-ℕ m n` contains at most one element.

## Definitions

```agda
div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = {!!}

quotient-div-ℕ : (x y : ℕ) → div-ℕ x y → ℕ
quotient-div-ℕ x y H = {!!}

eq-quotient-div-ℕ :
  (x y : ℕ) (H : div-ℕ x y) → (quotient-div-ℕ x y H) *ℕ x ＝ y
eq-quotient-div-ℕ x y H = {!!}

eq-quotient-div-ℕ' :
  (x y : ℕ) (H : div-ℕ x y) → x *ℕ (quotient-div-ℕ x y H) ＝ y
eq-quotient-div-ℕ' x y H = {!!}

div-quotient-div-ℕ :
  (d x : ℕ) (H : div-ℕ d x) → div-ℕ (quotient-div-ℕ d x H) x
pr1 (div-quotient-div-ℕ d x (u , p)) = {!!}
pr2 (div-quotient-div-ℕ d x (u , p)) = {!!}
```

### Concatenating equality and divisibility

```agda
concatenate-eq-div-ℕ :
  {x y z : ℕ} → x ＝ y → div-ℕ y z → div-ℕ x z
concatenate-eq-div-ℕ refl p = {!!}

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → y ＝ z → div-ℕ x z
concatenate-div-eq-ℕ p refl = {!!}

concatenate-eq-div-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → div-ℕ y z → z ＝ w → div-ℕ x w
concatenate-eq-div-eq-ℕ refl p refl = {!!}
```

## Properties

### The quotients of a natural number `n` by two natural numbers `p` and `q` are equal if `p` and `q` are equal

```agda
eq-quotient-div-eq-div-ℕ :
  (x y z : ℕ) → is-nonzero-ℕ x → x ＝ y →
  (H : div-ℕ x z) → (I : div-ℕ y z) →
  quotient-div-ℕ x z H ＝ quotient-div-ℕ y z I
eq-quotient-div-eq-div-ℕ x y z n e H I = {!!}
```

### Divisibility by a nonzero natural number is a property

```agda
is-prop-div-ℕ : (k x : ℕ) → is-nonzero-ℕ k → is-prop (div-ℕ k x)
is-prop-div-ℕ k x f = {!!}
```

### The divisibility relation is a partial order on the natural numbers

```agda
refl-div-ℕ : is-reflexive div-ℕ
pr1 (refl-div-ℕ x) = {!!}
pr2 (refl-div-ℕ x) = {!!}

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = {!!}

antisymmetric-div-ℕ : is-antisymmetric div-ℕ
antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = {!!}
antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K = {!!}
antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) = {!!}
antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) = {!!}

transitive-div-ℕ : is-transitive div-ℕ
pr1 (transitive-div-ℕ x y z (pair l q) (pair k p)) = {!!}
pr2 (transitive-div-ℕ x y z (pair l q) (pair k p)) = {!!}
```

### If `x` is nonzero and `d | x`, then `d ≤ x`

```agda
leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) = {!!}

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (pair y refl) = {!!}

leq-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → leq-ℕ (quotient-div-ℕ d x H) x
leq-quotient-div-ℕ d x f H = {!!}

leq-quotient-div-ℕ' :
  (d x : ℕ) → is-nonzero-ℕ d → (H : div-ℕ d x) → leq-ℕ (quotient-div-ℕ d x H) x
leq-quotient-div-ℕ' d zero-ℕ f (zero-ℕ , p) = {!!}
leq-quotient-div-ℕ' d zero-ℕ f (succ-ℕ n , p) = {!!}
leq-quotient-div-ℕ' d (succ-ℕ x) f H = {!!}
```

### If `x` is nonzero, if `d | x` and `d ≠ x`, then `d < x`

```agda
le-div-succ-ℕ :
  (d x : ℕ) → div-ℕ d (succ-ℕ x) → d ≠ succ-ℕ x → le-ℕ d (succ-ℕ x)
le-div-succ-ℕ d x H f = {!!}

le-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → d ≠ x → le-ℕ d x
le-div-ℕ d x H K f = {!!}
```

### `1` divides any number

```agda
div-one-ℕ :
  (x : ℕ) → div-ℕ 1 x
pr1 (div-one-ℕ x) = {!!}
pr2 (div-one-ℕ x) = {!!}

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .1 x refl = {!!}
```

### `x | 1` implies `x ＝ 1`

```agda
is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = {!!}
```

### Any number divides `0`

```agda
div-zero-ℕ :
  (k : ℕ) → div-ℕ k 0
pr1 (div-zero-ℕ k) = {!!}
pr2 (div-zero-ℕ k) = {!!}

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = {!!}
```

### `0 | x` implies `x = {!!}

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = {!!}

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = {!!}
```

### Any divisor of a nonzero number is nonzero

```agda
is-nonzero-div-ℕ :
  (d x : ℕ) → div-ℕ d x → is-nonzero-ℕ x → is-nonzero-ℕ d
is-nonzero-div-ℕ .zero-ℕ x H K refl = {!!}
```

### Any divisor of a number at least `1` is at least `1`

```agda
leq-one-div-ℕ :
  (d x : ℕ) → div-ℕ d x → leq-ℕ 1 x → leq-ℕ 1 d
leq-one-div-ℕ d x H L = {!!}
```

### If `x < d` and `d | x`, then `x` must be `0`

```agda
is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = {!!}
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) = {!!}
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (k *ℕ y)
div-mul-ℕ k x y H = {!!}

div-mul-ℕ' :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (y *ℕ k)
div-mul-ℕ' k x y H = {!!}
```

### A 3-for-2 property of division with respect to addition

```agda
div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (x +ℕ y)
pr1 (div-add-ℕ d x y (pair n p) (pair m q)) = {!!}
pr2 (div-add-ℕ d x y (pair n p) (pair m q)) = {!!}

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (x +ℕ y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) = {!!}
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = {!!}
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = {!!}

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (x +ℕ y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 = {!!}
```

### If `d` divides both `x` and `x + 1`, then `d ＝ 1`

```agda
is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = {!!}
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (k *ℕ x) (k *ℕ y)
pr1 (preserves-div-mul-ℕ k x y (pair q p)) = {!!}
pr2 (preserves-div-mul-ℕ k x y (pair q p)) = {!!}
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → div-ℕ (k *ℕ x) (k *ℕ y) → div-ℕ x y
pr1 (reflects-div-mul-ℕ k x y H (pair q p)) = {!!}
pr2 (reflects-div-mul-ℕ k x y H (pair q p)) = {!!}
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) → is-nonzero-ℕ d →
  div-ℕ (d *ℕ x) y → div-ℕ x (quotient-div-ℕ d y H)
div-quotient-div-div-ℕ x y d H f K = {!!}

div-div-quotient-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ x (quotient-div-ℕ d y H) → div-ℕ (d *ℕ x) y
div-div-quotient-div-ℕ x y d H K = {!!}
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕ :
  {d x : ℕ} (H : div-ℕ d x) →
  is-nonzero-ℕ x → is-nonzero-ℕ (quotient-div-ℕ d x H)
is-nonzero-quotient-div-ℕ {d} {.(k *ℕ d)} (pair k refl) = {!!}
```

### If `d` divides a number `1 ≤ x`, then `1 ≤ x/d`

```agda
leq-one-quotient-div-ℕ :
  (d x : ℕ) (H : div-ℕ d x) → leq-ℕ 1 x → leq-ℕ 1 (quotient-div-ℕ d x H)
leq-one-quotient-div-ℕ d x H K = {!!}
```

### `a/a ＝ 1`

```agda
is-idempotent-quotient-div-ℕ :
  (a : ℕ) → is-nonzero-ℕ a → (H : div-ℕ a a) → is-one-ℕ (quotient-div-ℕ a a H)
is-idempotent-quotient-div-ℕ zero-ℕ nz (u , p) = {!!}
is-idempotent-quotient-div-ℕ (succ-ℕ a) nz (u , p) = {!!}
```

### If `b` divides `a` and `c` divides `b` and `c` is nonzero, then `a/b · b/c ＝ a/c`

```agda
simplify-mul-quotient-div-ℕ :
  {a b c : ℕ} → is-nonzero-ℕ c →
  (H : div-ℕ b a) (K : div-ℕ c b) (L : div-ℕ c a) →
  ( (quotient-div-ℕ b a H) *ℕ (quotient-div-ℕ c b K)) ＝
  ( quotient-div-ℕ c a L)
simplify-mul-quotient-div-ℕ {a} {b} {c} nz H K L = {!!}
```

### If `d | a` and `d` is nonzero, then `x | a/d` if and only if `xd | a`

```agda
simplify-div-quotient-div-ℕ :
  {a d x : ℕ} → is-nonzero-ℕ d → (H : div-ℕ d a) →
  (div-ℕ x (quotient-div-ℕ d a H)) ↔ (div-ℕ (x *ℕ d) a)
pr1 (pr1 (simplify-div-quotient-div-ℕ nz H) (u , p)) = {!!}
pr2 (pr1 (simplify-div-quotient-div-ℕ {a} {d} {x} nz H) (u , p)) = {!!}
pr1 (pr2 (simplify-div-quotient-div-ℕ nz H) (u , p)) = {!!}
pr2 (pr2 (simplify-div-quotient-div-ℕ {a} {d} {x} nz H) (u , p)) = {!!}
```

### Suppose `H : b | a` and `K : c | b`, where `c` is nonzero. If `d` divides `b/c` then `d` divides `a/c`

```agda
div-quotient-div-div-quotient-div-ℕ :
  {a b c d : ℕ} → is-nonzero-ℕ c → (H : div-ℕ b a)
  (K : div-ℕ c b) (L : div-ℕ c a) →
  div-ℕ d (quotient-div-ℕ c b K) →
  div-ℕ d (quotient-div-ℕ c a L)
div-quotient-div-div-quotient-div-ℕ {a} {b} {c} {d} nz H K L M = {!!}
```

### If `x` is nonzero and `d | x`, then `x/d ＝ 1` if and only if `d ＝ x`

```agda
is-one-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → (d ＝ x) →
  is-one-ℕ (quotient-div-ℕ d x H)
is-one-quotient-div-ℕ d .d f H refl = {!!}

eq-is-one-quotient-div-ℕ :
  (d x : ℕ) → (H : div-ℕ d x) → is-one-ℕ (quotient-div-ℕ d x H) → d ＝ x
eq-is-one-quotient-div-ℕ d x (.1 , q) refl = {!!}
```

### If `x` is nonzero and `d | x`, then `x/d ＝ x` if and only if `d ＝ 1`

```agda
compute-quotient-div-is-one-ℕ :
  (d x : ℕ) → (H : div-ℕ d x) → is-one-ℕ d → quotient-div-ℕ d x H ＝ x
compute-quotient-div-is-one-ℕ .1 x (u , q) refl = {!!}

is-one-divisor-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) →
  quotient-div-ℕ d x H ＝ x → is-one-ℕ d
is-one-divisor-ℕ d x f (.x , q) refl = {!!}
```

### If `x` is nonzero and `d | x` is a nontrivial divisor, then `x/d < x`

```agda
le-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → ¬ (is-one-ℕ d) →
  le-ℕ (quotient-div-ℕ d x H) x
le-quotient-div-ℕ d x f H g = {!!}
```
