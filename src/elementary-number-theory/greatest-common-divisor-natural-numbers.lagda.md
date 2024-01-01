# The greatest common divisor of natural numbers

```agda
module elementary-number-theory.greatest-common-divisor-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The greatest common divisor of two natural numbers `x` and `y` is a number
`gcd x y` such that any natural number `d : ℕ` is a common divisor of `x` and
`y` if and only if it is a divisor of `gcd x y`.

## Definition

### Common divisors

```agda
is-common-divisor-ℕ : (a b x : ℕ) → UU lzero
is-common-divisor-ℕ a b x = {!!}
```

### Greatest common divisors

```agda
is-gcd-ℕ : (a b d : ℕ) → UU lzero
is-gcd-ℕ a b d = {!!}
```

### The predicate of being a multiple of the greatest common divisor

```agda
is-multiple-of-gcd-ℕ : (a b n : ℕ) → UU lzero
is-multiple-of-gcd-ℕ a b n = {!!}
```

## Properties

### Reflexivity for common divisors

```agda
refl-is-common-divisor-ℕ :
  (x : ℕ) → is-common-divisor-ℕ x x x
pr1 (refl-is-common-divisor-ℕ x) = {!!}
pr2 (refl-is-common-divisor-ℕ x) = {!!}
```

### Being a common divisor is decidable

```agda
is-decidable-is-common-divisor-ℕ :
  (a b : ℕ) → is-decidable-fam (is-common-divisor-ℕ a b)
is-decidable-is-common-divisor-ℕ a b x = {!!}
```

### Any greatest common divisor is a common divisor

```agda
is-common-divisor-is-gcd-ℕ :
  (a b d : ℕ) → is-gcd-ℕ a b d → is-common-divisor-ℕ a b d
is-common-divisor-is-gcd-ℕ a b d H = {!!}
```

### Uniqueness of greatest common divisors

```agda
uniqueness-is-gcd-ℕ :
  (a b d d' : ℕ) → is-gcd-ℕ a b d → is-gcd-ℕ a b d' → d ＝ d'
uniqueness-is-gcd-ℕ a b d d' H H' = {!!}
```

### If `d` is a common divisor of `a` and `b`, and `a + b ≠ 0`, then `d ≤ a + b`

```agda
leq-sum-is-common-divisor-ℕ' :
  (a b d : ℕ) →
  is-successor-ℕ (a +ℕ b) → is-common-divisor-ℕ a b d → leq-ℕ d (a +ℕ b)
leq-sum-is-common-divisor-ℕ' a zero-ℕ d (pair k p) H = {!!}
leq-sum-is-common-divisor-ℕ' a (succ-ℕ b) d (pair k p) H = {!!}

leq-sum-is-common-divisor-ℕ :
  (a b d : ℕ) →
  is-nonzero-ℕ (a +ℕ b) → is-common-divisor-ℕ a b d → leq-ℕ d (a +ℕ b)
leq-sum-is-common-divisor-ℕ a b d H = {!!}
```

### Being a multiple of the greatest common divisor is decidable

```agda
is-decidable-is-multiple-of-gcd-ℕ :
  (a b : ℕ) → is-decidable-fam (is-multiple-of-gcd-ℕ a b)
is-decidable-is-multiple-of-gcd-ℕ a b n = {!!}
```

### The sum of `a` and `b` is a multiple of the greatest common divisor of `a` and `b`

```agda
sum-is-multiple-of-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (a +ℕ b)
pr1 (sum-is-multiple-of-gcd-ℕ a b np) = {!!}
pr2 (sum-is-multiple-of-gcd-ℕ a b np) x H = {!!}
```

### The greatest common divisor exists

```agda
abstract
  GCD-ℕ : (a b : ℕ) → minimal-element-ℕ (is-multiple-of-gcd-ℕ a b)
  GCD-ℕ a b = {!!}

gcd-ℕ : ℕ → ℕ → ℕ
gcd-ℕ a b = {!!}

is-multiple-of-gcd-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (gcd-ℕ a b)
is-multiple-of-gcd-gcd-ℕ a b = {!!}

is-lower-bound-gcd-ℕ :
  (a b : ℕ) → is-lower-bound-ℕ (is-multiple-of-gcd-ℕ a b) (gcd-ℕ a b)
is-lower-bound-gcd-ℕ a b = {!!}
```

### `a + b = {!!}

```agda
is-zero-gcd-ℕ :
  (a b : ℕ) → is-zero-ℕ (a +ℕ b) → is-zero-ℕ (gcd-ℕ a b)
is-zero-gcd-ℕ a b p = {!!}

is-zero-gcd-zero-zero-ℕ : is-zero-ℕ (gcd-ℕ zero-ℕ zero-ℕ)
is-zero-gcd-zero-zero-ℕ = {!!}

is-zero-add-is-zero-gcd-ℕ :
  (a b : ℕ) → is-zero-ℕ (gcd-ℕ a b) → is-zero-ℕ (a +ℕ b)
is-zero-add-is-zero-gcd-ℕ a b H = {!!}
```

### If at least one of `a` and `b` is nonzero, then their gcd is nonzero

```agda
is-nonzero-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (a +ℕ b) → is-nonzero-ℕ (gcd-ℕ a b)
is-nonzero-gcd-ℕ a b ne = {!!}

is-successor-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (a +ℕ b) → is-successor-ℕ (gcd-ℕ a b)
is-successor-gcd-ℕ a b ne = {!!}
```

### Any common divisor is also a divisor of the greatest common divisor

```agda
div-gcd-is-common-divisor-ℕ :
  (a b x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x (gcd-ℕ a b)
div-gcd-is-common-divisor-ℕ a b x H with
  is-decidable-is-zero-ℕ (a +ℕ b)
... | inl p = {!!}
... | inr np = {!!}
```

### If every common divisor divides a number `r < gcd a b`, then `r = {!!}

```agda
is-zero-is-common-divisor-le-gcd-ℕ :
  (a b r : ℕ) → le-ℕ r (gcd-ℕ a b) →
  ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x r) → is-zero-ℕ r
is-zero-is-common-divisor-le-gcd-ℕ a b r l d with is-decidable-is-zero-ℕ r
... | inl H = {!!}
... | inr x = {!!}
```

### Any divisor of `gcd a b` is a common divisor of `a` and `b`

```agda
div-left-factor-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x a
div-left-factor-div-gcd-ℕ a b x d with
  is-decidable-is-zero-ℕ (a +ℕ b)
... | inl p = {!!}
... | inr np = {!!}

div-right-factor-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x b
div-right-factor-div-gcd-ℕ a b x d with
  is-decidable-is-zero-ℕ (a +ℕ b)
... | inl p = {!!}
... | inr np = {!!}

is-common-divisor-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → is-common-divisor-ℕ a b x
pr1 (is-common-divisor-div-gcd-ℕ a b x d) = {!!}
pr2 (is-common-divisor-div-gcd-ℕ a b x d) = {!!}
```

### The gcd of `a` and `b` is a common divisor

```agda
div-left-factor-gcd-ℕ : (a b : ℕ) → div-ℕ (gcd-ℕ a b) a
div-left-factor-gcd-ℕ a b = {!!}

div-right-factor-gcd-ℕ : (a b : ℕ) → div-ℕ (gcd-ℕ a b) b
div-right-factor-gcd-ℕ a b = {!!}

is-common-divisor-gcd-ℕ : (a b : ℕ) → is-common-divisor-ℕ a b (gcd-ℕ a b)
is-common-divisor-gcd-ℕ a b = {!!}
```

### The gcd of `a` and `b` is a greatest common divisor

```agda
is-gcd-gcd-ℕ : (a b : ℕ) → is-gcd-ℕ a b (gcd-ℕ a b)
pr1 (is-gcd-gcd-ℕ a b x) = {!!}
pr2 (is-gcd-gcd-ℕ a b x) = {!!}
```

### The gcd is commutative

```agda
is-commutative-gcd-ℕ : (a b : ℕ) → gcd-ℕ a b ＝ gcd-ℕ b a
is-commutative-gcd-ℕ a b = {!!}
```

### If `d` is a common divisor of `a` and `b`, then `kd` is a common divisor of `ka` and `kb`

```agda
preserves-is-common-divisor-mul-ℕ :
  (k a b d : ℕ) → is-common-divisor-ℕ a b d →
  is-common-divisor-ℕ (k *ℕ a) (k *ℕ b) (k *ℕ d)
preserves-is-common-divisor-mul-ℕ k a b d = {!!}

reflects-is-common-divisor-mul-ℕ :
  (k a b d : ℕ) → is-nonzero-ℕ k →
  is-common-divisor-ℕ (k *ℕ a) (k *ℕ b) (k *ℕ d) →
  is-common-divisor-ℕ a b d
reflects-is-common-divisor-mul-ℕ k a b d H = {!!}
```

### `gcd-ℕ 1 b ＝ 1`

```agda
is-one-is-gcd-one-ℕ : {b x : ℕ} → is-gcd-ℕ 1 b x → is-one-ℕ x
is-one-is-gcd-one-ℕ {b} {x} H = {!!}

is-one-gcd-one-ℕ : (b : ℕ) → is-one-ℕ (gcd-ℕ 1 b)
is-one-gcd-one-ℕ b = {!!}
```

### `gcd-ℕ a 1 ＝ 1`

```agda
is-one-is-gcd-one-ℕ' : {a x : ℕ} → is-gcd-ℕ a 1 x → is-one-ℕ x
is-one-is-gcd-one-ℕ' {a} {x} H = {!!}

is-one-gcd-one-ℕ' : (a : ℕ) → is-one-ℕ (gcd-ℕ a 1)
is-one-gcd-one-ℕ' a = {!!}
```

### `gcd-ℕ 0 b ＝ b`

```agda
is-id-is-gcd-zero-ℕ : {b x : ℕ} → gcd-ℕ 0 b ＝ x → x ＝ b
is-id-is-gcd-zero-ℕ {b} {x} H = {!!}
```

### `gcd-ℕ a 0 ＝ a`

```agda
is-id-is-gcd-zero-ℕ' : {a x : ℕ} → gcd-ℕ a 0 ＝ x → x ＝ a
is-id-is-gcd-zero-ℕ' {a} {x} H = {!!}
```

### Consider a common divisor `d` of `a` and `b` and let `e` be a divisor of `d`. Then any divisor of `d/e` is a common divisor of `a/e` and `b/e`

```agda
is-common-divisor-quotients-div-quotient-ℕ :
  {a b d e n : ℕ} → is-nonzero-ℕ e → (H : is-common-divisor-ℕ a b d)
  (K : div-ℕ e d) → div-ℕ n (quotient-div-ℕ e d K) →
  (M : is-common-divisor-ℕ a b e) →
  is-common-divisor-ℕ
    ( quotient-div-ℕ e a (pr1 M))
    ( quotient-div-ℕ e b (pr2 M))
    ( n)
pr1 (is-common-divisor-quotients-div-quotient-ℕ nz H K L M) = {!!}
pr2 (is-common-divisor-quotients-div-quotient-ℕ nz H K L M) = {!!}

simplify-is-common-divisor-quotient-div-ℕ :
  {a b d x : ℕ} → is-nonzero-ℕ d → (H : is-common-divisor-ℕ a b d) →
  is-common-divisor-ℕ
    ( quotient-div-ℕ d a (pr1 H))
    ( quotient-div-ℕ d b (pr2 H))
    ( x) ↔
  is-common-divisor-ℕ a b (x *ℕ d)
pr1 (pr1 (simplify-is-common-divisor-quotient-div-ℕ nz H) K) = {!!}
pr2 (pr1 (simplify-is-common-divisor-quotient-div-ℕ nz H) K) = {!!}
pr1 (pr2 (simplify-is-common-divisor-quotient-div-ℕ nz H) K) = {!!}
pr2 (pr2 (simplify-is-common-divisor-quotient-div-ℕ nz H) K) = {!!}
```

### The greatest common divisor of `a/d` and `b/d` is `gcd(a,b)/d`

```agda
is-gcd-quotient-div-gcd-ℕ :
  {a b d : ℕ} → is-nonzero-ℕ d → (H : is-common-divisor-ℕ a b d) →
  is-gcd-ℕ
    ( quotient-div-ℕ d a (pr1 H))
    ( quotient-div-ℕ d b (pr2 H))
    ( quotient-div-ℕ d
      ( gcd-ℕ a b)
      ( div-gcd-is-common-divisor-ℕ a b d H))
is-gcd-quotient-div-gcd-ℕ {a} {b} {d} nz H x = {!!}
```
