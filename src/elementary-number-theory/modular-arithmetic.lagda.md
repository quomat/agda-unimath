# Modular arithmetic

```agda
module elementary-number-theory.modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.sets
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**Modular arithmetic** is arithmetic of the integers modulo `n`. The integers
modulo `n` have addition, negatives, and multiplication that satisfy many of the
familiar properties of usual arithmetic of the
[integers](elementary-number-theory.integers.md).

Some modular arithmetic was already defined in
`modular-arithmetic-standard-finite-types`. Here we collect those results in a
more convenient format that also includes the integers modulo `0`, i.e., the
integers.

The fact that `ℤ-Mod n` is a [ring](ring-theory.rings.md) for every `n : ℕ` is
recorded in
[`elementary-number-theory.standard-cyclic-rings`](elementary-number-theory.standard-cyclic-rings.md).

```agda
ℤ-Mod : ℕ → UU lzero
ℤ-Mod = {!!}
ℤ-Mod (succ-ℕ k) = {!!}
```

## Important integers modulo k

```agda
zero-ℤ-Mod : (k : ℕ) → ℤ-Mod k
zero-ℤ-Mod = {!!}
zero-ℤ-Mod (succ-ℕ k) = {!!}

is-zero-ℤ-Mod : (k : ℕ) → ℤ-Mod k → UU lzero
is-zero-ℤ-Mod = {!!}

is-nonzero-ℤ-Mod : (k : ℕ) → ℤ-Mod k → UU lzero
is-nonzero-ℤ-Mod = {!!}

neg-one-ℤ-Mod : (k : ℕ) → ℤ-Mod k
neg-one-ℤ-Mod = {!!}
neg-one-ℤ-Mod (succ-ℕ k) = {!!}

one-ℤ-Mod : (k : ℕ) → ℤ-Mod k
one-ℤ-Mod = {!!}
one-ℤ-Mod (succ-ℕ k) = {!!}
```

### The integers modulo k have decidable equality

```agda
has-decidable-equality-ℤ-Mod : (k : ℕ) → has-decidable-equality (ℤ-Mod k)
has-decidable-equality-ℤ-Mod = {!!}
has-decidable-equality-ℤ-Mod (succ-ℕ k) = {!!}
```

### The integers modulo k are a discrete type

```agda
ℤ-Mod-Discrete-Type : (k : ℕ) → Discrete-Type lzero
ℤ-Mod-Discrete-Type = {!!}
ℤ-Mod-Discrete-Type (succ-ℕ k) = {!!}
```

### The integers modulo k form a set

```agda
abstract
  is-set-ℤ-Mod : (k : ℕ) → is-set (ℤ-Mod k)
  is-set-ℤ-Mod = {!!}

ℤ-Mod-Set : (k : ℕ) → Set lzero
ℤ-Mod-Set = {!!}
pr2 (ℤ-Mod-Set k) = {!!}
```

### The types `ℤ-Mod k` are finite for nonzero natural numbers `k`

```agda
abstract
  is-finite-ℤ-Mod : {k : ℕ} → is-nonzero-ℕ k → is-finite (ℤ-Mod k)
  is-finite-ℤ-Mod = {!!}

ℤ-Mod-𝔽 : (k : ℕ) → is-nonzero-ℕ k → 𝔽 lzero
ℤ-Mod-𝔽 = {!!}
pr2 (ℤ-Mod-𝔽 k H) = {!!}
```

## The inclusion of the integers modulo k into ℤ

```agda
int-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ
int-ℤ-Mod = {!!}
int-ℤ-Mod (succ-ℕ k) x = {!!}

is-injective-int-ℤ-Mod : (k : ℕ) → is-injective (int-ℤ-Mod k)
is-injective-int-ℤ-Mod = {!!}
is-injective-int-ℤ-Mod (succ-ℕ k) = {!!}

is-zero-int-zero-ℤ-Mod : (k : ℕ) → is-zero-ℤ (int-ℤ-Mod k (zero-ℤ-Mod k))
is-zero-int-zero-ℤ-Mod = {!!}
is-zero-int-zero-ℤ-Mod (succ-ℕ k) = {!!}

int-ℤ-Mod-bounded :
  (k : ℕ) → (x : ℤ-Mod (succ-ℕ k)) →
  leq-ℤ (int-ℤ-Mod (succ-ℕ k) x) (int-ℕ (succ-ℕ k))
int-ℤ-Mod-bounded = {!!}
int-ℤ-Mod-bounded (succ-ℕ k) (inl x) = {!!}
int-ℤ-Mod-bounded (succ-ℕ k) (inr x) = {!!}
```

## The successor and predecessor functions on the integers modulo k

```agda
succ-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
succ-ℤ-Mod = {!!}
succ-ℤ-Mod (succ-ℕ k) = {!!}

ℤ-Mod-Type-With-Endomorphism : (k : ℕ) → Type-With-Endomorphism lzero
ℤ-Mod-Type-With-Endomorphism = {!!}
pr2 (ℤ-Mod-Type-With-Endomorphism k) = {!!}

abstract
  is-equiv-succ-ℤ-Mod : (k : ℕ) → is-equiv (succ-ℤ-Mod k)
  is-equiv-succ-ℤ-Mod = {!!}

equiv-succ-ℤ-Mod : (k : ℕ) → ℤ-Mod k ≃ ℤ-Mod k
equiv-succ-ℤ-Mod = {!!}
pr2 (equiv-succ-ℤ-Mod k) = {!!}

pred-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
pred-ℤ-Mod = {!!}
pred-ℤ-Mod (succ-ℕ k) = {!!}

is-section-pred-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → succ-ℤ-Mod k (pred-ℤ-Mod k x) ＝ x
is-section-pred-ℤ-Mod = {!!}
is-section-pred-ℤ-Mod (succ-ℕ k) = {!!}

is-retraction-pred-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → pred-ℤ-Mod k (succ-ℤ-Mod k x) ＝ x
is-retraction-pred-ℤ-Mod = {!!}
is-retraction-pred-ℤ-Mod (succ-ℕ k) = {!!}

abstract
  is-equiv-pred-ℤ-Mod : (k : ℕ) → is-equiv (pred-ℤ-Mod k)
  is-equiv-pred-ℤ-Mod = {!!}

equiv-pred-ℤ-Mod : (k : ℕ) → ℤ-Mod k ≃ ℤ-Mod k
equiv-pred-ℤ-Mod = {!!}
pr2 (equiv-pred-ℤ-Mod k) = {!!}
```

## Addition on the integers modulo k

```agda
add-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
add-ℤ-Mod = {!!}
add-ℤ-Mod (succ-ℕ k) = {!!}

add-ℤ-Mod' : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
add-ℤ-Mod' = {!!}

ap-add-ℤ-Mod :
  (k : ℕ) {x x' y y' : ℤ-Mod k} →
  x ＝ x' → y ＝ y' → add-ℤ-Mod k x y ＝ add-ℤ-Mod k x' y'
ap-add-ℤ-Mod = {!!}

abstract
  is-equiv-left-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → is-equiv (add-ℤ-Mod k x)
  is-equiv-left-add-ℤ-Mod = {!!}

equiv-left-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → ℤ-Mod k ≃ ℤ-Mod k
equiv-left-add-ℤ-Mod = {!!}
pr2 (equiv-left-add-ℤ-Mod k x) = {!!}

abstract
  is-equiv-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → is-equiv (add-ℤ-Mod' k x)
  is-equiv-add-ℤ-Mod' = {!!}

equiv-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → ℤ-Mod k ≃ ℤ-Mod k
equiv-add-ℤ-Mod' = {!!}
pr2 (equiv-add-ℤ-Mod' k x) = {!!}

is-injective-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → is-injective (add-ℤ-Mod k x)
is-injective-add-ℤ-Mod = {!!}
is-injective-add-ℤ-Mod (succ-ℕ k) = {!!}

is-injective-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → is-injective (add-ℤ-Mod' k x)
is-injective-add-ℤ-Mod' = {!!}
is-injective-add-ℤ-Mod' (succ-ℕ k) = {!!}
```

## The negative of an integer modulo k

```agda
neg-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
neg-ℤ-Mod = {!!}
neg-ℤ-Mod (succ-ℕ k) = {!!}

abstract
  is-equiv-neg-ℤ-Mod : (k : ℕ) → is-equiv (neg-ℤ-Mod k)
  is-equiv-neg-ℤ-Mod = {!!}

equiv-neg-ℤ-Mod : (k : ℕ) → ℤ-Mod k ≃ ℤ-Mod k
equiv-neg-ℤ-Mod = {!!}
pr2 (equiv-neg-ℤ-Mod k) = {!!}
```

## Laws of addition modulo k

```agda
associative-add-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  add-ℤ-Mod k (add-ℤ-Mod k x y) z ＝ add-ℤ-Mod k x (add-ℤ-Mod k y z)
associative-add-ℤ-Mod = {!!}
associative-add-ℤ-Mod (succ-ℕ k) = {!!}

commutative-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) → add-ℤ-Mod k x y ＝ add-ℤ-Mod k y x
commutative-add-ℤ-Mod = {!!}
commutative-add-ℤ-Mod (succ-ℕ k) = {!!}

left-unit-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → add-ℤ-Mod k (zero-ℤ-Mod k) x ＝ x
left-unit-law-add-ℤ-Mod = {!!}
left-unit-law-add-ℤ-Mod (succ-ℕ k) = {!!}

right-unit-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → add-ℤ-Mod k x (zero-ℤ-Mod k) ＝ x
right-unit-law-add-ℤ-Mod = {!!}
right-unit-law-add-ℤ-Mod (succ-ℕ k) = {!!}

left-inverse-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → add-ℤ-Mod k (neg-ℤ-Mod k x) x ＝ zero-ℤ-Mod k
left-inverse-law-add-ℤ-Mod = {!!}
left-inverse-law-add-ℤ-Mod (succ-ℕ k) = {!!}

right-inverse-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → add-ℤ-Mod k x (neg-ℤ-Mod k x) ＝ zero-ℤ-Mod k
right-inverse-law-add-ℤ-Mod = {!!}
right-inverse-law-add-ℤ-Mod (succ-ℕ k) = {!!}

left-successor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  add-ℤ-Mod k (succ-ℤ-Mod k x) y ＝ succ-ℤ-Mod k (add-ℤ-Mod k x y)
left-successor-law-add-ℤ-Mod = {!!}
left-successor-law-add-ℤ-Mod (succ-ℕ k) = {!!}

right-successor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  add-ℤ-Mod k x (succ-ℤ-Mod k y) ＝ succ-ℤ-Mod k (add-ℤ-Mod k x y)
right-successor-law-add-ℤ-Mod = {!!}
right-successor-law-add-ℤ-Mod (succ-ℕ k) = {!!}

left-predecessor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  add-ℤ-Mod k (pred-ℤ-Mod k x) y ＝ pred-ℤ-Mod k (add-ℤ-Mod k x y)
left-predecessor-law-add-ℤ-Mod = {!!}
left-predecessor-law-add-ℤ-Mod (succ-ℕ k) = {!!}

right-predecessor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  add-ℤ-Mod k x (pred-ℤ-Mod k y) ＝ pred-ℤ-Mod k (add-ℤ-Mod k x y)
right-predecessor-law-add-ℤ-Mod = {!!}
right-predecessor-law-add-ℤ-Mod (succ-ℕ k) = {!!}

is-left-add-one-succ-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → succ-ℤ-Mod k x ＝ add-ℤ-Mod k (one-ℤ-Mod k) x
is-left-add-one-succ-ℤ-Mod = {!!}
is-left-add-one-succ-ℤ-Mod (succ-ℕ k) = {!!}

is-left-add-one-succ-ℤ-Mod' :
  (k : ℕ) (x : ℤ-Mod k) → succ-ℤ-Mod k x ＝ add-ℤ-Mod k x (one-ℤ-Mod k)
is-left-add-one-succ-ℤ-Mod' = {!!}
is-left-add-one-succ-ℤ-Mod' (succ-ℕ k) = {!!}

is-left-add-neg-one-pred-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → pred-ℤ-Mod k x ＝ add-ℤ-Mod k (neg-one-ℤ-Mod k) x
is-left-add-neg-one-pred-ℤ-Mod = {!!}
is-left-add-neg-one-pred-ℤ-Mod (succ-ℕ k) = {!!}

is-left-add-neg-one-pred-ℤ-Mod' :
  (k : ℕ) (x : ℤ-Mod k) → pred-ℤ-Mod k x ＝ add-ℤ-Mod k x (neg-one-ℤ-Mod k)
is-left-add-neg-one-pred-ℤ-Mod' = {!!}
is-left-add-neg-one-pred-ℤ-Mod' (succ-ℕ k) = {!!}
```

## Multiplication modulo k

```agda
mul-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
mul-ℤ-Mod = {!!}
mul-ℤ-Mod (succ-ℕ k) = {!!}

mul-ℤ-Mod' : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
mul-ℤ-Mod' = {!!}

ap-mul-ℤ-Mod :
  (k : ℕ) {x x' y y' : ℤ-Mod k} →
  x ＝ x' → y ＝ y' → mul-ℤ-Mod k x y ＝ mul-ℤ-Mod k x' y'
ap-mul-ℤ-Mod = {!!}
```

## Laws of multiplication modulo k

```agda
associative-mul-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  mul-ℤ-Mod k (mul-ℤ-Mod k x y) z ＝ mul-ℤ-Mod k x (mul-ℤ-Mod k y z)
associative-mul-ℤ-Mod = {!!}
associative-mul-ℤ-Mod (succ-ℕ k) = {!!}

commutative-mul-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) → mul-ℤ-Mod k x y ＝ mul-ℤ-Mod k y x
commutative-mul-ℤ-Mod = {!!}
commutative-mul-ℤ-Mod (succ-ℕ k) = {!!}

left-unit-law-mul-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → mul-ℤ-Mod k (one-ℤ-Mod k) x ＝ x
left-unit-law-mul-ℤ-Mod = {!!}
left-unit-law-mul-ℤ-Mod (succ-ℕ k) = {!!}

right-unit-law-mul-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → mul-ℤ-Mod k x (one-ℤ-Mod k) ＝ x
right-unit-law-mul-ℤ-Mod = {!!}
right-unit-law-mul-ℤ-Mod (succ-ℕ k) = {!!}

left-distributive-mul-add-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  ( mul-ℤ-Mod k x (add-ℤ-Mod k y z)) ＝
  ( add-ℤ-Mod k (mul-ℤ-Mod k x y) (mul-ℤ-Mod k x z))
left-distributive-mul-add-ℤ-Mod = {!!}
left-distributive-mul-add-ℤ-Mod (succ-ℕ k) = {!!}

right-distributive-mul-add-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  ( mul-ℤ-Mod k (add-ℤ-Mod k x y) z) ＝
  ( add-ℤ-Mod k (mul-ℤ-Mod k x z) (mul-ℤ-Mod k y z))
right-distributive-mul-add-ℤ-Mod = {!!}
right-distributive-mul-add-ℤ-Mod (succ-ℕ k) = {!!}

is-left-mul-neg-one-neg-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → neg-ℤ-Mod k x ＝ mul-ℤ-Mod k (neg-one-ℤ-Mod k) x
is-left-mul-neg-one-neg-ℤ-Mod = {!!}
is-left-mul-neg-one-neg-ℤ-Mod (succ-ℕ k) = {!!}

is-left-mul-neg-one-neg-ℤ-Mod' :
  (k : ℕ) (x : ℤ-Mod k) → neg-ℤ-Mod k x ＝ mul-ℤ-Mod k x (neg-one-ℤ-Mod k)
is-left-mul-neg-one-neg-ℤ-Mod' = {!!}
is-left-mul-neg-one-neg-ℤ-Mod' (succ-ℕ k) = {!!}
```

## Congruence classes of integers modulo k

```agda
mod-ℕ : (k : ℕ) → ℕ → ℤ-Mod k
mod-ℕ = {!!}
mod-ℕ (succ-ℕ k) x = {!!}

mod-ℤ : (k : ℕ) → ℤ → ℤ-Mod k
mod-ℤ = {!!}
mod-ℤ (succ-ℕ k) (inl x) = {!!}
mod-ℤ (succ-ℕ k) (inr (inl x)) = {!!}
mod-ℤ (succ-ℕ k) (inr (inr x)) = {!!}

mod-int-ℕ : (k x : ℕ) → mod-ℤ k (int-ℕ x) ＝ mod-ℕ k x
mod-int-ℕ = {!!}
mod-int-ℕ (succ-ℕ k) zero-ℕ = {!!}
mod-int-ℕ (succ-ℕ k) (succ-ℕ x) = {!!}
```

## Preservation laws of congruence classes

```agda
mod-zero-ℕ : (k : ℕ) → mod-ℕ k zero-ℕ ＝ zero-ℤ-Mod k
mod-zero-ℕ = {!!}
mod-zero-ℕ (succ-ℕ k) = {!!}

preserves-successor-mod-ℕ :
  (k x : ℕ) → mod-ℕ k (succ-ℕ x) ＝ succ-ℤ-Mod k (mod-ℕ k x)
preserves-successor-mod-ℕ = {!!}
preserves-successor-mod-ℕ zero-ℕ (succ-ℕ x) = {!!}
preserves-successor-mod-ℕ (succ-ℕ k) x = {!!}

mod-refl-ℕ : (k : ℕ) → mod-ℕ k k ＝ zero-ℤ-Mod k
mod-refl-ℕ = {!!}
mod-refl-ℕ (succ-ℕ k) = {!!}

mod-zero-ℤ : (k : ℕ) → mod-ℤ k zero-ℤ ＝ zero-ℤ-Mod k
mod-zero-ℤ = {!!}
mod-zero-ℤ (succ-ℕ k) = {!!}

mod-one-ℤ : (k : ℕ) → mod-ℤ k one-ℤ ＝ one-ℤ-Mod k
mod-one-ℤ = {!!}
mod-one-ℤ (succ-ℕ k) = {!!}

mod-neg-one-ℤ : (k : ℕ) → mod-ℤ k neg-one-ℤ ＝ neg-one-ℤ-Mod k
mod-neg-one-ℤ = {!!}
mod-neg-one-ℤ (succ-ℕ k) = {!!}

preserves-successor-mod-ℤ :
  (k : ℕ) (x : ℤ) → mod-ℤ k (succ-ℤ x) ＝ succ-ℤ-Mod k (mod-ℤ k x)
preserves-successor-mod-ℤ = {!!}
preserves-successor-mod-ℤ (succ-ℕ k) (inl zero-ℕ) = {!!}
preserves-successor-mod-ℤ (succ-ℕ k) (inl (succ-ℕ x)) = {!!}
preserves-successor-mod-ℤ (succ-ℕ k) (inr (inl star)) = {!!}
preserves-successor-mod-ℤ (succ-ℕ k) (inr (inr x)) = {!!}

preserves-predecessor-mod-ℤ :
  (k : ℕ) (x : ℤ) → mod-ℤ k (pred-ℤ x) ＝ pred-ℤ-Mod k (mod-ℤ k x)
preserves-predecessor-mod-ℤ = {!!}
preserves-predecessor-mod-ℤ (succ-ℕ k) (inl x) = {!!}
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inl star)) = {!!}
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) = {!!}
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) = {!!}

preserves-add-mod-ℤ :
  (k : ℕ) (x y : ℤ) →
  mod-ℤ k (x +ℤ y) ＝ add-ℤ-Mod k (mod-ℤ k x) (mod-ℤ k y)
preserves-add-mod-ℤ = {!!}
preserves-add-mod-ℤ (succ-ℕ k) (inl zero-ℕ) y = {!!}
preserves-add-mod-ℤ (succ-ℕ k) (inl (succ-ℕ x)) y = {!!}
preserves-add-mod-ℤ (succ-ℕ k) (inr (inl star)) y = {!!}
preserves-add-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) y = {!!}
preserves-add-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) y = {!!}

preserves-neg-mod-ℤ :
  (k : ℕ) (x : ℤ) → mod-ℤ k (neg-ℤ x) ＝ neg-ℤ-Mod k (mod-ℤ k x)
preserves-neg-mod-ℤ = {!!}
preserves-neg-mod-ℤ (succ-ℕ k) x = {!!}

preserves-mul-mod-ℤ :
  (k : ℕ) (x y : ℤ) →
  mod-ℤ k (x *ℤ y) ＝ mul-ℤ-Mod k (mod-ℤ k x) (mod-ℤ k y)
preserves-mul-mod-ℤ = {!!}
preserves-mul-mod-ℤ (succ-ℕ k) (inl zero-ℕ) y = {!!}
preserves-mul-mod-ℤ (succ-ℕ k) (inl (succ-ℕ x)) y = {!!}
preserves-mul-mod-ℤ (succ-ℕ k) (inr (inl star)) y = {!!}
preserves-mul-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) y = {!!}
preserves-mul-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) y = {!!}
```

```agda
cong-int-mod-ℕ :
  (k x : ℕ) → cong-ℤ (int-ℕ k) (int-ℤ-Mod k (mod-ℕ k x)) (int-ℕ x)
cong-int-mod-ℕ = {!!}
cong-int-mod-ℕ (succ-ℕ k) x = {!!}

cong-int-mod-ℤ :
  (k : ℕ) (x : ℤ) → cong-ℤ (int-ℕ k) (int-ℤ-Mod k (mod-ℤ k x)) x
cong-int-mod-ℤ = {!!}
cong-int-mod-ℤ (succ-ℕ k) (inl x) = {!!}
cong-int-mod-ℤ (succ-ℕ k) (inr (inl star)) = {!!}
cong-int-mod-ℤ (succ-ℕ k) (inr (inr x)) = {!!}

cong-eq-mod-ℤ :
  (k : ℕ) (x y : ℤ) → mod-ℤ k x ＝ mod-ℤ k y → cong-ℤ (int-ℕ k) x y
cong-eq-mod-ℤ = {!!}

eq-cong-int-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  cong-ℤ (int-ℕ k) (int-ℤ-Mod k x) (int-ℤ-Mod k y) → x ＝ y
eq-cong-int-ℤ-Mod = {!!}
eq-cong-int-ℤ-Mod (succ-ℕ k) x y H = {!!}

eq-mod-cong-ℤ :
  (k : ℕ) (x y : ℤ) → cong-ℤ (int-ℕ k) x y → mod-ℤ k x ＝ mod-ℤ k y
eq-mod-cong-ℤ = {!!}

is-zero-mod-div-ℤ :
  (k : ℕ) (x : ℤ) → div-ℤ (int-ℕ k) x → is-zero-ℤ-Mod k (mod-ℤ k x)
is-zero-mod-div-ℤ = {!!}
is-zero-mod-div-ℤ (succ-ℕ k) x H = {!!}

div-is-zero-mod-ℤ :
  (k : ℕ) (x : ℤ) → is-zero-ℤ-Mod k (mod-ℤ k x) → div-ℤ (int-ℕ k) x
div-is-zero-mod-ℤ = {!!}
div-is-zero-mod-ℤ (succ-ℕ k) x p = {!!}

is-section-int-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → mod-ℤ k (int-ℤ-Mod k x) ＝ x
is-section-int-ℤ-Mod = {!!}

is-one-is-fixed-point-succ-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → succ-ℤ-Mod k x ＝ x → is-one-ℕ k
is-one-is-fixed-point-succ-ℤ-Mod = {!!}

has-no-fixed-points-succ-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → is-not-one-ℕ k → succ-ℤ-Mod k x ≠ x
has-no-fixed-points-succ-ℤ-Mod = {!!}

has-no-fixed-points-succ-Fin :
  {k : ℕ} (x : Fin k) → is-not-one-ℕ k → succ-Fin k x ≠ x
has-no-fixed-points-succ-Fin = {!!}
```

### Divisibility is decidable

```agda
is-decidable-div-ℤ : (d x : ℤ) → is-decidable (div-ℤ d x)
is-decidable-div-ℤ = {!!}
```

### `mod-ℤ` is surjective

```agda
is-surjective-succ-Fin-comp-mod-succ-ℕ :
  (n : ℕ) → is-surjective (succ-Fin (succ-ℕ n) ∘ mod-succ-ℕ n)
is-surjective-succ-Fin-comp-mod-succ-ℕ = {!!}

is-surjective-mod-ℤ : (n : ℕ) → is-surjective (mod-ℤ n)
is-surjective-mod-ℤ = {!!}
is-surjective-mod-ℤ (succ-ℕ n) = {!!}
```
