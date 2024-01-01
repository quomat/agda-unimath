# The integers

```agda
module elementary-number-theory.integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The type of integers is an extension of the type of natural numbers including
negative whole numbers.

## Definitions

### The type of integers

```agda
ℤ : UU lzero
ℤ = {!!}

{-# BUILTIN INTEGER ℤ #-}
```

### Inclusion of the negative integers

```agda
in-neg : ℕ → ℤ
in-neg = {!!}

neg-one-ℤ : ℤ
neg-one-ℤ = {!!}

is-neg-one-ℤ : ℤ → UU lzero
is-neg-one-ℤ = {!!}
```

### Zero

```agda
zero-ℤ : ℤ
zero-ℤ = {!!}

is-zero-ℤ : ℤ → UU lzero
is-zero-ℤ = {!!}
```

### Inclusion of the positive integers

```agda
in-pos : ℕ → ℤ
in-pos = {!!}

one-ℤ : ℤ
one-ℤ = {!!}

is-one-ℤ : ℤ → UU lzero
is-one-ℤ = {!!}
```

### Inclusion of the natural numbers

```agda
int-ℕ : ℕ → ℤ
int-ℕ = {!!}
int-ℕ (succ-ℕ n) = {!!}

is-injective-int-ℕ : is-injective int-ℕ
is-injective-int-ℕ = {!!}
is-injective-int-ℕ {succ-ℕ x} {succ-ℕ y} refl = {!!}
```

### Induction principle on the type of integers

```agda
ind-ℤ :
  {l : Level} (P : ℤ → UU l) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ = {!!}
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) = {!!}
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = {!!}
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = {!!}
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) = {!!}
```

### The successor and predecessor functions on ℤ

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ = {!!}
succ-ℤ (inl (succ-ℕ x)) = {!!}
succ-ℤ (inr (inl star)) = {!!}
succ-ℤ (inr (inr x)) = {!!}

pred-ℤ : ℤ → ℤ
pred-ℤ = {!!}
pred-ℤ (inr (inl star)) = {!!}
pred-ℤ (inr (inr zero-ℕ)) = {!!}
pred-ℤ (inr (inr (succ-ℕ x))) = {!!}

ℤ-Type-With-Endomorphism : Type-With-Endomorphism lzero
ℤ-Type-With-Endomorphism = {!!}
pr2 ℤ-Type-With-Endomorphism = {!!}
```

### The negative of an integer

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ = {!!}
neg-ℤ (inr (inl star)) = {!!}
neg-ℤ (inr (inr x)) = {!!}
```

## Properties

### The type of integers is a set

```agda
is-set-ℤ : is-set ℤ
is-set-ℤ = {!!}

ℤ-Set : Set lzero
ℤ-Set = {!!}
pr2 ℤ-Set = {!!}
```

### The successor and predecessor functions on ℤ are mutual inverses

```agda
abstract
  is-retraction-pred-ℤ : (pred-ℤ ∘ succ-ℤ) ~ id
  is-retraction-pred-ℤ = {!!}

  is-section-pred-ℤ : (succ-ℤ ∘ pred-ℤ) ~ id
  is-section-pred-ℤ = {!!}

abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  pr1 (pr1 is-equiv-succ-ℤ) = {!!}

equiv-succ-ℤ : ℤ ≃ ℤ
equiv-succ-ℤ = {!!}
pr2 equiv-succ-ℤ = {!!}

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  pr1 (pr1 is-equiv-pred-ℤ) = {!!}

equiv-pred-ℤ : ℤ ≃ ℤ
equiv-pred-ℤ = {!!}
pr2 equiv-pred-ℤ = {!!}
```

### The successor function on ℤ is injective and has no fixed points

```agda
is-injective-succ-ℤ : is-injective succ-ℤ
is-injective-succ-ℤ = {!!}

has-no-fixed-points-succ-ℤ : (x : ℤ) → succ-ℤ x ≠ x
has-no-fixed-points-succ-ℤ (inl zero-ℕ) ()
has-no-fixed-points-succ-ℤ (inl (succ-ℕ x)) ()
has-no-fixed-points-succ-ℤ (inr (inl star)) ()
```

### The negative function is an involution

```agda
neg-neg-ℤ : (neg-ℤ ∘ neg-ℤ) ~ id
neg-neg-ℤ = {!!}
neg-neg-ℤ (inr (inl star)) = {!!}
neg-neg-ℤ (inr (inr n)) = {!!}

abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  pr1 (pr1 is-equiv-neg-ℤ) = {!!}

equiv-neg-ℤ : ℤ ≃ ℤ
equiv-neg-ℤ = {!!}
pr2 equiv-neg-ℤ = {!!}

abstract
  is-emb-neg-ℤ : is-emb neg-ℤ
  is-emb-neg-ℤ = {!!}

emb-neg-ℤ : ℤ ↪ ℤ
emb-neg-ℤ = {!!}
pr2 emb-neg-ℤ = {!!}

neg-pred-ℤ : (k : ℤ) → neg-ℤ (pred-ℤ k) ＝ succ-ℤ (neg-ℤ k)
neg-pred-ℤ = {!!}
neg-pred-ℤ (inr (inl star)) = {!!}
neg-pred-ℤ (inr (inr zero-ℕ)) = {!!}
neg-pred-ℤ (inr (inr (succ-ℕ x))) = {!!}

neg-succ-ℤ : (x : ℤ) → neg-ℤ (succ-ℤ x) ＝ pred-ℤ (neg-ℤ x)
neg-succ-ℤ = {!!}
neg-succ-ℤ (inl (succ-ℕ x)) = {!!}
neg-succ-ℤ (inr (inl star)) = {!!}
neg-succ-ℤ (inr (inr x)) = {!!}

pred-neg-ℤ :
  (k : ℤ) → pred-ℤ (neg-ℤ k) ＝ neg-ℤ (succ-ℤ k)
pred-neg-ℤ = {!!}
pred-neg-ℤ (inl (succ-ℕ x)) = {!!}
pred-neg-ℤ (inr (inl star)) = {!!}
pred-neg-ℤ (inr (inr x)) = {!!}
```

### Nonnegative integers

```agda
is-nonnegative-ℤ : ℤ → UU lzero
is-nonnegative-ℤ = {!!}
is-nonnegative-ℤ (inr k) = {!!}

is-nonnegative-eq-ℤ :
  {x y : ℤ} → x ＝ y → is-nonnegative-ℤ x → is-nonnegative-ℤ y
is-nonnegative-eq-ℤ = {!!}

is-zero-is-nonnegative-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonnegative-ℤ = {!!}

is-nonnegative-succ-ℤ :
  (k : ℤ) → is-nonnegative-ℤ k → is-nonnegative-ℤ (succ-ℤ k)
is-nonnegative-succ-ℤ = {!!}
is-nonnegative-succ-ℤ (inr (inr x)) p = {!!}

is-prop-is-nonnegative-ℤ : (x : ℤ) → is-prop (is-nonnegative-ℤ x)
is-prop-is-nonnegative-ℤ = {!!}
is-prop-is-nonnegative-ℤ (inr x) = {!!}

is-nonnegative-ℤ-Prop : ℤ → Prop lzero
is-nonnegative-ℤ-Prop = {!!}
pr2 (is-nonnegative-ℤ-Prop x) = {!!}
```

### The positive integers

```agda
is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ = {!!}
is-positive-ℤ (inr (inl x)) = {!!}
is-positive-ℤ (inr (inr x)) = {!!}

is-prop-is-positive-ℤ : (x : ℤ) → is-prop (is-positive-ℤ x)
is-prop-is-positive-ℤ = {!!}
is-prop-is-positive-ℤ (inr (inl x)) = {!!}
is-prop-is-positive-ℤ (inr (inr x)) = {!!}

is-positive-ℤ-Prop : ℤ → Prop lzero
is-positive-ℤ-Prop = {!!}
pr2 (is-positive-ℤ-Prop x) = {!!}

is-set-is-positive-ℤ : (x : ℤ) → is-set (is-positive-ℤ x)
is-set-is-positive-ℤ = {!!}
is-set-is-positive-ℤ (inr (inl x)) = {!!}
is-set-is-positive-ℤ (inr (inr x)) = {!!}

is-positive-ℤ-Set : ℤ → Set lzero
is-positive-ℤ-Set = {!!}
pr2 (is-positive-ℤ-Set z) = {!!}

positive-ℤ : UU lzero
positive-ℤ = {!!}

is-set-positive-ℤ : is-set positive-ℤ
is-set-positive-ℤ = {!!}

positive-ℤ-Set : Set lzero
positive-ℤ-Set = {!!}
pr2 positive-ℤ-Set = {!!}

int-positive-ℤ : positive-ℤ → ℤ
int-positive-ℤ = {!!}

is-positive-int-positive-ℤ :
  (x : positive-ℤ) → is-positive-ℤ (int-positive-ℤ x)
is-positive-int-positive-ℤ = {!!}

is-nonnegative-is-positive-ℤ : {x : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ x
is-nonnegative-is-positive-ℤ = {!!}

is-positive-eq-ℤ : {x y : ℤ} → x ＝ y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ = {!!}

is-positive-one-ℤ : is-positive-ℤ one-ℤ
is-positive-one-ℤ = {!!}

one-positive-ℤ : positive-ℤ
one-positive-ℤ = {!!}
pr2 one-positive-ℤ = {!!}

is-positive-succ-ℤ : {x : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-ℤ = {!!}
is-positive-succ-ℤ {inr (inr x)} H = {!!}

is-positive-int-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
is-positive-int-ℕ = {!!}
is-positive-int-ℕ (succ-ℕ x) H = {!!}
```

### Properties of nonnegative integers

```agda
nonnegative-ℤ : UU lzero
nonnegative-ℤ = {!!}

int-nonnegative-ℤ : nonnegative-ℤ → ℤ
int-nonnegative-ℤ = {!!}

is-nonnegative-int-nonnegative-ℤ :
  (x : nonnegative-ℤ) → is-nonnegative-ℤ (int-nonnegative-ℤ x)
is-nonnegative-int-nonnegative-ℤ = {!!}

is-injective-int-nonnegative-ℤ : is-injective int-nonnegative-ℤ
is-injective-int-nonnegative-ℤ = {!!}

is-nonnegative-int-ℕ : (n : ℕ) → is-nonnegative-ℤ (int-ℕ n)
is-nonnegative-int-ℕ = {!!}
is-nonnegative-int-ℕ (succ-ℕ n) = {!!}

nonnegative-int-ℕ : ℕ → nonnegative-ℤ
nonnegative-int-ℕ = {!!}
pr2 (nonnegative-int-ℕ n) = {!!}

nat-nonnegative-ℤ : nonnegative-ℤ → ℕ
nat-nonnegative-ℤ = {!!}
nat-nonnegative-ℤ (pair (inr (inr x)) H) = {!!}

is-section-nat-nonnegative-ℤ :
  (x : nonnegative-ℤ) → nonnegative-int-ℕ (nat-nonnegative-ℤ x) ＝ x
is-section-nat-nonnegative-ℤ = {!!}
is-section-nat-nonnegative-ℤ (pair (inr (inr x)) star) = {!!}

is-retraction-nat-nonnegative-ℤ :
  (n : ℕ) → nat-nonnegative-ℤ (nonnegative-int-ℕ n) ＝ n
is-retraction-nat-nonnegative-ℤ = {!!}
is-retraction-nat-nonnegative-ℤ (succ-ℕ n) = {!!}

is-equiv-nat-nonnegative-ℤ : is-equiv nat-nonnegative-ℤ
pr1 (pr1 is-equiv-nat-nonnegative-ℤ) = {!!}
pr2 (pr1 is-equiv-nat-nonnegative-ℤ) = {!!}
pr1 (pr2 is-equiv-nat-nonnegative-ℤ) = {!!}
pr2 (pr2 is-equiv-nat-nonnegative-ℤ) = {!!}

is-equiv-nonnegative-int-ℕ : is-equiv nonnegative-int-ℕ
pr1 (pr1 is-equiv-nonnegative-int-ℕ) = {!!}
pr2 (pr1 is-equiv-nonnegative-int-ℕ) = {!!}
pr1 (pr2 is-equiv-nonnegative-int-ℕ) = {!!}
pr2 (pr2 is-equiv-nonnegative-int-ℕ) = {!!}

equiv-nonnegative-int-ℕ : ℕ ≃ nonnegative-ℤ
equiv-nonnegative-int-ℕ = {!!}
pr2 equiv-nonnegative-int-ℕ = {!!}

is-injective-nonnegative-int-ℕ : is-injective nonnegative-int-ℕ
is-injective-nonnegative-int-ℕ = {!!}

decide-is-nonnegative-ℤ :
  {x : ℤ} → (is-nonnegative-ℤ x) + (is-nonnegative-ℤ (neg-ℤ x))
decide-is-nonnegative-ℤ = {!!}
decide-is-nonnegative-ℤ {inr x} = {!!}

is-zero-is-nonnegative-neg-is-nonnegative-ℤ :
  (x : ℤ) → (is-nonnegative-ℤ x) → (is-nonnegative-ℤ (neg-ℤ x)) → is-zero-ℤ x
is-zero-is-nonnegative-neg-is-nonnegative-ℤ = {!!}
```

```agda
succ-int-ℕ : (x : ℕ) → succ-ℤ (int-ℕ x) ＝ int-ℕ (succ-ℕ x)
succ-int-ℕ = {!!}
succ-int-ℕ (succ-ℕ x) = {!!}
```

```agda
is-injective-neg-ℤ : is-injective neg-ℤ
is-injective-neg-ℤ = {!!}

is-zero-is-zero-neg-ℤ : (x : ℤ) → is-zero-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-zero-neg-ℤ = {!!}
```

## See also

- We show in
  [`structured-types.initial-pointed-type-equipped-with-automorphism`](structured-types.initial-pointed-type-equipped-with-automorphism.md)
  that ℤ is the initial pointed type equipped with an automorphism.
- The group of integers is constructed in
  [`elementary-number-theory.group-of-integers`](elementary-number-theory.group-of-integers.md).
