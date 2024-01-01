# The standard finite types

```agda
module univalent-combinatorics.standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.noncontractible-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The standard finite types are defined inductively by `Fin 0 := {!!}
`Fin (n+1) := {!!}
`inr` injection) is the _top_ element, when `Fin n` is considered as an initial
segment of `ℕ`.

## Definition

### The standard finite types in universe level zero

```agda
Fin-Set : ℕ → Set lzero
Fin-Set zero-ℕ = {!!}
Fin-Set (succ-ℕ n) = {!!}

Fin : ℕ → UU lzero
Fin n = {!!}

is-set-Fin : (n : ℕ) → is-set (Fin n)
is-set-Fin n = {!!}

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin = {!!}

emb-inl-Fin : (k : ℕ) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-inl-Fin k) = {!!}
pr2 (emb-inl-Fin k) = {!!}

neg-one-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-one-Fin k = {!!}

is-neg-one-Fin : (k : ℕ) → Fin k → UU lzero
is-neg-one-Fin (succ-ℕ k) x = {!!}

neg-two-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-two-Fin zero-ℕ = {!!}
neg-two-Fin (succ-ℕ k) = {!!}

is-inl-Fin : (k : ℕ) → Fin (succ-ℕ k) → UU lzero
is-inl-Fin k x = {!!}

is-neg-one-is-not-inl-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  ¬ (is-inl-Fin k x) → is-neg-one-Fin (succ-ℕ k) x
is-neg-one-is-not-inl-Fin = {!!}

inr-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
inr-Fin (succ-ℕ k) (inl x) = {!!}
inr-Fin (succ-ℕ k) (inr star) = {!!}

neq-inl-Fin-inr-Fin :
  (n : ℕ) → (k : Fin n) → inl-Fin n k ≠ inr-Fin n k
neq-inl-Fin-inr-Fin = {!!}

neq-inr-Fin-inl-Fin :
  (n : ℕ) → (k : Fin n) → inr-Fin n k ≠ inl-Fin n k
neq-inr-Fin-inl-Fin = {!!}
```

### The standard finite types in an arbitrary universe

```agda
raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = {!!}

compute-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
compute-raise-Fin l k = {!!}

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = {!!}

raise-Fin-Set : (l : Level) (k : ℕ) → Set l
raise-Fin-Set l k = {!!}
```

## Properties

### Being on the left is decidable

```agda
is-decidable-is-inl-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin k x)
is-decidable-is-inl-Fin = {!!}
```

### `Fin 1` is contractible

```agda
map-equiv-Fin-one-ℕ : Fin 1 → unit
map-equiv-Fin-one-ℕ (inr star) = {!!}

inv-map-equiv-Fin-one-ℕ : unit → Fin 1
inv-map-equiv-Fin-one-ℕ star = {!!}

is-section-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
is-section-inv-map-equiv-Fin-one-ℕ = {!!}

is-retraction-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
is-retraction-inv-map-equiv-Fin-one-ℕ = {!!}

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ = {!!}

equiv-Fin-one-ℕ : Fin 1 ≃ unit
pr1 equiv-Fin-one-ℕ = {!!}
pr2 equiv-Fin-one-ℕ = {!!}

is-contr-Fin-one-ℕ : is-contr (Fin 1)
is-contr-Fin-one-ℕ = {!!}

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin = {!!}
```

### The inclusion of `Fin k` into `ℕ`

```agda
nat-Fin : (k : ℕ) → Fin k → ℕ
nat-Fin (succ-ℕ k) (inl x) = {!!}
nat-Fin (succ-ℕ k) (inr x) = {!!}

nat-Fin-reverse : (k : ℕ) → Fin k → ℕ
nat-Fin-reverse (succ-ℕ k) (inl x) = {!!}
nat-Fin-reverse (succ-ℕ k) (inr x) = {!!}

strict-upper-bound-nat-Fin : (k : ℕ) (x : Fin k) → le-ℕ (nat-Fin k x) k
strict-upper-bound-nat-Fin (succ-ℕ k) (inl x) = {!!}
strict-upper-bound-nat-Fin (succ-ℕ k) (inr star) = {!!}

upper-bound-nat-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin (succ-ℕ k) x) k
upper-bound-nat-Fin = {!!}

upper-bound-nat-Fin' :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin k x) k
upper-bound-nat-Fin' = {!!}

is-injective-nat-Fin : (k : ℕ) → is-injective (nat-Fin k)
is-injective-nat-Fin (succ-ℕ k) {inl x} {inl y} p = {!!}
is-injective-nat-Fin (succ-ℕ k) {inl x} {inr star} p = {!!}
is-injective-nat-Fin (succ-ℕ k) {inr star} {inl y} p = {!!}
is-injective-nat-Fin (succ-ℕ k) {inr star} {inr star} p = {!!}

is-emb-nat-Fin : (k : ℕ) → is-emb (nat-Fin k)
is-emb-nat-Fin k = {!!}

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
pr1 (emb-nat-Fin k) = {!!}
pr2 (emb-nat-Fin k) = {!!}
```

### The zero elements in the standard finite types

```agda
zero-Fin : (k : ℕ) → Fin (succ-ℕ k)
zero-Fin zero-ℕ = {!!}
zero-Fin (succ-ℕ k) = {!!}

is-zero-Fin : (k : ℕ) → Fin k → UU lzero
is-zero-Fin (succ-ℕ k) x = {!!}

is-zero-Fin' : (k : ℕ) → Fin k → UU lzero
is-zero-Fin' (succ-ℕ k) x = {!!}

is-nonzero-Fin : (k : ℕ) → Fin k → UU lzero
is-nonzero-Fin (succ-ℕ k) x = {!!}
```

### The successor function on the standard finite types

```agda
skip-zero-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-zero-Fin (succ-ℕ k) (inl x) = {!!}
skip-zero-Fin (succ-ℕ k) (inr star) = {!!}

succ-Fin : (k : ℕ) → Fin k → Fin k
succ-Fin (succ-ℕ k) (inl x) = {!!}
succ-Fin (succ-ℕ k) (inr star) = {!!}

Fin-Type-With-Endomorphism : ℕ → Type-With-Endomorphism lzero
pr1 (Fin-Type-With-Endomorphism k) = {!!}
pr2 (Fin-Type-With-Endomorphism k) = {!!}
```

```agda
is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (succ-ℕ k) (zero-Fin k))
is-zero-nat-zero-Fin {zero-ℕ} = {!!}
is-zero-nat-zero-Fin {succ-ℕ k} = {!!}

nat-skip-zero-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (skip-zero-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-skip-zero-Fin = {!!}

nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x)) ＝ succ-ℕ (nat-Fin k x)
nat-succ-Fin = {!!}

nat-inr-Fin :
  (k : ℕ) (x : Fin k) → nat-Fin (succ-ℕ k) (inr-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-inr-Fin = {!!}
```

```agda
one-Fin : (k : ℕ) → Fin (succ-ℕ k)
one-Fin k = {!!}

is-one-Fin : (k : ℕ) → Fin k → UU lzero
is-one-Fin (succ-ℕ k) x = {!!}

is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → (is-zero-Fin 2 x) + (is-one-Fin 2 x)
is-zero-or-one-Fin-two-ℕ = {!!}

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) (one-Fin (succ-ℕ k)))
is-one-nat-one-Fin = {!!}
```

```agda
is-injective-inl-Fin : (k : ℕ) → is-injective (inl-Fin k)
is-injective-inl-Fin k refl = {!!}
```

### Exercise 7.5 (c)

```agda
neq-zero-skip-zero-Fin :
  {k : ℕ} {x : Fin k} →
  is-nonzero-Fin (succ-ℕ k) (skip-zero-Fin k x)
neq-zero-skip-zero-Fin = {!!}

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} →
  is-nonzero-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl-Fin k x))
neq-zero-succ-Fin = {!!}
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inr star} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inl y} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inr star} p = {!!}

is-injective-succ-Fin : (k : ℕ) → is-injective (succ-Fin k)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inl y} p = {!!}
is-injective-succ-Fin (succ-ℕ k) {inl x} {inr star} p = {!!}
is-injective-succ-Fin (succ-ℕ k) {inr star} {inl y} p = {!!}
is-injective-succ-Fin (succ-ℕ k) {inr star} {inr star} p = {!!}
```

We define a function `skip-neg-two-Fin` in order to define `pred-Fin`.

```agda
skip-neg-two-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin = {!!}
```

We define the predecessor function on `Fin k`.

```agda
pred-Fin : (k : ℕ) → Fin k → Fin k
pred-Fin (succ-ℕ k) (inl x) = {!!}
pred-Fin (succ-ℕ k) (inr x) = {!!}
```

We now turn to the exercise.

```agda
pred-zero-Fin :
  (k : ℕ) → is-neg-one-Fin (succ-ℕ k) (pred-Fin (succ-ℕ k) (zero-Fin k))
pred-zero-Fin = {!!}

succ-skip-neg-two-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ (succ-ℕ k)) (skip-neg-two-Fin (succ-ℕ k) x) ＝
  inl (succ-Fin (succ-ℕ k) x)
succ-skip-neg-two-Fin = {!!}

is-section-pred-Fin :
  (k : ℕ) (x : Fin k) → succ-Fin k (pred-Fin k x) ＝ x
is-section-pred-Fin = {!!}

is-retraction-pred-Fin :
  (k : ℕ) (x : Fin k) → pred-Fin k (succ-Fin k x) ＝ x
is-retraction-pred-Fin = {!!}

is-equiv-succ-Fin : (k : ℕ) → is-equiv (succ-Fin k)
pr1 (pr1 (is-equiv-succ-Fin k)) = {!!}
pr2 (pr1 (is-equiv-succ-Fin k)) = {!!}
pr1 (pr2 (is-equiv-succ-Fin k)) = {!!}
pr2 (pr2 (is-equiv-succ-Fin k)) = {!!}

equiv-succ-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-succ-Fin k) = {!!}
pr2 (equiv-succ-Fin k) = {!!}

is-equiv-pred-Fin : (k : ℕ) → is-equiv (pred-Fin k)
pr1 (pr1 (is-equiv-pred-Fin k)) = {!!}
pr2 (pr1 (is-equiv-pred-Fin k)) = {!!}
pr1 (pr2 (is-equiv-pred-Fin k)) = {!!}
pr2 (pr2 (is-equiv-pred-Fin k)) = {!!}

equiv-pred-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-pred-Fin k) = {!!}
pr2 (equiv-pred-Fin k) = {!!}
```

```agda
leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin k (succ-Fin k x)) (succ-ℕ (nat-Fin k x))
leq-nat-succ-Fin = {!!}
```

### Fin is injective

```agda
abstract
  is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → k ＝ l
  is-injective-Fin {zero-ℕ} {zero-ℕ} e = {!!}
```
