# Equality in the standard finite types

```agda
module univalent-combinatorics.equality-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.apartness-relations
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.set-truncations
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Since the standard finite types are defined recursively by adding a point one at
a time, it follows that equality in the standard finite types is decidable, and
that they are sets.

## Properties

### Characterization of the identity types of the standard finite types

```agda
Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
Eq-Fin (succ-ℕ k) (inl x) (inr y) = {!!}
Eq-Fin (succ-ℕ k) (inr x) (inl y) = {!!}
Eq-Fin (succ-ℕ k) (inr x) (inr y) = {!!}

is-prop-Eq-Fin : (k : ℕ) → (x : Fin k) → (y : Fin k) → is-prop (Eq-Fin k x y)
is-prop-Eq-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
is-prop-Eq-Fin (succ-ℕ k) (inr x) (inl y) = {!!}
is-prop-Eq-Fin (succ-ℕ k) (inl x) (inr y) = {!!}
is-prop-Eq-Fin (succ-ℕ k) (inr x) (inr y) = {!!}

refl-Eq-Fin : (k : ℕ) (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin (succ-ℕ k) (inl x) = {!!}
refl-Eq-Fin (succ-ℕ k) (inr x) = {!!}

Eq-Fin-eq : (k : ℕ) {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq k refl = {!!}

eq-Eq-Fin :
  (k : ℕ) {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin (succ-ℕ k) {inl x} {inl y} e = {!!}
eq-Eq-Fin (succ-ℕ k) {inr star} {inr star} star = {!!}

extensionality-Fin :
  (k : ℕ)
  (x y : Fin k) →
  (x ＝ y) ≃ (Eq-Fin k x y)
pr1 (extensionality-Fin k x y) = {!!}
pr2 (extensionality-Fin k x y) = {!!}

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = {!!}
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = {!!}
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = {!!}
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = {!!}

has-decidable-equality-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin k x y = {!!}

Fin-Discrete-Type : ℕ → Discrete-Type lzero
pr1 (Fin-Discrete-Type k) = {!!}
pr2 (Fin-Discrete-Type k) = {!!}

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin k x)
is-decidable-is-zero-Fin {succ-ℕ k} x = {!!}

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin k x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x = {!!}

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin k x)
is-decidable-is-one-Fin {succ-ℕ k} x = {!!}
```

### Being zero or being one is a proposition

```agda
is-prop-is-zero-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-prop (is-zero-Fin (succ-ℕ k) x)
is-prop-is-zero-Fin k x = {!!}

is-prop-is-one-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-prop (is-one-Fin (succ-ℕ k) x)
is-prop-is-one-Fin k x = {!!}

is-prop-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-prop ((is-zero-Fin 2 x) + (is-one-Fin 2 x))
is-prop-is-zero-or-one-Fin-two-ℕ x = {!!}
```

### Every element in the standard two-element type is either `0` or `1`

```agda
is-contr-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-contr ((is-zero-Fin 2 x) + (is-one-Fin 2 x))
is-contr-is-zero-or-one-Fin-two-ℕ x = {!!}
```

```agda
decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → Decidable-Prop lzero
pr1 (decidable-Eq-Fin n i j) = {!!}
pr1 (pr2 (decidable-Eq-Fin n i j)) = {!!}
pr2 (pr2 (decidable-Eq-Fin n i j)) = {!!}
```

### The standard finite types are their own set truncations

```agda
equiv-unit-trunc-Fin-Set : (k : ℕ) → Fin k ≃ type-trunc-Set (Fin k)
equiv-unit-trunc-Fin-Set k = {!!}
```

### If `leq-ℕ 2 n`, then there exists two distinct elements in `Fin n`

```agda
two-distinct-elements-leq-2-Fin :
  (n : ℕ) → leq-ℕ 2 n → Σ (Fin n) (λ x → Σ (Fin n) (λ y → x ≠ y))
pr1 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq) = {!!}
pr1 (pr2 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq)) = {!!}
pr2 (pr2 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq)) = {!!}
```

### The standard finite type with a (tight) apartness relation

```agda
Fin-Type-With-Apartness : (k : ℕ) → Type-With-Apartness lzero lzero
Fin-Type-With-Apartness k = {!!}

Fin-Type-With-Tight-Apartness : (k : ℕ) → Type-With-Tight-Apartness lzero lzero
Fin-Type-With-Tight-Apartness k = {!!}
```
