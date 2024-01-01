# Multivariable operations

```agda
module foundation.multivariable-operations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import linear-algebra.vectors
```

</details>

## Idea

Given `n` types, an n-ary multivariable operation on them is a function that
takes as inputs one element of each type, and returns an element in some type
`X`.

## Definitions

```agda
multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) n) →
  UU l
multivariable-input = {!!}

empty-multivariable-input :
  {l : Level}
  (A : functional-vec (UU l) 0) →
  multivariable-input 0 A
empty-multivariable-input = {!!}

head-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) A →
  head-functional-vec n A
head-multivariable-input = {!!}

tail-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) A →
  multivariable-input n (tail-functional-vec n A)
tail-multivariable-input = {!!}

cons-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) n) →
  {A0 : UU l} →
  A0 →
  multivariable-input n A →
  multivariable-input (succ-ℕ n) (cons-functional-vec n A0 A)
cons-multivariable-input = {!!}

multivariable-operation :
  { l : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l) n)
  ( X : UU l) →
  UU l
multivariable-operation = {!!}
```

## Properties

### For the case of constant families, multivariable inputs and vectors coincide

```agda
vector-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  multivariable-input n (λ _ → A) →
  vec A n
vector-multivariable-input = {!!}

multivariable-input-vector :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  vec A n →
  multivariable-input n (λ _ → A)
multivariable-input-vector = {!!}

is-section-multivariable-input-vector :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  ( vector-multivariable-input n A ∘
    multivariable-input-vector n A) ~ id
is-section-multivariable-input-vector = {!!}

is-retraction-multivariable-input-vector :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  ( multivariable-input-vector n A ∘
    vector-multivariable-input n A) ~ id
is-retraction-multivariable-input-vector = {!!}

is-equiv-vector-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  is-equiv (vector-multivariable-input n A)
is-equiv-vector-multivariable-input = {!!}

compute-vector-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  multivariable-input n (λ _ → A) ≃ vec A n
compute-vector-multivariable-input = {!!}
```
