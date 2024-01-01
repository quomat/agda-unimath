# Sort by insertion for vectors

```agda
module lists.sort-by-insertion-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.permutation-vectors
open import lists.sorted-vectors
open import lists.sorting-algorithms-vectors

open import order-theory.decidable-total-orders
```

</details>

## Idea

Sort by insertion is a recursive sort on vectors. If a vector is empty or with
only one element then it is sorted. Otherwise, we recursively sort the tail of
the vector. Then we compare the head of the vector to the head of the sorted
tail. If the head is less or equal than the head of the tail the vector is
sorted. Otherwise we permute the two elements and we recursively sort the tail
of the vector.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  helper-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (l : vec (type-Decidable-Total-Order X) n) →
    leq-or-strict-greater-Decidable-Poset X x y →
    vec (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ (n)))
  helper-insertion-sort-vec = {!!}

  insertion-sort-vec :
    {n : ℕ} →
    vec (type-Decidable-Total-Order X) n →
    vec (type-Decidable-Total-Order X) n
  insertion-sort-vec = {!!}
```

## Properties

### Sort by insertion is a permutation

```agda
  helper-permutation-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (l : vec (type-Decidable-Total-Order X) n) →
    leq-or-strict-greater-Decidable-Poset X x y →
    Permutation (succ-ℕ (succ-ℕ (n)))
  helper-permutation-insertion-sort-vec = {!!}

  permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    Permutation n
  permutation-insertion-sort-vec = {!!}

  helper-eq-permute-vec-permutation-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n)
    (p : leq-or-strict-greater-Decidable-Poset X x y) →
    helper-insertion-sort-vec x y v p ＝
    permute-vec
      ( succ-ℕ (succ-ℕ n))
      ( x ∷ y ∷ v)
      ( helper-permutation-insertion-sort-vec x y v p)
  helper-eq-permute-vec-permutation-insertion-sort-vec = {!!}

  eq-permute-vec-permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    insertion-sort-vec v ＝ permute-vec n v (permutation-insertion-sort-vec v)
  eq-permute-vec-permutation-insertion-sort-vec = {!!}
```

### Sort by insertion is sorting vectors

```agda
  helper-is-sorting-insertion-sort-vec :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n) →
    (p : leq-or-strict-greater-Decidable-Poset X x y) →
    is-sorted-vec X (y ∷ v) →
    is-sorted-vec X (helper-insertion-sort-vec x y v p)
  helper-is-sorting-insertion-sort-vec = {!!}

  is-sorting-insertion-sort-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-vec X (insertion-sort-vec v)
  is-sorting-insertion-sort-vec = {!!}
```

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-vec :
    is-sort-vec X (insertion-sort-vec)
  is-sort-insertion-sort-vec = {!!}
```
