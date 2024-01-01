# Sorted vectors

```agda
module lists.sorted-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.permutation-vectors

open import order-theory.decidable-total-orders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define a sorted vector to be a vector such that for every pair of consecutive
elements `x` and `y`, the inequality `x ≤ y` holds.

## Definitions

### The proposition that a vector is sorted

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sorted-vec-Prop :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → Prop l2
  is-sorted-vec-Prop = {!!}

  is-sorted-vec :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → UU l2
  is-sorted-vec = {!!}
```

### The proposition that an element is less than or equal to every element in a vector

```agda
  is-least-element-vec-Prop :
    {n : ℕ} → type-Decidable-Total-Order X →
    vec (type-Decidable-Total-Order X) n → Prop l2
  is-least-element-vec-Prop = {!!}

  is-least-element-vec :
    {n : ℕ} → type-Decidable-Total-Order X →
    vec (type-Decidable-Total-Order X) n → UU l2
  is-least-element-vec = {!!}
```

## Properties

### If a vector is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-vec :
    {n : ℕ} →
    (v : vec (type-Decidable-Total-Order X) (succ-ℕ n)) →
    is-sorted-vec v → is-sorted-vec (tail-vec v)
  is-sorted-tail-is-sorted-vec = {!!}

  is-leq-head-head-tail-is-sorted-vec :
    {n : ℕ} → (v : vec (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-vec v →
    leq-Decidable-Total-Order X (head-vec v) (head-vec (tail-vec v))
  is-leq-head-head-tail-is-sorted-vec = {!!}
```

### If a vector `v' ＝ y ∷ v` is sorted then for all elements `x` less than or equal to `y`, `x` is less than or equal to every element in the vector

```agda
  is-least-element-vec-is-leq-head-sorted-vec :
    {n : ℕ}
    (x : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) (succ-ℕ n)) →
    is-sorted-vec v → leq-Decidable-Total-Order X x (head-vec v) →
    is-least-element-vec x v
  is-least-element-vec-is-leq-head-sorted-vec = {!!}
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-vec-Prop :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → Prop l2
  is-sorted-least-element-vec-Prop = {!!}

  is-sorted-least-element-vec :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → UU l2
  is-sorted-least-element-vec = {!!}

  is-sorted-least-element-vec-is-sorted-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-vec v → is-sorted-least-element-vec v
  is-sorted-least-element-vec-is-sorted-vec = {!!}

  is-sorted-vec-is-sorted-least-element-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-least-element-vec v →
    is-sorted-vec v
  is-sorted-vec-is-sorted-least-element-vec = {!!}
```

### If the tail of a vector `v` is sorted and `x ≤ head-vec v`, then `v` is sorted

```agda
  is-sorted-vec-is-sorted-tail-is-leq-head-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-vec (tail-vec v) →
    (leq-Decidable-Total-Order X (head-vec v) (head-vec (tail-vec v))) →
    is-sorted-vec v
  is-sorted-vec-is-sorted-tail-is-leq-head-vec = {!!}
```

### If an element `x` is less than or equal to every element of a vector `v`, then it is less than or equal to every element of every permutation of `v`

```agda
  is-least-element-functional-vec-Prop :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n) →
    Prop l2
  is-least-element-functional-vec-Prop = {!!}

  is-least-element-functional-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n) →
    UU l2
  is-least-element-functional-vec = {!!}

  is-least-element-permute-functional-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n)
    (a : Permutation n) →
    is-least-element-functional-vec n x fv →
    is-least-element-functional-vec n x (fv ∘ map-equiv a)
  is-least-element-permute-functional-vec = {!!}

  is-least-element-vec-is-least-element-functional-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n) →
    is-least-element-functional-vec n x fv →
    is-least-element-vec x (listed-vec-functional-vec n fv)
  is-least-element-vec-is-least-element-functional-vec = {!!}

  is-least-element-functional-vec-is-least-element-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n) →
    is-least-element-vec x v →
    is-least-element-functional-vec n x (functional-vec-vec n v)
  is-least-element-functional-vec-is-least-element-vec = {!!}

  is-least-element-permute-vec :
    {n : ℕ}
    (x : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n)
    (a : Permutation n) →
    is-least-element-vec x v →
    is-least-element-vec x (permute-vec n v a)
  is-least-element-permute-vec = {!!}
```
