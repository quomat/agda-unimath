# Sorted lists

```agda
module lists.sorted-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.arrays
open import lists.lists
open import lists.sorted-vectors

open import order-theory.decidable-total-orders
```

</details>

## Idea

We define a sorted list to be a list such that for every pair of consecutive
entries `x` and `y`, the inequality `x ≤ y` holds.

## Definitions

### The proposition that a list is sorted

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sorted-list-Prop : list (type-Decidable-Total-Order X) → Prop l2
  is-sorted-list-Prop nil = {!!}

  is-sorted-list : list (type-Decidable-Total-Order X) → UU l2
  is-sorted-list l = {!!}

  is-prop-is-sorted-list :
    (l : list (type-Decidable-Total-Order X)) → is-prop (is-sorted-list l)
  is-prop-is-sorted-list l = {!!}
```

### The proposition that an element is less or equal than every element in a list

```agda
  is-least-element-list-Prop :
    type-Decidable-Total-Order X →
    list (type-Decidable-Total-Order X) → Prop l2
  is-least-element-list-Prop x nil = {!!}

  is-least-element-list :
    type-Decidable-Total-Order X →
    list (type-Decidable-Total-Order X) → UU l2
  is-least-element-list x l = {!!}
```

## Properties

### If a list is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-list :
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-list l → is-sorted-list (tail-list l)
  is-sorted-tail-is-sorted-list nil _ = {!!}
```

### If a list is sorted then its head is less or equal than every element in the list

```agda
  leq-element-in-list-leq-head-is-sorted-list :
    (x y z : type-Decidable-Total-Order X)
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-list (cons y l) →
    z ∈-list (cons y l) →
    leq-Decidable-Total-Order X x y →
    leq-Decidable-Total-Order X x z
  leq-element-in-list-leq-head-is-sorted-list x .z z l s (is-head .z l) q = {!!}
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-list-Prop :
    list (type-Decidable-Total-Order X) → Prop l2
  is-sorted-least-element-list-Prop nil = {!!}

  is-sorted-least-element-list :
    list (type-Decidable-Total-Order X) → UU l2
  is-sorted-least-element-list l = {!!}

  is-sorted-list-is-sorted-least-element-list :
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-least-element-list l → is-sorted-list l
  is-sorted-list-is-sorted-least-element-list nil _ = {!!}
```

### If a vector `v` of length `n` is sorted, then the list `list-vec n v` is also sorted

```agda
  is-sorted-list-is-sorted-vec :
    (n : ℕ) (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-vec X v →
    is-sorted-list (list-vec n v)
  is-sorted-list-is-sorted-vec 0 v S = {!!}
```
