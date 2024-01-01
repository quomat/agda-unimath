# Quicksort for lists

```agda
module lists.quicksort-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.lists

open import order-theory.decidable-total-orders
```

</details>

## Idea

Quicksort is a sorting algorithm on lists that works by selecting a pivoting
element, dividing the list into elements smaller than the pivoting element and
elements greater than the pivoting element, and sorting those two lists by again
applying the quicksort algorithm.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  helper-quicksort-list-divide-leq :
    (x : type-Decidable-Total-Order X) →
    (y : type-Decidable-Total-Order X) →
    leq-or-strict-greater-Decidable-Poset X x y →
    list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  helper-quicksort-list-divide-leq = {!!}

  quicksort-list-divide-leq :
    type-Decidable-Total-Order X → list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  quicksort-list-divide-leq = {!!}

  helper-quicksort-list-divide-strict-greater :
    (x : type-Decidable-Total-Order X) →
    (y : type-Decidable-Total-Order X) →
    leq-or-strict-greater-Decidable-Poset X x y →
    list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  helper-quicksort-list-divide-strict-greater = {!!}

  quicksort-list-divide-strict-greater :
    type-Decidable-Total-Order X → list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  quicksort-list-divide-strict-greater = {!!}

  private
    helper-inequality-length-quicksort-list-divide-leq :
      (x : type-Decidable-Total-Order X) →
      (y : type-Decidable-Total-Order X) →
      (p : leq-or-strict-greater-Decidable-Poset X x y) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (helper-quicksort-list-divide-leq x y p l) ≤-ℕ
      length-list (cons y l)
    helper-inequality-length-quicksort-list-divide-leq = {!!}

    inequality-length-quicksort-list-divide-leq :
      (x : type-Decidable-Total-Order X) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (quicksort-list-divide-leq x l) ≤-ℕ length-list l
    inequality-length-quicksort-list-divide-leq = {!!}

    helper-inequality-length-quicksort-list-divide-strict-greater :
      (x : type-Decidable-Total-Order X) →
      (y : type-Decidable-Total-Order X) →
      (p : leq-or-strict-greater-Decidable-Poset X x y) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (helper-quicksort-list-divide-strict-greater x y p l) ≤-ℕ
      length-list (cons y l)
    helper-inequality-length-quicksort-list-divide-strict-greater = {!!}

    inequality-length-quicksort-list-divide-strict-greater :
      (x : type-Decidable-Total-Order X) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (quicksort-list-divide-strict-greater x l) ≤-ℕ length-list l
    inequality-length-quicksort-list-divide-strict-greater = {!!}

  base-quicksort-list :
    (l : list (type-Decidable-Total-Order X)) → zero-ℕ ＝ length-list l →
    list (type-Decidable-Total-Order X)
  base-quicksort-list = {!!}

  inductive-step-quicksort-list :
    (k : ℕ) →
    □-≤-ℕ
      ( λ n →
        (l : list (type-Decidable-Total-Order X)) →
        n ＝ length-list l → list (type-Decidable-Total-Order X))
      ( k) →
    (l : list (type-Decidable-Total-Order X)) →
    succ-ℕ k ＝ length-list l → list (type-Decidable-Total-Order X)
  inductive-step-quicksort-list = {!!}

  quicksort-list :
    list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  quicksort-list = {!!}
```
