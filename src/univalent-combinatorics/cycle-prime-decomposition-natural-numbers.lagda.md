# Cycle prime decompositions of natural numbers

```agda
module univalent-combinatorics.cycle-prime-decomposition-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.fundamental-theorem-of-arithmetic
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterated-cartesian-product-types
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.iterated-cartesian-products-concrete-groups

open import lists.arrays
open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.permutation-lists
open import lists.sort-by-insertion-lists

open import univalent-combinatorics.cyclic-finite-types
```

</details>

## Idea

Let `n` be a natural number. The `cycle-prime-decomposition-ℕ` of `n` is the
iterated cartesian product of the cyclic types assocated to the prime
decomposition of `n`.

## Definition

```agda
concrete-group-cycle-prime-decomposition-ℕ :
  (n : ℕ) → leq-ℕ 1 n → Concrete-Group (lsuc lzero)
concrete-group-cycle-prime-decomposition-ℕ = {!!}

cycle-prime-decomposition-ℕ :
  (n : ℕ) → leq-ℕ 1 n → UU (lsuc lzero)
cycle-prime-decomposition-ℕ = {!!}
```

## Properties

### Cycle prime decomposition are closed under cartesian products

The cartesian product of the cycle prime decomposition of `n` and `m` is equal
to the cycle prime decomposition of `n *ℕ m`.

```agda
equiv-product-cycle-prime-decomposition-ℕ :
  (n m : ℕ) → (H : leq-ℕ 1 n) → (I : leq-ℕ 1 m) →
  ( cycle-prime-decomposition-ℕ n H × cycle-prime-decomposition-ℕ m I) ≃
  cycle-prime-decomposition-ℕ (n *ℕ m) (preserves-leq-mul-ℕ 1 n 1 m H I)
equiv-product-cycle-prime-decomposition-ℕ = {!!}
```
