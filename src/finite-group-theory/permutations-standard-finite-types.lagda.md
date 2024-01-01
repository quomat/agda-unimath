# Permutations of standard finite types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.permutations-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.transpositions

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A permutation of `Fin n` is an automorphism of `Fin n`.

## Definitions

```agda
Permutation : (n : ℕ) → UU lzero
Permutation = {!!}
```

## Properties

### Every permutation on `Fin n` can be described as a composite of transpositions

```agda
list-transpositions-permutation-Fin' :
  (n : ℕ) (f : Permutation (succ-ℕ n)) →
  (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
  ( list
    ( Σ
      ( Fin (succ-ℕ n) → Decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ n)) (type-Decidable-Prop ∘ P)))))
list-transpositions-permutation-Fin' = {!!}

list-transpositions-permutation-Fin :
  (n : ℕ) (f : Permutation n) →
  ( list
    ( Σ
      ( Fin n → Decidable-Prop lzero)
      ( λ P → has-cardinality 2 (Σ (Fin n) (type-Decidable-Prop ∘ P)))))
list-transpositions-permutation-Fin = {!!}

abstract
  retraction-permutation-list-transpositions-Fin' :
    (n : ℕ) (f : Permutation (succ-ℕ n)) →
    (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
    (y z : Fin (succ-ℕ n)) → Id (map-equiv f y) z →
    Id
      ( map-equiv
        ( permutation-list-transpositions
          ( list-transpositions-permutation-Fin (succ-ℕ n) f))
        ( y))
      ( map-equiv f y)
  retraction-permutation-list-transpositions-Fin' = {!!}

  retraction-permutation-list-transpositions-Fin :
    (n : ℕ) (f : Permutation n) →
    htpy-equiv
      ( permutation-list-transpositions
        ( list-transpositions-permutation-Fin n f))
      ( f)
  retraction-permutation-list-transpositions-Fin = {!!}
```

```agda
permutation-list-standard-transpositions-Fin :
  (n : ℕ) →
  list (Σ (Fin n × Fin n) (λ (i , j) → i ≠ j)) →
  Permutation n
permutation-list-standard-transpositions-Fin = {!!}

list-standard-transpositions-permutation-Fin :
  (n : ℕ) (f : Permutation n) →
  list (Σ (Fin n × Fin n) (λ (i , j) → i ≠ j))
list-standard-transpositions-permutation-Fin = {!!}

private
  htpy-permutation-list :
    (n : ℕ)
    (l : list
      (2-Element-Decidable-Subtype lzero (Fin (succ-ℕ n)))) →
    htpy-equiv
      ( permutation-list-standard-transpositions-Fin
        ( succ-ℕ n)
        ( map-list
          ( λ P →
            ( element-two-elements-transposition-Fin P ,
              other-element-two-elements-transposition-Fin P) ,
            neq-elements-two-elements-transposition-Fin P)
          ( l)))
      ( permutation-list-transpositions l)
  htpy-permutation-list = {!!}

retraction-permutation-list-standard-transpositions-Fin :
  (n : ℕ) (f : Permutation n) →
  htpy-equiv
    ( permutation-list-standard-transpositions-Fin
      ( n)
      ( list-standard-transpositions-permutation-Fin n f))
    ( f)
retraction-permutation-list-standard-transpositions-Fin = {!!}
```
