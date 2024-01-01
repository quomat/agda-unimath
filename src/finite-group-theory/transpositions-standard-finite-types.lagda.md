# Transpositions of standard finite types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.transpositions-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given `i` and `j` in `Fin n`, the transposition associated to `i` and `j` swap
these two elements.

## Definitions

### Transpositions on `Fin n`

This definition uses the `standard-transposition` in
[`finite-group-theory.transposition`](finite-group-theory.transpositions.md).

```agda
module _
  (n : ℕ) (i j : Fin n) (neq : i ≠ j)
  where

  transposition-Fin : Permutation n
  transposition-Fin = {!!}

  map-transposition-Fin : Fin n → Fin n
  map-transposition-Fin = {!!}

  left-computation-transposition-Fin :
    map-standard-transposition (has-decidable-equality-Fin n) neq i ＝ j
  left-computation-transposition-Fin = {!!}

  right-computation-transposition-Fin :
    map-standard-transposition (has-decidable-equality-Fin n) neq j ＝ i
  right-computation-transposition-Fin = {!!}

  is-fixed-point-transposition-Fin :
    (z : Fin n) →
    i ≠ z →
    j ≠ z →
    map-standard-transposition (has-decidable-equality-Fin n) neq z ＝ z
  is-fixed-point-transposition-Fin = {!!}
```

### The transposition that swaps the two last elements of `Fin (succ-ℕ (succ-ℕ n))`

We define directly the transposition of `Fin (succ-ℕ (succ-ℕ n))` that exchanges
the two elements associated to `n` and `succ-ℕ n`.

```agda
module _
  (n : ℕ)
  where

  map-swap-two-last-elements-transposition-Fin :
    Fin (succ-ℕ (succ-ℕ n)) → Fin (succ-ℕ (succ-ℕ n))
  map-swap-two-last-elements-transposition-Fin = {!!}

  is-involution-map-swap-two-last-elements-transposition-Fin :
    ( map-swap-two-last-elements-transposition-Fin ∘
      map-swap-two-last-elements-transposition-Fin) ~
    id
  is-involution-map-swap-two-last-elements-transposition-Fin = {!!}

  swap-two-last-elements-transposition-Fin : Permutation (succ-ℕ (succ-ℕ n))
  swap-two-last-elements-transposition-Fin = {!!}
```

We show that this definiton is an instance of the previous one.

```agda
  cases-htpy-swap-two-last-elements-transposition-Fin :
    (x : Fin (succ-ℕ (succ-ℕ n))) →
    (x ＝ neg-one-Fin (succ-ℕ n)) + (x ≠ neg-one-Fin (succ-ℕ n)) →
    (x ＝ neg-two-Fin (succ-ℕ n)) + (x ≠ neg-two-Fin (succ-ℕ n)) →
    map-swap-two-last-elements-transposition-Fin x ＝
    map-transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( neg-two-Fin (succ-ℕ n))
      ( neg-one-Fin (succ-ℕ n))
      ( neq-inl-inr)
      ( x)
  cases-htpy-swap-two-last-elements-transposition-Fin = {!!}

  htpy-swap-two-last-elements-transposition-Fin :
    htpy-equiv
      ( swap-two-last-elements-transposition-Fin)
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neq-inl-inr))
  htpy-swap-two-last-elements-transposition-Fin = {!!}
```

### Transpositions of a pair of adjacent elements in `Fin (succ-ℕ n)`

#### Definition using `swap-two-last-elements-transposition-Fin`

```agda
adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) →
  Permutation (succ-ℕ n)
adjacent-transposition-Fin = {!!}

map-adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) →
  (Fin (succ-ℕ n) → Fin (succ-ℕ n))
map-adjacent-transposition-Fin = {!!}
```

#### `adjacent-transposition-Fin` is an instance of the definiton `transposition-Fin`

```agda
cases-htpy-map-coprod-map-transposition-id-Fin :
  (n : ℕ) → (k l : Fin n) → (neq : k ≠ l) →
  (x : Fin (succ-ℕ n)) →
  (x ＝ inl-Fin n k) + (x ≠ inl-Fin n k) →
  (x ＝ inl-Fin n l) + (x ≠ inl-Fin n l) →
  map-coprod (map-transposition-Fin n k l neq) id x ＝
  map-transposition-Fin
    ( succ-ℕ n)
    ( inl-Fin n k)
    ( inl-Fin n l)
    ( neq ∘ is-injective-inl-Fin n)
    ( x)
cases-htpy-map-coprod-map-transposition-id-Fin = {!!}
cases-htpy-map-coprod-map-transposition-id-Fin
  ( n)
  ( k)
  ( l)
  ( neq)
  ( x)
  ( inr _)
  ( inl refl) = {!!}
cases-htpy-map-coprod-map-transposition-id-Fin
  ( n)
  ( k)
  ( l)
  ( neq)
  ( inl x)
  ( inr neqk)
  ( inr neql) = {!!}
cases-htpy-map-coprod-map-transposition-id-Fin
  ( n)
  ( k)
  ( l)
  ( neq)
  ( inr star)
  ( inr neqk)
  ( inr neql) = {!!}

htpy-map-coprod-map-transposition-id-Fin :
  (n : ℕ) → (k l : Fin n) → (neq : k ≠ l) →
  htpy-equiv
    ( equiv-coprod (transposition-Fin n k l neq) id-equiv)
    ( transposition-Fin
      ( succ-ℕ n)
      ( inl-Fin n k)
      ( inl-Fin n l)
      ( neq ∘ is-injective-inl-Fin n))
htpy-map-coprod-map-transposition-id-Fin = {!!}

helper-htpy-same-transposition-Fin :
  (n : ℕ) (k l : Fin n) (neq1 : k ≠ l) (neq2 : k ≠ l) →
  (neq1 ＝ neq2) →
  htpy-equiv
    ( transposition-Fin n k l neq1)
    ( transposition-Fin n k l neq2)
helper-htpy-same-transposition-Fin = {!!}

htpy-same-transposition-Fin :
  {n : ℕ} {k l : Fin n} {neq1 : k ≠ l} {neq2 : k ≠ l} →
  htpy-equiv
    ( transposition-Fin n k l neq1)
    ( transposition-Fin n k l neq2)
htpy-same-transposition-Fin = {!!}

htpy-adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) →
  htpy-equiv
    ( adjacent-transposition-Fin n k)
    ( transposition-Fin
      ( succ-ℕ n)
      ( inl-Fin n k)
      ( inr-Fin n k)
      ( neq-inl-Fin-inr-Fin n k))
htpy-adjacent-transposition-Fin = {!!}
```

## Properties

### The transposition associated to `i` and `j` is homotopic to the one associated with `j` and `i`

```agda
cases-htpy-transposition-Fin-transposition-swap-Fin :
  (n : ℕ) → (i j : Fin n) → (neq : i ≠ j) → (x : Fin n) →
  (x ＝ i) + (x ≠ i) →
  (x ＝ j) + (x ≠ j) →
  map-transposition-Fin n i j neq x ＝
  map-transposition-Fin n j i (neq ∘ inv) x
cases-htpy-transposition-Fin-transposition-swap-Fin = {!!}
cases-htpy-transposition-Fin-transposition-swap-Fin
  ( n)
  ( i)
  ( j)
  ( neq)
  ( .j)
  ( inr _)
  ( inl refl) = {!!}
cases-htpy-transposition-Fin-transposition-swap-Fin
  ( n)
  ( i)
  ( j)
  ( neq)
  ( x)
  ( inr neqi)
  ( inr neqj) = {!!}

htpy-transposition-Fin-transposition-swap-Fin :
  (n : ℕ) → (i j : Fin n) → (neq : i ≠ j) →
  htpy-equiv
    ( transposition-Fin n i j neq)
    ( transposition-Fin n j i (neq ∘ inv))
htpy-transposition-Fin-transposition-swap-Fin = {!!}
```

### The conjugate of a transposition is also a transposition

```agda
htpy-conjugate-transposition-Fin :
  (n : ℕ) (x y z : Fin n)
  (neqxy : x ≠ y)
  (neqyz : y ≠ z)
  (neqxz : x ≠ z) →
  htpy-equiv
    ( transposition-Fin n y z neqyz ∘e
      ( transposition-Fin n x y neqxy ∘e
        transposition-Fin n y z neqyz))
    ( transposition-Fin n x z neqxz)
htpy-conjugate-transposition-Fin = {!!}

private
  htpy-whisk-conjugate :
    {l1 : Level} {A : UU l1} {f f' : A → A} (g : A → A) →
    (f ~ f') → (f ∘ (g ∘ f)) ~ (f' ∘ (g ∘ f'))
  htpy-whisk-conjugate = {!!}

  htpy-whisk :
    {l : Level} {A : UU l} (f : A → A) {g g' : A → A} →
    g ~ g' → (f ∘ (g ∘ f)) ~ (f ∘ (g' ∘ f))
  htpy-whisk = {!!}

htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin :
  (n : ℕ) (x : Fin (succ-ℕ n)) (neq : x ≠ neg-one-Fin n) →
  htpy-equiv
    ( swap-two-last-elements-transposition-Fin n ∘e
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( inl-Fin (succ-ℕ n) x)
        ( neg-two-Fin (succ-ℕ n))
        ( neq ∘ is-injective-inl-Fin (succ-ℕ n)) ∘e
        swap-two-last-elements-transposition-Fin n))
    ( transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( inl-Fin (succ-ℕ n) x)
      ( neg-one-Fin (succ-ℕ n))
      ( neq-inl-inr))
htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin = {!!}

htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin' :
  (n : ℕ) (x : Fin (succ-ℕ n)) (neq : x ≠ neg-one-Fin n) →
  htpy-equiv
    ( swap-two-last-elements-transposition-Fin n ∘e
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( inl-Fin (succ-ℕ n) x)
        ( neq ∘ (is-injective-inl-Fin (succ-ℕ n) ∘ inv)) ∘e
        swap-two-last-elements-transposition-Fin n))
    ( transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( neg-one-Fin (succ-ℕ n))
      ( inl-Fin (succ-ℕ n) x)
      ( neq-inr-inl))
htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin' = {!!}
```

### Every transposition is the composition of a list of adjacent transpositions

```agda
list-adjacent-transpositions-transposition-Fin :
  (n : ℕ) → (i j : Fin (succ-ℕ n)) →
  list (Fin n)
list-adjacent-transpositions-transposition-Fin = {!!}
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl i)
  ( inl j) = {!!}
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inr star))
  ( inr star) = {!!}
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inl i))
  ( inr star) = {!!}
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inl j)) = {!!}
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inr star)) = {!!}

permutation-list-adjacent-transpositions :
  (n : ℕ) → list (Fin n) → Permutation (succ-ℕ n)
permutation-list-adjacent-transpositions = {!!}

map-permutation-list-adjacent-transpositions :
  (n : ℕ) → list (Fin n) → Fin (succ-ℕ n) → Fin (succ-ℕ n)
map-permutation-list-adjacent-transpositions = {!!}

htpy-permutation-inl-list-adjacent-transpositions :
  (n : ℕ) → (l : list (Fin n)) →
  htpy-equiv
    ( permutation-list-adjacent-transpositions
      ( succ-ℕ n)
      ( map-list (inl-Fin n) l))
    ( equiv-coprod
      ( permutation-list-adjacent-transpositions n l)
      ( id-equiv))
htpy-permutation-inl-list-adjacent-transpositions = {!!}

htpy-permutation-snoc-list-adjacent-transpositions :
  (n : ℕ) (l : list (Fin n)) (x : Fin n) →
  htpy-equiv
    ( permutation-list-adjacent-transpositions n (snoc l x))
    ( permutation-list-adjacent-transpositions n l ∘e
      adjacent-transposition-Fin n x)
htpy-permutation-snoc-list-adjacent-transpositions = {!!}

htpy-permutation-list-adjacent-transpositions-transposition-Fin :
  (n : ℕ) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
  htpy-equiv
    ( permutation-list-adjacent-transpositions
      ( n)
      ( list-adjacent-transpositions-transposition-Fin n i j))
    ( transposition-Fin (succ-ℕ n) i j neq)
htpy-permutation-list-adjacent-transpositions-transposition-Fin = {!!}
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl i)
  ( inl j)
  ( neq) = {!!}
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inl i))
  ( inr star)
  ( neq) = {!!}
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inr star))
  ( inr star)
  ( neq) = {!!}
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inl j))
  ( neq) = {!!}
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inr star))
  ( neq) = {!!}
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inr star)
  ( neq) = {!!}
```
