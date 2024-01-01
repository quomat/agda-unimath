# Permutations of vectors

```agda
module lists.permutation-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import lists.arrays
open import lists.lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given an functional vector `t` of length `n` and a automorphism `σ` of `Fin n`,
the permutation of `t` according to `σ` is the functional vector where the index
are permuted by `σ`. Then, we can define what is a permutation of a vector of
length `n` via the equivalence between functional vectors and vectors.

## Definitions

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-vec : (n : ℕ) → vec A n → Permutation n → vec A n
  permute-vec = {!!}
```

### The predicate that a function from `vec` to `vec` is just permuting vectors

```agda
  is-permutation-vec : (n : ℕ) → (vec A n → vec A n) → UU l
  is-permutation-vec = {!!}

  permutation-is-permutation-vec :
    (n : ℕ) (f : vec A n → vec A n) → is-permutation-vec n f →
    (v : vec A n) → Permutation n
  permutation-is-permutation-vec = {!!}

  eq-permute-vec-permutation-is-permutation-vec :
    (n : ℕ) (f : vec A n → vec A n) → (P : is-permutation-vec n f) →
    (v : vec A n) →
    (f v ＝ permute-vec n v (permutation-is-permutation-vec n f P v))
  eq-permute-vec-permutation-is-permutation-vec = {!!}
```

## Properties

### Computational rules

```agda
  compute-permute-vec-id-equiv :
    (n : ℕ)
    (v : vec A n) →
    permute-vec n v id-equiv ＝ v
  compute-permute-vec-id-equiv = {!!}

  compute-composition-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (a b : Permutation n) →
    permute-vec n v (a ∘e b) ＝ permute-vec n (permute-vec n v a) b
  compute-composition-permute-vec = {!!}

  compute-swap-two-last-elements-transposition-Fin-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (x y : A) →
    permute-vec
      (succ-ℕ (succ-ℕ n))
      (x ∷ y ∷ v)
      (swap-two-last-elements-transposition-Fin n) ＝
    (y ∷ x ∷ v)
  compute-swap-two-last-elements-transposition-Fin-permute-vec = {!!}

  compute-equiv-coprod-permutation-id-equiv-permute-vec :
    (n : ℕ)
    (v : vec A n)
    (x : A)
    (t : Permutation n) →
    permute-vec (succ-ℕ n) (x ∷ v) (equiv-coprod t id-equiv) ＝
    (x ∷ permute-vec n v t)
  compute-equiv-coprod-permutation-id-equiv-permute-vec = {!!}

  ap-permute-vec :
    {n : ℕ}
    (a : Permutation n)
    {v w : vec A n} →
    v ＝ w →
    permute-vec n v a ＝ permute-vec n w a
  ap-permute-vec = {!!}
```

### `x` is in a vector `v` iff it is in `permute v t`

```agda
  is-in-functional-vec-is-in-permute-functional-vec :
    (n : ℕ) (v : Fin n → A) (t : Permutation n) (x : A) →
    in-functional-vec n x (v ∘ map-equiv t) → in-functional-vec n x v
  is-in-functional-vec-is-in-permute-functional-vec = {!!}

  is-in-vec-is-in-permute-vec :
    (n : ℕ) (v : vec A n) (t : Permutation n) (x : A) →
    x ∈-vec (permute-vec n v t) → x ∈-vec v
  is-in-vec-is-in-permute-vec = {!!}

  is-in-permute-functional-vec-is-in-functional-vec :
    (n : ℕ) (v : Fin n → A) (t : Permutation n) (x : A) →
    in-functional-vec n x v → in-functional-vec n x (v ∘ map-equiv t)
  is-in-permute-functional-vec-is-in-functional-vec = {!!}

  is-in-permute-vec-is-in-vec :
    (n : ℕ) (v : vec A n) (t : Permutation n) (x : A) →
    x ∈-vec v → x ∈-vec (permute-vec n v t)
  is-in-permute-vec-is-in-vec = {!!}
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-vec b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (μ : A → (B → B))
  where

  commutative-fold-vec : UU (l1 ⊔ l2)
  commutative-fold-vec = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  (C : commutative-fold-vec μ)
  where

  invariant-swap-two-last-elements-transposition-fold-vec :
    {n : ℕ} → (v : vec A (succ-ℕ (succ-ℕ n))) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec (succ-ℕ (succ-ℕ n))
      ( v)
      ( swap-two-last-elements-transposition-Fin n))
  invariant-swap-two-last-elements-transposition-fold-vec = {!!}

  invariant-adjacent-transposition-fold-vec :
    {n : ℕ} → (v : vec A (succ-ℕ n)) → (k : Fin n) →
    fold-vec b μ v ＝
    fold-vec b μ (permute-vec (succ-ℕ n) v (adjacent-transposition-Fin n k))
  invariant-adjacent-transposition-fold-vec = {!!}
  invariant-adjacent-transposition-fold-vec {succ-ℕ n} (x ∷ v) (inr _) = {!!}

  invariant-list-adjacent-transpositions-fold-vec :
    {n : ℕ} (v : vec A (succ-ℕ n)) (l : list (Fin n)) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec
        ( succ-ℕ n)
        ( v)
        ( permutation-list-adjacent-transpositions n l))
  invariant-list-adjacent-transpositions-fold-vec = {!!}
  invariant-list-adjacent-transpositions-fold-vec {n} v (cons x l) = {!!}

  invariant-transposition-fold-vec :
    {n : ℕ} (v : vec A (succ-ℕ n)) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec (succ-ℕ n) v (transposition-Fin (succ-ℕ n) i j neq))
  invariant-transposition-fold-vec = {!!}

  invariant-list-transpositions-fold-vec :
    {n : ℕ}
    (v : vec A n)
    (l : list (Σ (Fin n × Fin n) (λ (i , j) → i ≠ j))) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec
        ( n)
        ( v)
        ( permutation-list-standard-transpositions-Fin n l))
  invariant-list-transpositions-fold-vec = {!!}
  invariant-list-transpositions-fold-vec {0} v (cons _ _) = {!!}

  invariant-permutation-fold-vec :
    {n : ℕ} → (v : vec A n) → (f : Permutation n) →
    fold-vec b μ v ＝ fold-vec b μ (permute-vec n v f)
  invariant-permutation-fold-vec = {!!}
```

### `map-vec` of the permutation of a vector

```agda
eq-map-vec-permute-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) {n : ℕ} (v : vec A n) (t : Permutation n) →
  permute-vec n (map-vec f v) t ＝
  map-vec f (permute-vec n v t)
eq-map-vec-permute-vec = {!!}
```
