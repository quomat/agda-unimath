# Permutations of lists

```agda
module lists.permutation-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import lists.arrays
open import lists.functoriality-lists
open import lists.lists
open import lists.permutation-vectors
```

</details>

## Idea

Given an array `t` of length `n` and a automorphism `σ` of `Fin n`, the
permutation of `t` according to `σ` is the array where the index are permuted by
`σ`. Then, we can define what is a permutation of a list of length `n` via the
equivalence between arrays and lists.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-list : (l : list A) → Permutation (length-list l) → list A
  permute-list l s = {!!}
```

### The predicate that a function from `list` to `list` is permuting lists

```agda
  is-permutation-list : (list A → list A) → UU l
  is-permutation-list f = {!!}

  permutation-is-permutation-list :
    (f : list A → list A) → is-permutation-list f →
    ((l : list A) → Permutation (length-list l))
  permutation-is-permutation-list f P l = {!!}

  eq-permute-list-permutation-is-permutation-list :
    (f : list A → list A) → (P : is-permutation-list f) →
    (l : list A) →
    (f l ＝ permute-list l (permutation-is-permutation-list f P l))
  eq-permute-list-permutation-is-permutation-list f P l = {!!}
```

## Properties

### The length of a permuted list

```agda
  length-permute-list :
    (l : list A) (t : Permutation (length-list l)) →
    length-list (permute-list l t) ＝ (length-list l)
  length-permute-list l t = {!!}
```

### Link between `permute-list` and `permute-vec`

```agda
  eq-vec-list-permute-list :
    (l : list A) (f : Permutation (length-list l)) →
    permute-vec (length-list l) (vec-list l) f ＝
    tr
      ( vec A)
      ( _)
      ( vec-list ( permute-list l f))
  eq-vec-list-permute-list l f = {!!}
```

### If a function `f` from `vec` to `vec` is a permutation of vectors then `list-vec ∘ f ∘ vec-list` is a permutation of lists

```agda
  is-permutation-list-is-permutation-vec :
    (f : (n : ℕ) → vec A n → vec A n) →
    ((n : ℕ) → is-permutation-vec n (f n)) →
    is-permutation-list
      ( λ l → list-vec (length-list l) (f (length-list l) (vec-list l)))
  pr1 (is-permutation-list-is-permutation-vec f T l) = {!!}
```

### If `x` is in `permute-list l t` then `x` is in `l`

```agda
  is-in-list-is-in-permute-list :
    (l : list A) (t : Permutation (length-list l)) (x : A) →
    x ∈-list (permute-list l t) → x ∈-list l
  is-in-list-is-in-permute-list l t x I = {!!}

  is-in-permute-list-is-in-list :
    (l : list A) (t : Permutation (length-list l)) (x : A) →
    x ∈-list l → x ∈-list (permute-list l t)
  is-in-permute-list-is-in-list l t x I = {!!}
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-list b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  (C : commutative-fold-vec μ)
  where

  invariant-fold-vec-tr :
    {n m : ℕ} (v : vec A n) (eq : n ＝ m) →
    fold-vec b μ (tr (vec A) eq v) ＝ fold-vec b μ v
  invariant-fold-vec-tr v refl = {!!}

  invariant-permutation-fold-list :
    (l : list A) → (f : Permutation (length-list l)) →
    fold-list b μ l ＝ fold-list b μ (permute-list l f)
  invariant-permutation-fold-list l f = {!!}
```

### `map-list` of the permutation of a list

```agda
compute-tr-permute-vec :
  {l : Level} {A : UU l} {n m : ℕ}
  (e : n ＝ m) (v : vec A n) (t : Permutation m) →
  tr
    ( vec A)
    ( e)
    ( permute-vec
      ( n)
      ( v)
      ( tr Permutation (inv e) t)) ＝
  permute-vec
    ( m)
    ( tr (vec A) e v)
    ( t)
compute-tr-permute-vec refl v t = {!!}

compute-tr-map-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) {n m : ℕ} (p : n ＝ m) (v : vec A n) →
  tr (vec B) p (map-vec f v) ＝ map-vec f (tr (vec A) p v)
compute-tr-map-vec f refl v = {!!}

helper-compute-list-vec-map-vec-permute-vec-vec-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (p : list A) (t : Permutation (length-list p)) →
  tr
    ( vec B)
    ( inv (length-permute-list p t))
    ( map-vec f (permute-vec (length-list p) (vec-list p) t)) ＝
  map-vec f (vec-list (permute-list p t))
helper-compute-list-vec-map-vec-permute-vec-vec-list f p t = {!!}

compute-list-vec-map-vec-permute-vec-vec-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (p : list A) (t : Permutation (length-list p)) →
  list-vec
    ( length-list p)
    ( map-vec f (permute-vec (length-list p) (vec-list p) t)) ＝
  list-vec
    ( length-list (permute-list p t))
    ( map-vec f (vec-list (permute-list p t)))
compute-list-vec-map-vec-permute-vec-vec-list f p t = {!!}

eq-map-list-permute-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (p : list A) (t : Permutation (length-list p)) →
  permute-list (map-list f p) (tr Permutation (inv (length-map-list f p)) t) ＝
  map-list f (permute-list p t)
eq-map-list-permute-list {B = B} f p t = {!!}
```
