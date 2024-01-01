# Arrays

```agda
module lists.arrays where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.lists

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An array is a pair of a natural number `n`, and a function from `Fin n` to `A`.
We show that arrays and lists are equivalent.

```agda
array : {l : Level} → UU l → UU l
array = {!!}

module _
  {l : Level} {A : UU l}
  where

  length-array : array A → ℕ
  length-array = {!!}

  functional-vec-array : (t : array A) → Fin (length-array t) → A
  functional-vec-array = {!!}

  empty-array : array A
  pr1 (empty-array) = {!!}

  is-empty-array-Prop : array A → Prop lzero
  is-empty-array-Prop = {!!}

  is-empty-array : array A → UU lzero
  is-empty-array = {!!}

  is-nonempty-array-Prop : array A → Prop lzero
  is-nonempty-array-Prop = {!!}

  is-nonempty-array : array A → UU lzero
  is-nonempty-array = {!!}

  head-array : (t : array A) → is-nonempty-array t → A
  head-array = {!!}

  tail-array : (t : array A) → is-nonempty-array t → array A
  tail-array = {!!}

  cons-array : A → array A → array A
  cons-array = {!!}

  revert-array : array A → array A
  revert-array = {!!}
```

### The definition of `fold-vec`

```agda
fold-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  {n : ℕ} → vec A n → B
fold-vec = {!!}
```

## Properties

### The types of lists and arrays are equivalent

```agda
module _
  {l : Level} {A : UU l}
  where

  list-vec : (n : ℕ) → (vec A n) → list A
  list-vec = {!!}

  vec-list : (l : list A) → vec A (length-list l)
  vec-list = {!!}

  is-section-vec-list : (λ l → list-vec (length-list l) (vec-list l)) ~ id
  is-section-vec-list = {!!}

  is-retraction-vec-list :
    ( λ (x : Σ ℕ (λ n → vec A n)) →
      ( length-list (list-vec (pr1 x) (pr2 x)) ,
        vec-list (list-vec (pr1 x) (pr2 x)))) ~
    id
  is-retraction-vec-list = {!!}

  list-array : array A → list A
  list-array = {!!}

  array-list : list A → array A
  array-list = {!!}

  is-section-array-list : (list-array ∘ array-list) ~ id
  is-section-array-list = {!!}

  is-retraction-array-list : (array-list ∘ list-array) ~ id
  is-retraction-array-list = {!!}

  equiv-list-array : array A ≃ list A
  equiv-list-array = {!!}

  equiv-array-list : list A ≃ array A
  equiv-array-list = {!!}
```

### Computational rules of the equivalence between arrays and lists

```agda
  compute-length-list-list-vec :
    (n : ℕ) (v : vec A n) →
    length-list (list-vec n v) ＝ n
  compute-length-list-list-vec = {!!}

  compute-length-list-list-array :
    (t : array A) → length-list (list-array t) ＝ length-array t
  compute-length-list-list-array = {!!}
```

### An element `x` is in a vector `v` iff it is in `list-vec n v`

```agda
  is-in-list-is-in-vec-list :
    (l : list A) (x : A) →
    x ∈-vec (vec-list l) → x ∈-list l
  is-in-list-is-in-vec-list = {!!}

  is-in-vec-list-is-in-list :
    (l : list A) (x : A) →
    x ∈-list l → x ∈-vec (vec-list l)
  is-in-vec-list-is-in-list = {!!}
```

### Link between `fold-list` and `fold-vec`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  where
  htpy-fold-list-fold-vec :
    (l : list A) →
    fold-vec b μ (vec-list l) ＝ fold-list b μ l
  htpy-fold-list-fold-vec = {!!}
```
