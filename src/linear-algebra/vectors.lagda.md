# Vectors

```agda
module linear-algebra.vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

There are two equivalent definitions of vectors of length `n`. First, a **listed
vector** of length `n` is a list of `n` elements of type `A`. Secondly, a
**functional vector** of length `n` is a map `Fin n → A`. We define both types
of vectors and show that they are equivalent.

## Definitions

### The type of listed vectors

```agda
infixr 10 _∷_

data vec {l : Level} (A : UU l) : ℕ → UU l where
  empty-vec : vec A zero-ℕ
  _∷_ : ∀ {n} → A → vec A n → vec A (succ-ℕ n)

module _
  {l : Level} {A : UU l}
  where

  head-vec : {n : ℕ} → vec A (succ-ℕ n) → A
  head-vec (x ∷ v) = {!!}

  tail-vec : {n : ℕ} → vec A (succ-ℕ n) → vec A n
  tail-vec (x ∷ v) = {!!}

  snoc-vec : {n : ℕ} → vec A n → A → vec A (succ-ℕ n)
  snoc-vec empty-vec a = {!!}

  revert-vec : {n : ℕ} → vec A n → vec A n
  revert-vec empty-vec = {!!}

  all-vec : {l2 : Level} {n : ℕ} → (P : A → UU l2) → vec A n → UU l2
  all-vec P empty-vec = {!!}

  component-vec :
    (n : ℕ) → vec A n → Fin n → A
  component-vec (succ-ℕ n) (a ∷ v) (inl k) = {!!}

  infix 6 _∈-vec_
  data _∈-vec_ : {n : ℕ} → A → vec A n → UU l where
    is-head : {n : ℕ} (a : A) (l : vec A n) → a ∈-vec (a ∷ l)
    is-in-tail : {n : ℕ} (a x : A) (l : vec A n) → a ∈-vec l → a ∈-vec (x ∷ l)

  index-in-vec : (n : ℕ) → (a : A) → (v : vec A n) → a ∈-vec v → Fin n
  index-in-vec (succ-ℕ n) a (.a ∷ v) (is-head .a .v) = {!!}

  eq-component-vec-index-in-vec :
    (n : ℕ) (a : A) (v : vec A n) (I : a ∈-vec v) →
    a ＝ component-vec n v (index-in-vec n a v I)
  eq-component-vec-index-in-vec (succ-ℕ n) a (.a ∷ v) (is-head .a .v) = {!!}
```

### The functional type of vectors

```agda
functional-vec : {l : Level} → UU l → ℕ → UU l
functional-vec A n = {!!}

module _
  {l : Level} {A : UU l}
  where

  empty-functional-vec : functional-vec A 0
  empty-functional-vec ()

  head-functional-vec : (n : ℕ) → functional-vec A (succ-ℕ n) → A
  head-functional-vec n v = {!!}

  tail-functional-vec :
    (n : ℕ) → functional-vec A (succ-ℕ n) → functional-vec A n
  tail-functional-vec n v = {!!}

  cons-functional-vec :
    (n : ℕ) → A → functional-vec A n → functional-vec A (succ-ℕ n)
  cons-functional-vec n a v (inl x) = {!!}

  snoc-functional-vec :
    (n : ℕ) → functional-vec A n → A → functional-vec A (succ-ℕ n)
  snoc-functional-vec zero-ℕ v a i = {!!}

  revert-functional-vec :
    (n : ℕ) → functional-vec A n → functional-vec A n
  revert-functional-vec n v i = {!!}

  in-functional-vec : (n : ℕ) → A → functional-vec A n → UU l
  in-functional-vec n a v = {!!}

  index-in-functional-vec :
    (n : ℕ) (x : A) (v : functional-vec A n) →
    in-functional-vec n x v → Fin n
  index-in-functional-vec n x v I = {!!}

  eq-component-functional-vec-index-in-functional-vec :
    (n : ℕ) (x : A) (v : functional-vec A n) (I : in-functional-vec n x v) →
    x ＝ v (index-in-functional-vec n x v I)
  eq-component-functional-vec-index-in-functional-vec n x v I = {!!}
```

## Properties

### Characterizing equality of listed vectors

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-vec : (n : ℕ) → vec A n → vec A n → UU l
  Eq-vec zero-ℕ empty-vec empty-vec = {!!}

  refl-Eq-vec : (n : ℕ) → (u : vec A n) → Eq-vec n u u
  refl-Eq-vec zero-ℕ empty-vec = {!!}

  Eq-eq-vec : (n : ℕ) → (u v : vec A n) → Id u v → Eq-vec n u v
  Eq-eq-vec n u .u refl = {!!}

  eq-Eq-vec : (n : ℕ) → (u v : vec A n) → Eq-vec n u v → Id u v
  eq-Eq-vec zero-ℕ empty-vec empty-vec eq-vec = {!!}

  is-retraction-eq-Eq-vec :
    (n : ℕ) → (u v : vec A n) →
    (p : u ＝ v) → eq-Eq-vec n u v (Eq-eq-vec n u v p) ＝ p
  is-retraction-eq-Eq-vec zero-ℕ empty-vec empty-vec refl = {!!}

  square-Eq-eq-vec :
    (n : ℕ) (x : A) (u v : vec A n) (p : Id u v) →
    (Eq-eq-vec _ (x ∷ u) (x ∷ v) (ap (x ∷_) p)) ＝ (refl , (Eq-eq-vec n u v p))
  square-Eq-eq-vec zero-ℕ x empty-vec empty-vec refl = {!!}

  is-section-eq-Eq-vec :
    (n : ℕ) (u v : vec A n) →
    (p : Eq-vec n u v) → Eq-eq-vec n u v (eq-Eq-vec n u v p) ＝ p
  is-section-eq-Eq-vec zero-ℕ empty-vec empty-vec (map-raise star) = {!!}

  is-equiv-Eq-eq-vec :
    (n : ℕ) → (u v : vec A n) → is-equiv (Eq-eq-vec n u v)
  is-equiv-Eq-eq-vec n u v = {!!}

  extensionality-vec : (n : ℕ) → (u v : vec A n) → Id u v ≃ Eq-vec n u v
  extensionality-vec n u v = {!!}
```

### The types of listed vectors and functional vectors are equivalent

```agda
module _
  {l : Level} {A : UU l}
  where

  listed-vec-functional-vec : (n : ℕ) → functional-vec A n → vec A n
  listed-vec-functional-vec zero-ℕ v = {!!}

  functional-vec-vec : (n : ℕ) → vec A n → functional-vec A n
  functional-vec-vec zero-ℕ v = {!!}

  is-section-functional-vec-vec :
    (n : ℕ) → (listed-vec-functional-vec n ∘ functional-vec-vec n) ~ id
  is-section-functional-vec-vec .zero-ℕ empty-vec = {!!}

  abstract
    is-retraction-functional-vec-vec :
      (n : ℕ) → (functional-vec-vec n ∘ listed-vec-functional-vec n) ~ id
    is-retraction-functional-vec-vec zero-ℕ v = {!!}

  is-equiv-listed-vec-functional-vec :
    (n : ℕ) → is-equiv (listed-vec-functional-vec n)
  is-equiv-listed-vec-functional-vec n = {!!}

  is-equiv-functional-vec-vec :
    (n : ℕ) → is-equiv (functional-vec-vec n)
  is-equiv-functional-vec-vec n = {!!}

  compute-vec : (n : ℕ) → functional-vec A n ≃ vec A n
  pr1 (compute-vec n) = {!!}
```

### Characterizing the elementhood predicate

```agda
  is-in-functional-vec-is-in-vec :
    (n : ℕ) (v : vec A n) (x : A) →
    (x ∈-vec v) → (in-functional-vec n x (functional-vec-vec n v))
  is-in-functional-vec-is-in-vec (succ-ℕ n) (y ∷ l) x (is-head .x l) = {!!}

  is-in-vec-is-in-functional-vec :
    (n : ℕ) (v : vec A n) (x : A) →
    (in-functional-vec n x (functional-vec-vec n v)) → (x ∈-vec v)
  is-in-vec-is-in-functional-vec (succ-ℕ n) (y ∷ v) x (inl k , p) = {!!}
```

### The type of vectors of elements in a truncated type is truncated

#### The type of listed vectors of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-Eq-vec :
    (k : 𝕋) (n : ℕ) → is-trunc (succ-𝕋 k) A →
    (u v : vec A n) → is-trunc (k) (Eq-vec n u v)
  is-trunc-Eq-vec k zero-ℕ A-trunc empty-vec empty-vec = {!!}

  center-is-contr-vec :
    {n : ℕ} → is-contr A → vec A n
  center-is-contr-vec {zero-ℕ} H = {!!}

  contraction-is-contr-vec' :
    {n : ℕ} (H : is-contr A) → (v : vec A n) →
    Eq-vec n (center-is-contr-vec H) v
  contraction-is-contr-vec' {zero-ℕ} H empty-vec = {!!}

  contraction-is-contr-vec :
    {n : ℕ} (H : is-contr A) → (v : vec A n) → (center-is-contr-vec H) ＝ v
  contraction-is-contr-vec {n} H v = {!!}

  is-contr-vec :
    {n : ℕ} → is-contr A → is-contr (vec A n)
  pr1 (is-contr-vec H) = {!!}

  is-trunc-vec :
    (k : 𝕋) → (n : ℕ) → is-trunc k A → is-trunc k (vec A n)
  is-trunc-vec neg-two-𝕋 n H = {!!}
```

#### The type of functional vectors of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-functional-vec :
    (k : 𝕋) (n : ℕ) → is-trunc k A → is-trunc k (functional-vec A n)
  is-trunc-functional-vec k n H = {!!}
```

### The type of vectors of elements in a set is a set

#### The type of listed vectors of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-vec : (n : ℕ) → is-set A -> is-set (vec A n)
  is-set-vec = {!!}

vec-Set : {l : Level} → Set l → ℕ → Set l
pr1 (vec-Set A n) = {!!}
pr2 (vec-Set A n) = {!!}
```

#### The type of functional vectors of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-functional-vec : (n : ℕ) → is-set A → is-set (functional-vec A n)
  is-set-functional-vec = {!!}

functional-vec-Set : {l : Level} → Set l → ℕ → Set l
pr1 (functional-vec-Set A n) = {!!}
pr2 (functional-vec-Set A n) = {!!}
```

### Adding the tail to the head gives the same vector

#### Adding the tail to the head gives the same listed vector

```agda
module _
  {l : Level} {A : UU l}
  where

  cons-head-tail-vec :
    (n : ℕ) →
    (v : vec A (succ-ℕ n)) →
    ((head-vec v) ∷ (tail-vec v)) ＝ v
  cons-head-tail-vec n (x ∷ v) = {!!}
```

#### Adding the tail to the head gives the same functional vector

```agda
module _
  {l : Level} {A : UU l}
  where
  htpy-cons-head-tail-functional-vec :
    ( n : ℕ) →
    ( v : functional-vec A (succ-ℕ n)) →
    ( cons-functional-vec n
      ( head-functional-vec n v)
      ( tail-functional-vec n v)) ~
      ( v)
  htpy-cons-head-tail-functional-vec n v (inl x) = {!!}

  cons-head-tail-functional-vec :
    ( n : ℕ) →
    ( v : functional-vec A (succ-ℕ n)) →
    ( cons-functional-vec n
      ( head-functional-vec n v)
      ( tail-functional-vec n v)) ＝
      ( v)
  cons-head-tail-functional-vec n v = {!!}
```

### Computing the transport of a vector over its size

```agda
compute-tr-vec :
  {l : Level} {A : UU l}
  {n m : ℕ} (p : succ-ℕ n ＝ succ-ℕ m) (v : vec A n) (x : A) →
  tr (vec A) p (x ∷ v) ＝
  (x ∷ tr (vec A) (is-injective-succ-ℕ p) v)
compute-tr-vec refl v x = {!!}
```
