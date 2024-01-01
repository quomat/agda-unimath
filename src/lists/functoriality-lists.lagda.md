# Functoriality of the list operation

```agda
module lists.functoriality-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import lists.arrays
open import lists.concatenation-lists
open import lists.lists
```

</details>

## Idea

Given a functiion `f : A → B`, we obtain a function
`map-list f : list A → list B`.

## Definition

```agda
map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
map-list = {!!}
```

## Properties

### `map-list` preserves the length of a list

```agda
length-map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (l : list A) →
  Id (length-list (map-list f l)) (length-list l)
length-map-list = {!!}
```

### Link between `map-list` and `map-vec`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  where

  map-list-map-vec-list :
    (l : list A) →
    list-vec (length-list l) (map-vec f (vec-list l)) ＝
    map-list f l
  map-list-map-vec-list = {!!}

  map-vec-map-list-vec :
    (n : ℕ) (v : vec A n) →
    tr
      ( vec B)
      ( length-map-list f (list-vec n v) ∙
        compute-length-list-list-vec n v)
      ( vec-list (map-list f (list-vec n v))) ＝
    map-vec f v
  map-vec-map-list-vec = {!!}

  map-vec-map-list-vec' :
    (n : ℕ) (v : vec A n) →
    vec-list (map-list f (list-vec n v)) ＝
    tr
      ( vec B)
      ( inv
        ( length-map-list f (list-vec n v) ∙
          compute-length-list-list-vec n v))
      ( map-vec f v)
  map-vec-map-list-vec' = {!!}

  vec-list-map-list-map-vec-list :
    (l : list A) →
    tr
      ( vec B)
      ( length-map-list f l)
      ( vec-list (map-list f l)) ＝
    map-vec f (vec-list l)
  vec-list-map-list-map-vec-list = {!!}

  vec-list-map-list-map-vec-list' :
    (l : list A) →
    vec-list (map-list f l) ＝
    tr
      ( vec B)
      ( inv (length-map-list f l))
      ( map-vec f (vec-list l))
  vec-list-map-list-map-vec-list' = {!!}

  list-vec-map-vec-map-list-vec :
    (n : ℕ) (v : vec A n) →
    list-vec
      ( length-list (map-list f (list-vec n v)))
      ( vec-list (map-list f (list-vec n v))) ＝
    list-vec n (map-vec f v)
  list-vec-map-vec-map-list-vec = {!!}
```

### `map-list` preserves concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-concat-map-list :
    (l k : list A) →
    Id
      ( map-list f (concat-list l k))
      ( concat-list (map-list f l) (map-list f k))
  preserves-concat-map-list = {!!}
```

### Functoriality of the list operation

First we introduce the functoriality of the list operation, because it will come
in handy when we try to define and prove more advanced things.

```agda
identity-law-map-list :
  {l1 : Level} {A : UU l1} →
  map-list (id {A = A}) ~ id
identity-law-map-list nil = {!!}
identity-law-map-list (cons a x) = {!!}

composition-law-map-list :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (f : A → B) (g : B → C) →
  map-list (g ∘ f) ~ (map-list g ∘ map-list f)
composition-law-map-list = {!!}
```

### `map-list` applied to lists of the form `snoc x a`

```agda
map-snoc-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : list A) (a : A) →
  map-list f (snoc x a) ＝ snoc (map-list f x) (f a)
map-snoc-list = {!!}
```
