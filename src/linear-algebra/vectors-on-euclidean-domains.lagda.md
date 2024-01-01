# Vectors on euclidean domains

```agda
module linear-algebra.vectors-on-euclidean-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.euclidean-domains

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors
```

</details>

## Idea

Given an euclidean domain `R`, the type `vec n R` of `R`-vectors is an
`R`-module.

## Definitions

### Listed vectors on euclidean domains

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  vec-Euclidean-Domain : ℕ → UU l
  vec-Euclidean-Domain = {!!}

  head-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain (succ-ℕ n) → type-Euclidean-Domain R
  head-vec-Euclidean-Domain = {!!}

  tail-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain (succ-ℕ n) → vec-Euclidean-Domain n
  tail-vec-Euclidean-Domain = {!!}

  snoc-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain n →
    type-Euclidean-Domain R → vec-Euclidean-Domain (succ-ℕ n)
  snoc-vec-Euclidean-Domain = {!!}
```

### Functional vectors on euclidean domains

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  functional-vec-Euclidean-Domain : ℕ → UU l
  functional-vec-Euclidean-Domain = {!!}

  head-functional-vec-Euclidean-Domain :
    (n : ℕ) →
    functional-vec-Euclidean-Domain (succ-ℕ n) →
    type-Euclidean-Domain R
  head-functional-vec-Euclidean-Domain = {!!}

  tail-functional-vec-Euclidean-Domain :
    (n : ℕ) →
    functional-vec-Euclidean-Domain (succ-ℕ n) →
    functional-vec-Euclidean-Domain n
  tail-functional-vec-Euclidean-Domain = {!!}

  cons-functional-vec-Euclidean-Domain :
    (n : ℕ) → type-Euclidean-Domain R →
    functional-vec-Euclidean-Domain n →
    functional-vec-Euclidean-Domain (succ-ℕ n)
  cons-functional-vec-Euclidean-Domain = {!!}

  snoc-functional-vec-Euclidean-Domain :
    (n : ℕ) → functional-vec-Euclidean-Domain n → type-Euclidean-Domain R →
    functional-vec-Euclidean-Domain (succ-ℕ n)
  snoc-functional-vec-Euclidean-Domain = {!!}
```

### Zero vector on a euclidean domain

#### The zero listed vector

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-vec-Euclidean-Domain : {n : ℕ} → vec-Euclidean-Domain R n
  zero-vec-Euclidean-Domain = {!!}
```

#### The zero functional vector

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-functional-vec-Euclidean-Domain :
    (n : ℕ) → functional-vec-Euclidean-Domain R n
  zero-functional-vec-Euclidean-Domain = {!!}
```

### Pointwise addition of vectors on a euclidean domain

#### Pointwise addition of listed vectors on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-vec-Euclidean-Domain :
    {n : ℕ} →
    vec-Euclidean-Domain R n →
    vec-Euclidean-Domain R n →
    vec-Euclidean-Domain R n
  add-vec-Euclidean-Domain = {!!}

  associative-add-vec-Euclidean-Domain :
    {n : ℕ} (v1 v2 v3 : vec-Euclidean-Domain R n) →
    Id
      ( add-vec-Euclidean-Domain (add-vec-Euclidean-Domain v1 v2) v3)
      ( add-vec-Euclidean-Domain v1 (add-vec-Euclidean-Domain v2 v3))
  associative-add-vec-Euclidean-Domain = {!!}

  vec-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  vec-Euclidean-Domain-Semigroup = {!!}

  left-unit-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id (add-vec-Euclidean-Domain (zero-vec-Euclidean-Domain R) v) v
  left-unit-law-add-vec-Euclidean-Domain = {!!}

  right-unit-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id (add-vec-Euclidean-Domain v (zero-vec-Euclidean-Domain R)) v
  right-unit-law-add-vec-Euclidean-Domain = {!!}

  vec-Euclidean-Domain-Monoid : ℕ → Monoid l
  vec-Euclidean-Domain-Monoid = {!!}

  commutative-add-vec-Euclidean-Domain :
    {n : ℕ} (v w : vec-Euclidean-Domain R n) →
    Id (add-vec-Euclidean-Domain v w) (add-vec-Euclidean-Domain w v)
  commutative-add-vec-Euclidean-Domain = {!!}

  vec-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  vec-Euclidean-Domain-Commutative-Monoid = {!!}
```

#### Pointwise addition of functional vectors on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v w : functional-vec-Euclidean-Domain R n) →
    functional-vec-Euclidean-Domain R n
  add-functional-vec-Euclidean-Domain = {!!}

  associative-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v1 v2 v3 : functional-vec-Euclidean-Domain R n) →
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( add-functional-vec-Euclidean-Domain n v1 v2)
      ( v3)) ＝
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( v1)
      ( add-functional-vec-Euclidean-Domain n v2 v3))
  associative-add-functional-vec-Euclidean-Domain = {!!}

  functional-vec-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  functional-vec-Euclidean-Domain-Semigroup = {!!}

  left-unit-law-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v : functional-vec-Euclidean-Domain R n) →
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( zero-functional-vec-Euclidean-Domain R n)
      ( v)) ＝
    ( v)
  left-unit-law-add-functional-vec-Euclidean-Domain = {!!}

  right-unit-law-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v : functional-vec-Euclidean-Domain R n) →
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( v)
      ( zero-functional-vec-Euclidean-Domain R n)) ＝
    ( v)
  right-unit-law-add-functional-vec-Euclidean-Domain = {!!}

  functional-vec-Euclidean-Domain-Monoid : ℕ → Monoid l
  functional-vec-Euclidean-Domain-Monoid = {!!}

  commutative-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v w : functional-vec-Euclidean-Domain R n) →
    add-functional-vec-Euclidean-Domain n v w ＝
    add-functional-vec-Euclidean-Domain n w v
  commutative-add-functional-vec-Euclidean-Domain = {!!}

  functional-vec-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  functional-vec-Euclidean-Domain-Commutative-Monoid = {!!}
```

### The negative of a vector on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  neg-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain R n → vec-Euclidean-Domain R n
  neg-vec-Euclidean-Domain = {!!}

  left-inverse-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id
      ( add-vec-Euclidean-Domain R (neg-vec-Euclidean-Domain v) v)
      ( zero-vec-Euclidean-Domain R)
  left-inverse-law-add-vec-Euclidean-Domain = {!!}

  right-inverse-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id
      ( add-vec-Euclidean-Domain R v (neg-vec-Euclidean-Domain v))
      ( zero-vec-Euclidean-Domain R)
  right-inverse-law-add-vec-Euclidean-Domain = {!!}

  is-unital-vec-Euclidean-Domain :
    (n : ℕ) → is-unital (add-vec-Euclidean-Domain R {n})
  is-unital-vec-Euclidean-Domain = {!!}

  is-group-vec-Euclidean-Domain :
    (n : ℕ) → is-group (vec-Euclidean-Domain-Semigroup R n)
  is-group-vec-Euclidean-Domain = {!!}

  vec-Euclidean-Domain-Group : ℕ → Group l
  vec-Euclidean-Domain-Group = {!!}

  vec-Euclidean-Domain-Ab : ℕ → Ab l
  vec-Euclidean-Domain-Ab = {!!}
```
