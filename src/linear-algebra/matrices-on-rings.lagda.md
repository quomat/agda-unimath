# Matrices on rings

```agda
module linear-algebra.matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.constant-matrices
open import linear-algebra.functoriality-matrices
open import linear-algebra.matrices
open import linear-algebra.vectors
open import linear-algebra.vectors-on-rings

open import ring-theory.rings
```

</details>

## Definitions

### Matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  matrix-Ring : ℕ → ℕ → UU l
  matrix-Ring m n = {!!}
```

### The zero matrix

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-matrix-Ring : {m n : ℕ} → matrix-Ring R m n
  zero-matrix-Ring = {!!}
```

### Addition of matrices on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-matrix-Ring : {m n : ℕ} (A B : matrix-Ring R m n) → matrix-Ring R m n
  add-matrix-Ring = {!!}
```

## Properties

### Addition of matrices is associative

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-matrix-Ring :
    {m n : ℕ} (A B C : matrix-Ring R m n) →
    Id
      ( add-matrix-Ring R (add-matrix-Ring R A B) C)
      ( add-matrix-Ring R A (add-matrix-Ring R B C))
  associative-add-matrix-Ring empty-vec empty-vec empty-vec = {!!}
```

### Addition of matrices is commutative

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-matrix-Ring :
    {m n : ℕ} (A B : matrix-Ring R m n) →
    Id (add-matrix-Ring R A B) (add-matrix-Ring R B A)
  commutative-add-matrix-Ring empty-vec empty-vec = {!!}
```

### Left unit law for addition of matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-matrix-Ring :
    {m n : ℕ} (A : matrix-Ring R m n) →
    Id (add-matrix-Ring R (zero-matrix-Ring R) A) A
  left-unit-law-add-matrix-Ring empty-vec = {!!}
```

### Right unit law for addition of matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-unit-law-add-matrix-Ring :
    {m n : ℕ} (A : matrix-Ring R m n) →
    Id (add-matrix-Ring R A (zero-matrix-Ring R)) A
  right-unit-law-add-matrix-Ring empty-vec = {!!}
```
