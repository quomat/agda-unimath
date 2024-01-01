# Transposition of matrices

```agda
module linear-algebra.transposition-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.matrices
open import linear-algebra.vectors
```

</details>

## Idea

The transposition of a matrix is the operation that turns rows into columns and
columns into rows.

## Definition

```agda
transpose-matrix :
  {l : Level} → {A : UU l} → {m n : ℕ} → matrix A m n → matrix A n m
transpose-matrix = {!!}
```

## Properties

```agda
is-involution-transpose-matrix :
  {l : Level} → {A : UU l} → {m n : ℕ} →
  (x : matrix A m n) → Id x (transpose-matrix (transpose-matrix x))
is-involution-transpose-matrix = {!!}

  lemma-rest :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : vec A n) → (xs : matrix A m n) →
    Id (transpose-matrix xs) (map-vec tail-vec (transpose-matrix (x ∷ xs)))
  lemma-rest = {!!}
```
