# Cubes

```agda
module univalent-combinatorics.cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.finite-types
```

</details>

## Definitions

### Cubes

```agda
cube : ℕ → UU (lsuc lzero)
cube k = {!!}

module _
  (k : ℕ) (X : cube k)
  where

  dim-cube-UU-Fin : UU-Fin lzero k
  dim-cube-UU-Fin = {!!}

  dim-cube : UU lzero
  dim-cube = {!!}

  has-cardinality-dim-cube : has-cardinality k dim-cube
  has-cardinality-dim-cube = {!!}

  has-finite-cardinality-dim-cube : has-finite-cardinality dim-cube
  has-finite-cardinality-dim-cube = {!!}

  is-finite-dim-cube : is-finite dim-cube
  is-finite-dim-cube = {!!}

  axis-cube-UU-2 : dim-cube → UU-Fin lzero 2
  axis-cube-UU-2 = {!!}

  axis-cube : dim-cube → UU lzero
  axis-cube d = {!!}

  has-cardinality-axis-cube : (d : dim-cube) → has-cardinality 2 (axis-cube d)
  has-cardinality-axis-cube d = {!!}

  has-finite-cardinality-axis-cube :
    (d : dim-cube) → has-finite-cardinality (axis-cube d)
  has-finite-cardinality-axis-cube = {!!}

  is-finite-axis-cube : (d : dim-cube) → is-finite (axis-cube d)
  is-finite-axis-cube d = {!!}

  vertex-cube : UU lzero
  vertex-cube = {!!}
```

### The standard cube

```agda
dim-standard-cube-UU-Fin : (k : ℕ) → UU-Fin lzero k
dim-standard-cube-UU-Fin k = {!!}

dim-standard-cube : ℕ → UU lzero
dim-standard-cube k = {!!}

axis-standard-cube-UU-Fin : (k : ℕ) → dim-standard-cube k → UU-Fin lzero 2
axis-standard-cube-UU-Fin k d = {!!}

axis-standard-cube : (k : ℕ) → dim-standard-cube k → UU lzero
axis-standard-cube k d = {!!}

standard-cube : (k : ℕ) → cube k
standard-cube k = {!!}

{-
mere-equiv-standard-cube :
  {k : ℕ} (X : cube k) → type-trunc-Prop (equiv-cube (standard-cube k) X)
mere-equiv-standard-cube = {!!}
-}
```

### Faces of cubes

```agda
face-cube :
  (k : ℕ) (X : cube (succ-ℕ k)) (d : dim-cube (succ-ℕ k) X)
  (a : axis-cube (succ-ℕ k) X d) → cube k
face-cube = {!!}
```
