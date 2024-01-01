# Diagonal matrices on rings

```agda
module linear-algebra.diagonal-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.matrices-on-rings
open import linear-algebra.vectors
open import linear-algebra.vectors-on-rings

open import ring-theory.rings
```

</details>

## Definitions

### Diagonal matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  diagonal-matrix-Ring : (n : ℕ) → vec-Ring R n → matrix-Ring R n n
  diagonal-matrix-Ring zero-ℕ v = {!!}
```

### Scalar matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  scalar-matrix-Ring : (n : ℕ) → type-Ring R → matrix-Ring R n n
  scalar-matrix-Ring n x = {!!}

  identity-matrix-Ring : (n : ℕ) → matrix-Ring R n n
  identity-matrix-Ring n = {!!}
```
