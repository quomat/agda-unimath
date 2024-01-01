# Dirichlet convolution

```agda
module elementary-number-theory.dirichlet-convolution where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-functions
open import elementary-number-theory.bounded-sums-arithmetic-functions
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  dirichlet-convolution-arithmetic-functions-Ring :
    (f g : type-arithmetic-functions-Ring R) →
    type-arithmetic-functions-Ring R
  dirichlet-convolution-arithmetic-functions-Ring f g (pair zero-ℕ H) = {!!}
```
