# Multisubsets

```agda
module foundation.multisubsets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.images
open import foundation.negated-equality
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.sets

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A multisubset of a given set `U` is a type `B` equipped with a function
`f : B → U`

## Definition

```agda
module _
  {l1 : Level} (l2 : Level)
  where

  multisubset : Set l1 → UU (l1 ⊔ lsuc l2)
  multisubset U = {!!}

  is-locally-finite-multisubset :
    (U : Set l1) → multisubset U → UU (l1 ⊔ l2)
  is-locally-finite-multisubset U (pair B f) = {!!}

  is-finite-multisubset :
    (U : Set l1) → multisubset U → UU (l1 ⊔ l2)
  is-finite-multisubset U (pair B f) = {!!}

module _
  {l1 : Level}
  where

  locally-finite-multisubset : Set l1 → UU l1
  locally-finite-multisubset U = {!!}

  support-locally-finite-multisubset :
    (U : Set l1) → locally-finite-multisubset U → UU l1
  support-locally-finite-multisubset U μ = {!!}

  is-finite-locally-finite-multisubset :
    (U : Set l1) → locally-finite-multisubset U → UU l1
  is-finite-locally-finite-multisubset U μ = {!!}
```
