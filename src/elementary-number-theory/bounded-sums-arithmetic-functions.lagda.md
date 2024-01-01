# Bounded sums of arithmetic functions

```agda
module elementary-number-theory.bounded-sums-arithmetic-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-functions
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.function-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

Given a decidable predicate `P` on the nonzero natural numbers, and a map `f`
from the nonzero natural numbers in `P` into a ring `R`, the bounded sum is a
summation of the values of `f` up to an upper bound `b`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  restricted-arithmetic-function-Ring :
    {l' : Level} (P : nonzero-ℕ → Decidable-Prop l') → UU (l ⊔ l')
  restricted-arithmetic-function-Ring = {!!}

  shift-arithmetic-function-Ring :
    type-arithmetic-functions-Ring R → type-arithmetic-functions-Ring R
  shift-arithmetic-function-Ring = {!!}

  shift-restricted-arithmetic-function-Ring :
    {l' : Level} (P : nonzero-ℕ → Decidable-Prop l') →
    restricted-arithmetic-function-Ring P →
    restricted-arithmetic-function-Ring (P ∘ succ-nonzero-ℕ)
  shift-restricted-arithmetic-function-Ring = {!!}

  case-one-bounded-sum-arithmetic-function-Ring :
    {l' : Level} → (P : Decidable-Prop l') →
    is-decidable (type-Decidable-Prop P) →
    (type-Decidable-Prop P → type-Ring R) → type-Ring R
  case-one-bounded-sum-arithmetic-function-Ring = {!!}

  bounded-sum-arithmetic-function-Ring :
    (b : ℕ) {l' : Level} (P : nonzero-ℕ → Decidable-Prop l')
    (f : restricted-arithmetic-function-Ring P) → type-Ring R
  bounded-sum-arithmetic-function-Ring = {!!}
```
