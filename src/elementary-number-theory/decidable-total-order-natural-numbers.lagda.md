# The decidable total order of natural numbers

```agda
module elementary-number-theory.decidable-total-order-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-total-orders
open import order-theory.total-orders
```

</details>

## Idea

The type of [natural numbers](elementary-number-theory.natural-numbers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-natural-numbers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

```agda
is-total-leq-ℕ : is-total-Poset ℕ-Poset
is-total-leq-ℕ n m = {!!}

ℕ-Total-Order : Total-Order lzero lzero
pr1 ℕ-Total-Order = {!!}
pr2 ℕ-Total-Order = {!!}

ℕ-Decidable-Total-Order : Decidable-Total-Order lzero lzero
pr1 ℕ-Decidable-Total-Order = {!!}
pr1 (pr2 ℕ-Decidable-Total-Order) = {!!}
pr2 (pr2 ℕ-Decidable-Total-Order) = {!!}
```
