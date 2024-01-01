# Locally finite posets

```agda
module order-theory.locally-finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-posets
open import order-theory.interval-subposets
open import order-theory.posets
```

</details>

## Idea

A poset `X` is said to be **locally finite** if for every `x, y ∈ X`, the
[interval subposet](order-theory.interval-subposets.md) `[x, y]` consisting of
`z : X` such that `x ≤ z ≤ y`, is finite.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-locally-finite-Poset-Prop : Prop (l1 ⊔ l2)
  is-locally-finite-Poset-Prop = {!!}

  is-locally-finite-Poset : UU (l1 ⊔ l2)
  is-locally-finite-Poset = {!!}

  is-prop-is-locally-finite-Poset : is-prop is-locally-finite-Poset
  is-prop-is-locally-finite-Poset = {!!}
```
