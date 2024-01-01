# Maximal chains in preorders

```agda
module order-theory.maximal-chains-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.chains-preorders
open import order-theory.preorders
```

</details>

## Idea

A **maximal chain** in a preorder `P` is a chain `C` in `P` such that for every
chain `D` in `P` we have `C ⊆ D ⇒ D ⊆ C`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-maximal-chain-Preorder-Prop :
    {l3 : Level} → chain-Preorder l3 X → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Preorder-Prop = {!!}

  is-maximal-chain-Preorder :
    {l3 : Level} → chain-Preorder l3 X → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Preorder = {!!}

  is-prop-is-maximal-chain-Preorder :
    {l3 : Level} (C : chain-Preorder l3 X) →
    is-prop (is-maximal-chain-Preorder C)
  is-prop-is-maximal-chain-Preorder = {!!}

maximal-chain-Preorder :
  {l1 l2 : Level} (l3 : Level) (X : Preorder l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
maximal-chain-Preorder = {!!}

module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (C : maximal-chain-Preorder l3 X)
  where

  chain-maximal-chain-Preorder : chain-Preorder l3 X
  chain-maximal-chain-Preorder = {!!}

  is-maximal-chain-maximal-chain-Preorder :
    is-maximal-chain-Preorder X chain-maximal-chain-Preorder
  is-maximal-chain-maximal-chain-Preorder = {!!}

  type-maximal-chain-Preorder : UU (l1 ⊔ l3)
  type-maximal-chain-Preorder = {!!}
```
