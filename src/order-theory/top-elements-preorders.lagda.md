# Top elements in preorders

```agda
module order-theory.top-elements-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **largest element** in a preorder `P` is an element `t` such that `x ≤ t`
holds for every `x : P`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-top-element-Preorder-Prop : type-Preorder X → Prop (l1 ⊔ l2)
  is-top-element-Preorder-Prop = {!!}

  is-top-element-Preorder : type-Preorder X → UU (l1 ⊔ l2)
  is-top-element-Preorder = {!!}

  is-prop-is-top-element-Preorder :
    (x : type-Preorder X) → is-prop (is-top-element-Preorder x)
  is-prop-is-top-element-Preorder = {!!}

  has-top-element-Preorder : UU (l1 ⊔ l2)
  has-top-element-Preorder = {!!}
```
