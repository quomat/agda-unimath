# Top elements in large posets

```agda
module order-theory.top-elements-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
```

</details>

## Idea

We say that a [large poset](order-theory.large-posets.md) `P` has a **largest
element** if it comes equipped with an element `t : type-Large-Poset P lzero`
such that `x ≤ t` holds for every `x : P`

## Definition

### The predicate on elements of posets of being a top element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  is-top-element-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → UUω
  is-top-element-Large-Poset = {!!}
```

### The predicate on posets of having a top element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  where

  record
    has-top-element-Large-Poset : UUω
    where
    field
      top-has-top-element-Large-Poset :
        type-Large-Poset P lzero
      top-has-top-element-Large-Poset = {!!}
```
