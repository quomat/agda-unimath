# Greatest lower bounds in large posets

```agda
module order-theory.greatest-lower-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
open import order-theory.lower-bounds-large-posets
```

</details>

## Idea

A **greatest binary lower bound** of two elements `a` and `b` in a large poset
`P` is an element `x` such that for every element `y` in `P` the logical
equivalence

```text
  is-binary-lower-bound-Large-Poset P a b y ↔ y ≤ x
```

holds.

## Definitions

### The predicate that an element of a large poset is the greatest lower bound of two elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-greatest-binary-lower-bound-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → UUω
  is-greatest-binary-lower-bound-Large-Poset = {!!}
```

## Properties

### Any pointwise greatest lower bound of two elements in a dependent product of large posets is a greatest lower bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  {l1 l2 l3 : Level}
  (x : type-Π-Large-Poset P l1)
  (y : type-Π-Large-Poset P l2)
  (z : type-Π-Large-Poset P l3)
  where

  is-greatest-binary-lower-bound-Π-Large-Poset :
    ( (i : I) →
      is-greatest-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)) →
    is-greatest-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z
  is-greatest-binary-lower-bound-Π-Large-Poset = {!!}
```
