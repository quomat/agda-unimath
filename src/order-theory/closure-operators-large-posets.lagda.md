# Closure operators on large posets

```agda
module order-theory.closure-operators-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-subpreorders
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

A **closure operator** on a [large poset](order-theory.large-posets.md) `P`
consists of an order preserving map `cl : P → P` such that

1. `cl` is increasing, i.e., `x ≤ cl x` for each `x : P`, and
2. `cl` is idempotent, i.e., `cl (cl x) ＝ cl x` for each `x : P`.

In other words, closure operators are idempotent monads on (large) posets.

## Definitions

### Closure operators on large posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  where

  record
    closure-operator-Large-Poset : UUω
    where
    field
      hom-closure-operator-Large-Poset :
        hom-Large-Poset (λ l → l) P P
      hom-closure-operator-Large-Poset = {!!}

    preserves-order-closure-operator-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      leq-Large-Poset P x y →
      leq-Large-Poset P
        ( map-closure-operator-Large-Poset x)
        ( map-closure-operator-Large-Poset y)
    preserves-order-closure-operator-Large-Poset = {!!}
```

### The large subposet of closed elements of a closure operator

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (cl : closure-operator-Large-Poset P)
  where

  large-subpreorder-closure-operator-Large-Poset :
    Large-Subpreorder α (large-preorder-Large-Poset P)
  large-subpreorder-closure-operator-Large-Poset = {!!}

  is-closed-element-closure-operator-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → UU (α l1)
  is-closed-element-closure-operator-Large-Poset = {!!}

  is-prop-is-closed-element-closure-operator-Large-Poset :
    {l1 : Level} (x : type-Large-Poset P l1) →
    is-prop (is-closed-element-closure-operator-Large-Poset x)
  is-prop-is-closed-element-closure-operator-Large-Poset = {!!}

  is-closed-element-leq-closure-operator-Large-Poset :
    {l1 : Level} (x : type-Large-Poset P l1) →
    leq-Large-Poset P (map-closure-operator-Large-Poset P cl x) x →
    is-closed-element-closure-operator-Large-Poset x
  is-closed-element-leq-closure-operator-Large-Poset = {!!}

  closed-element-closure-operator-Large-Poset :
    (l1 : Level) → UU (α l1)
  closed-element-closure-operator-Large-Poset = {!!}

  is-closed-under-sim-closure-operator-Large-Poset :
    {l1 l2 : Level}
    (x : type-Large-Poset P l1)
    (y : type-Large-Poset P l2) →
    leq-Large-Poset P x y → leq-Large-Poset P y x →
    is-closed-element-closure-operator-Large-Poset x →
    is-closed-element-closure-operator-Large-Poset y
  is-closed-under-sim-closure-operator-Large-Poset = {!!}

  large-subposet-closure-operator-Large-Poset :
    Large-Subposet α P
  large-subposet-closure-operator-Large-Poset = {!!}

  large-poset-closure-operator-Large-Poset :
    Large-Poset α β
  large-poset-closure-operator-Large-Poset = {!!}

  leq-prop-closed-element-closure-operator-Large-Poset :
    Large-Relation-Prop α β closed-element-closure-operator-Large-Poset
  leq-prop-closed-element-closure-operator-Large-Poset = {!!}

  leq-closed-element-closure-operator-Large-Poset :
    Large-Relation α β closed-element-closure-operator-Large-Poset
  leq-closed-element-closure-operator-Large-Poset = {!!}

  is-prop-leq-closed-element-closure-operator-Large-Poset :
    is-prop-Large-Relation
      ( closed-element-closure-operator-Large-Poset)
      ( leq-closed-element-closure-operator-Large-Poset)
  is-prop-leq-closed-element-closure-operator-Large-Poset = {!!}

  refl-leq-closed-element-closure-operator-Large-Poset :
    is-reflexive-Large-Relation
      ( closed-element-closure-operator-Large-Poset)
      ( leq-closed-element-closure-operator-Large-Poset)
  refl-leq-closed-element-closure-operator-Large-Poset = {!!}

  antisymmetric-leq-closed-element-closure-operator-Large-Poset :
    is-antisymmetric-Large-Relation
      ( closed-element-closure-operator-Large-Poset)
      ( leq-closed-element-closure-operator-Large-Poset)
  antisymmetric-leq-closed-element-closure-operator-Large-Poset = {!!}

  transitive-leq-closed-element-closure-operator-Large-Poset :
    is-transitive-Large-Relation
      ( closed-element-closure-operator-Large-Poset)
      ( leq-closed-element-closure-operator-Large-Poset)
  transitive-leq-closed-element-closure-operator-Large-Poset = {!!}
```
