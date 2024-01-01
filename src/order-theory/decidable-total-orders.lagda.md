# Decidable total orders

```agda
module order-theory.decidable-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-posets
open import order-theory.decidable-total-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Idea

A **decidable total order** is a [total order](order-theory.total-orders.md) of
which the inequality [relation](foundation.binary-relations.md) is
[decidable](foundation.decidable-relations.md).

## Definitions

### The predicate on posets of being decidable total orders

```agda
is-decidable-total-prop-Poset : {l1 l2 : Level} → Poset l1 l2 → Prop (l1 ⊔ l2)
is-decidable-total-prop-Poset = {!!}

is-decidable-total-Poset : {l1 l2 : Level} → Poset l1 l2 → UU (l1 ⊔ l2)
is-decidable-total-Poset = {!!}

is-prop-is-decidable-total-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) → is-prop (is-decidable-total-Poset P)
is-prop-is-decidable-total-Poset = {!!}
```

### The type of decidable total orders

```agda
Decidable-Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Total-Order = {!!}

module _
  {l1 l2 : Level} (P : Decidable-Total-Order l1 l2)
  where

  poset-Decidable-Total-Order : Poset l1 l2
  poset-Decidable-Total-Order = {!!}

  is-total-poset-Decidable-Total-Order :
    is-total-Poset (poset-Decidable-Total-Order)
  is-total-poset-Decidable-Total-Order = {!!}

  is-decidable-poset-Decidable-Total-Order :
    is-decidable-leq-Poset (poset-Decidable-Total-Order)
  is-decidable-poset-Decidable-Total-Order = {!!}

  type-Decidable-Total-Order : UU l1
  type-Decidable-Total-Order = {!!}

  leq-Decidable-Total-Order-Prop :
    (x y : type-Decidable-Total-Order) → Prop l2
  leq-Decidable-Total-Order-Prop = {!!}

  leq-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) → UU l2
  leq-Decidable-Total-Order = {!!}

  is-prop-leq-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    is-prop (leq-Decidable-Total-Order x y)
  is-prop-leq-Decidable-Total-Order = {!!}

  le-Decidable-Total-Order-Prop :
    (x y : type-Decidable-Total-Order) → Prop (l1 ⊔ l2)
  le-Decidable-Total-Order-Prop = {!!}

  le-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) → UU (l1 ⊔ l2)
  le-Decidable-Total-Order = {!!}

  is-prop-le-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    is-prop (le-Decidable-Total-Order x y)
  is-prop-le-Decidable-Total-Order = {!!}

  decidable-poset-Decidable-Total-Order : Decidable-Poset l1 l2
  decidable-poset-Decidable-Total-Order = {!!}

  leq-total-decidable-poset-decidable-Prop :
    (x y : type-Decidable-Total-Order) → Decidable-Prop l2
  leq-total-decidable-poset-decidable-Prop = {!!}

  concatenate-eq-leq-Decidable-Total-Order :
    {x y z : type-Decidable-Total-Order} → x ＝ y →
    leq-Decidable-Total-Order y z → leq-Decidable-Total-Order x z
  concatenate-eq-leq-Decidable-Total-Order = {!!}

  concatenate-leq-eq-Decidable-Total-Order :
    {x y z : type-Decidable-Total-Order} →
    leq-Decidable-Total-Order x y → y ＝ z → leq-Decidable-Total-Order x z
  concatenate-leq-eq-Decidable-Total-Order = {!!}

  refl-leq-Decidable-Total-Order : is-reflexive leq-Decidable-Total-Order
  refl-leq-Decidable-Total-Order = {!!}

  transitive-leq-Decidable-Total-Order : is-transitive leq-Decidable-Total-Order
  transitive-leq-Decidable-Total-Order = {!!}

  preorder-Decidable-Total-Order : Preorder l1 l2
  preorder-Decidable-Total-Order = {!!}

  decidable-total-preorder-Decidable-Total-Order :
    Decidable-Total-Preorder l1 l2
  decidable-total-preorder-Decidable-Total-Order = {!!}

  leq-or-strict-greater-Decidable-Poset :
    (x y : type-Decidable-Total-Order) → UU (l1 ⊔ l2)
  leq-or-strict-greater-Decidable-Poset = {!!}

  is-leq-or-strict-greater-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    leq-or-strict-greater-Decidable-Poset x y
  is-leq-or-strict-greater-Decidable-Total-Order = {!!}

  antisymmetric-leq-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    leq-Decidable-Total-Order x y → leq-Decidable-Total-Order y x → Id x y
  antisymmetric-leq-Decidable-Total-Order = {!!}

  is-prop-leq-or-strict-greater-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    is-prop (leq-or-strict-greater-Decidable-Poset x y)
  is-prop-leq-or-strict-greater-Decidable-Total-Order = {!!}

  is-set-type-Decidable-Total-Order : is-set type-Decidable-Total-Order
  is-set-type-Decidable-Total-Order = {!!}

  set-Decidable-Total-Order : Set l1
  set-Decidable-Total-Order = {!!}
```
