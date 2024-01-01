# Decidable preorders

```agda
module order-theory.decidable-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **decidable preorder** is a preorder of which the ordering relation is
decidable.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-decidable-leq-Preorder-Prop : Prop (l1 ⊔ l2)
  is-decidable-leq-Preorder-Prop = {!!}

  is-decidable-leq-Preorder : UU (l1 ⊔ l2)
  is-decidable-leq-Preorder = {!!}

  is-prop-is-decidable-leq-Preorder : is-prop is-decidable-leq-Preorder
  is-prop-is-decidable-leq-Preorder = {!!}

Decidable-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Preorder l1 l2 = {!!}

module _
  {l1 l2 : Level} (X : Decidable-Preorder l1 l2)
  where

  preorder-Decidable-Preorder : Preorder l1 l2
  preorder-Decidable-Preorder = {!!}

  is-decidable-leq-Decidable-Preorder :
    is-decidable-leq-Preorder preorder-Decidable-Preorder
  is-decidable-leq-Decidable-Preorder = {!!}

  type-Decidable-Preorder : UU l1
  type-Decidable-Preorder = {!!}

  leq-Decidable-Preorder-Prop :
    (x y : type-Decidable-Preorder) → Prop l2
  leq-Decidable-Preorder-Prop = {!!}

  leq-Decidable-Preorder :
    (x y : type-Decidable-Preorder) → UU l2
  leq-Decidable-Preorder = {!!}

  is-prop-leq-Decidable-Preorder :
    (x y : type-Decidable-Preorder) →
    is-prop (leq-Decidable-Preorder x y)
  is-prop-leq-Decidable-Preorder = {!!}

  leq-Decidable-Preorder-Decidable-Prop :
    (x y : type-Decidable-Preorder) → Decidable-Prop l2
  leq-Decidable-Preorder-Decidable-Prop = {!!}

  refl-leq-Decidable-Preorder : is-reflexive leq-Decidable-Preorder
  refl-leq-Decidable-Preorder = {!!}

  transitive-leq-Decidable-Preorder : is-transitive leq-Decidable-Preorder
  transitive-leq-Decidable-Preorder = {!!}
```
