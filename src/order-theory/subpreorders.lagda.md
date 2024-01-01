# Subpreorders

```agda
module order-theory.subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **subpreorder** of a preorder `P` is a subtype of `P`. By restriction of the
ordering on `P`, the subpreorder inherits the structure of a preorder.

## Definition

### Subpreorders

```agda
Subpreorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ lsuc l3)
Subpreorder = {!!}

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (S : Subpreorder l3 P)
  where

  type-Subpreorder : UU (l1 ⊔ l3)
  type-Subpreorder = {!!}

  eq-type-Subpreorder :
    (x y : type-Subpreorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-type-Subpreorder = {!!}

  leq-Subpreorder-Prop : (x y : type-Subpreorder) → Prop l2
  leq-Subpreorder-Prop = {!!}

  leq-Subpreorder : (x y : type-Subpreorder) → UU l2
  leq-Subpreorder = {!!}

  is-prop-leq-Subpreorder :
    (x y : type-Subpreorder) → is-prop (leq-Subpreorder x y)
  is-prop-leq-Subpreorder = {!!}

  refl-leq-Subpreorder : is-reflexive leq-Subpreorder
  refl-leq-Subpreorder = {!!}

  transitive-leq-Subpreorder : is-transitive leq-Subpreorder
  transitive-leq-Subpreorder = {!!}

  preorder-Subpreorder : Preorder (l1 ⊔ l3) l2
  preorder-Subpreorder = {!!}
```

### Inclusions of subpreorders

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  module _
    {l3 l4 : Level} (S : type-Preorder P → Prop l3)
    (T : type-Preorder P → Prop l4)
    where

    inclusion-Subpreorder-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-Subpreorder-Prop = {!!}

    inclusion-Subpreorder : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Subpreorder = {!!}

    is-prop-inclusion-Subpreorder : is-prop inclusion-Subpreorder
    is-prop-inclusion-Subpreorder = {!!}

  refl-inclusion-Subpreorder :
    {l3 : Level} → is-reflexive (inclusion-Subpreorder {l3})
  refl-inclusion-Subpreorder = {!!}

  transitive-inclusion-Subpreorder :
    {l3 l4 l5 : Level} (S : type-Preorder P → Prop l3)
    (T : type-Preorder P → Prop l4)
    (U : type-Preorder P → Prop l5) →
    inclusion-Subpreorder T U →
    inclusion-Subpreorder S T →
    inclusion-Subpreorder S U
  transitive-inclusion-Subpreorder = {!!}

  Sub-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  Sub-Preorder = {!!}
```
