# Dependent products large preorders

```agda
module order-theory.dependent-products-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

Given a family `P : I → Large-Preorder α β` of large preorders indexed by a type
`I : UU l`, the dependent prodcut of the large preorders `P i` is again a large
preorder.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Preorder α β)
  where

  type-Π-Large-Preorder : (l1 : Level) → UU (α l1 ⊔ l)
  type-Π-Large-Preorder = {!!}

  leq-prop-Π-Large-Preorder :
    Large-Relation-Prop
      ( λ l1 → α l1 ⊔ l)
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Preorder)
  leq-prop-Π-Large-Preorder = {!!}

  leq-Π-Large-Preorder :
    Large-Relation
      ( λ l1 → α l1 ⊔ l)
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Preorder)
  leq-Π-Large-Preorder = {!!}

  is-prop-leq-Π-Large-Preorder :
    is-prop-Large-Relation type-Π-Large-Preorder leq-Π-Large-Preorder
  is-prop-leq-Π-Large-Preorder = {!!}

  refl-leq-Π-Large-Preorder :
    is-reflexive-Large-Relation type-Π-Large-Preorder leq-Π-Large-Preorder
  refl-leq-Π-Large-Preorder = {!!}

  transitive-leq-Π-Large-Preorder :
    is-transitive-Large-Relation type-Π-Large-Preorder leq-Π-Large-Preorder
  transitive-leq-Π-Large-Preorder = {!!}

  Π-Large-Preorder : Large-Preorder (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  Π-Large-Preorder = {!!}
  leq-prop-Large-Preorder Π-Large-Preorder = {!!}
  refl-leq-Large-Preorder Π-Large-Preorder = {!!}
  transitive-leq-Large-Preorder Π-Large-Preorder = {!!}
```
