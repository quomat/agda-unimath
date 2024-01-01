# Dependent products of large posets

```agda
module order-theory.dependent-products-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.large-binary-relations
open import foundation.universe-levels

open import order-theory.dependent-products-large-preorders
open import order-theory.large-posets
open import order-theory.large-preorders
```

</details>

## Idea

Given a family `P : I → Large-Poset α β` indexed by a type `I : UU l`, the
dependent product of the large posets `P i` is again a large poset.

## Definitions

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  where

  large-preorder-Π-Large-Poset :
    Large-Preorder (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  large-preorder-Π-Large-Poset = {!!}

  type-Π-Large-Poset : (l1 : Level) → UU (α l1 ⊔ l)
  type-Π-Large-Poset = {!!}

  leq-prop-Π-Large-Poset :
    Large-Relation-Prop
      ( λ l1 → α l1 ⊔ l)
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Poset)
  leq-prop-Π-Large-Poset = {!!}

  leq-Π-Large-Poset :
    Large-Relation
      ( λ l1 → α l1 ⊔ l)
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Poset)
  leq-Π-Large-Poset = {!!}

  is-prop-leq-Π-Large-Poset :
    is-prop-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  is-prop-leq-Π-Large-Poset = {!!}

  refl-leq-Π-Large-Poset :
    is-reflexive-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  refl-leq-Π-Large-Poset = {!!}

  transitive-leq-Π-Large-Poset :
    is-transitive-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  transitive-leq-Π-Large-Poset = {!!}

  antisymmetric-leq-Π-Large-Poset :
    is-antisymmetric-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  antisymmetric-leq-Π-Large-Poset = {!!}

  Π-Large-Poset : Large-Poset (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  Π-Large-Poset = {!!}
```
