# Products of equivalence relataions

```agda
module foundation.products-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.products-binary-relations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalence-relations
```

</details>

## Idea

Given two equivalence relations `R` and `S`, their product is an equivalence
relation.

## Definition

### The product of two equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  reflexive-prod-Relation-Prop :
    is-reflexive-Relation-Prop
      ( prod-Relation-Prop
        ( prop-equivalence-relation R)
        ( prop-equivalence-relation S))
  pr1 (reflexive-prod-Relation-Prop x) = {!!}

  symmetric-prod-Relation-Prop :
    is-symmetric-Relation-Prop
      ( prod-Relation-Prop
        ( prop-equivalence-relation R)
        ( prop-equivalence-relation S))
  pr1 (symmetric-prod-Relation-Prop x y (p , q)) = {!!}

  transitive-prod-Relation-Prop :
    is-transitive-Relation-Prop
      ( prod-Relation-Prop
        ( prop-equivalence-relation R)
        ( prop-equivalence-relation S))
  pr1 (transitive-prod-Relation-Prop x y z (p , q) (p' , q')) = {!!}

  prod-equivalence-relation : equivalence-relation (l2 ⊔ l4) (A × B)
  pr1 prod-equivalence-relation = {!!}
```
