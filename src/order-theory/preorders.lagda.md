# Preorders

```agda
module order-theory.preorders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **preorder** is a type equipped with a reflexive, transitive relation that is
valued in propositions.

## Definition

```agda
Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preorder l1 l2 = {!!}

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  type-Preorder : UU l1
  type-Preorder = {!!}

  leq-Preorder-Prop : Relation-Prop l2 type-Preorder
  leq-Preorder-Prop = {!!}

  leq-Preorder : (x y : type-Preorder) → UU l2
  leq-Preorder x y = {!!}

  is-prop-leq-Preorder : (x y : type-Preorder) → is-prop (leq-Preorder x y)
  is-prop-leq-Preorder = {!!}

  concatenate-eq-leq-Preorder :
    {x y z : type-Preorder} → x ＝ y → leq-Preorder y z → leq-Preorder x z
  concatenate-eq-leq-Preorder = {!!}

  concatenate-leq-eq-Preorder :
    {x y z : type-Preorder} → leq-Preorder x y → y ＝ z → leq-Preorder x z
  concatenate-leq-eq-Preorder = {!!}

  le-Preorder-Prop : Relation-Prop (l1 ⊔ l2) type-Preorder
  le-Preorder-Prop x y = {!!}

  le-Preorder : Relation (l1 ⊔ l2) type-Preorder
  le-Preorder x y = {!!}

  is-prop-le-Preorder : (x y : type-Preorder) → is-prop (le-Preorder x y)
  is-prop-le-Preorder = {!!}

  is-reflexive-leq-Preorder : is-reflexive (leq-Preorder)
  is-reflexive-leq-Preorder = {!!}

  refl-leq-Preorder : is-reflexive leq-Preorder
  refl-leq-Preorder = {!!}

  is-transitive-leq-Preorder : is-transitive leq-Preorder
  is-transitive-leq-Preorder = {!!}

  transitive-leq-Preorder : is-transitive leq-Preorder
  transitive-leq-Preorder = {!!}
```

## Reasoning with inequalities in preorders

Inequalities in preorders can be constructed by equational reasoning as follows:

```text
calculate-in-Preorder X
  chain-of-inequalities
  x ≤ y
      by ineq-1
      in-Preorder X
    ≤ z
      by ineq-2
      in-Preorder X
    ≤ v
      by ineq-3
      in-Preorder X
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
infixl 1 calculate-in-Preorder_chain-of-inequalities_
infixl 0 step-calculate-in-Preorder

calculate-in-Preorder_chain-of-inequalities_ :
  {l1 l2 : Level} (X : Preorder l1 l2)
  (x : type-Preorder X) → leq-Preorder X x x
calculate-in-Preorder_chain-of-inequalities_ = {!!}

step-calculate-in-Preorder :
  {l1 l2 : Level} (X : Preorder l1 l2)
  {x y : type-Preorder X} → leq-Preorder X x y →
  (z : type-Preorder X) → leq-Preorder X y z → leq-Preorder X x z
step-calculate-in-Preorder = {!!}

syntax step-calculate-in-Preorder X u z v = {!!}
```

## Properties

### Preorders are precategories whose hom-sets are propositions

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  precategory-Preorder : Precategory l1 l2
  pr1 precategory-Preorder = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  ( is-prop-hom-C : (x y : obj-Precategory C) → is-prop (hom-Precategory C x y))
  where

  preorder-is-prop-hom-Precategory : Preorder l1 l2
  pr1 preorder-is-prop-hom-Precategory = {!!}
```

It remains to show that these constructions form inverses to eachother.
