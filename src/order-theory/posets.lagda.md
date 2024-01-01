# Posets

```agda
module order-theory.posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **poset** is a [set](foundation-core.sets.md)
[equipped](foundation.structure.md) with a reflexive, antisymmetric, transitive
[relation](foundation.binary-relations.md) that takes values in
[propositions](foundation-core.propositions.md).

## Definition

```agda
is-antisymmetric-leq-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) → UU (l1 ⊔ l2)
is-antisymmetric-leq-Preorder = {!!}

Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Poset l1 l2 = {!!}

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  preorder-Poset : Preorder l1 l2
  preorder-Poset = {!!}

  type-Poset : UU l1
  type-Poset = {!!}

  leq-Poset-Prop : (x y : type-Poset) → Prop l2
  leq-Poset-Prop = {!!}

  leq-Poset : (x y : type-Poset) → UU l2
  leq-Poset = {!!}

  is-prop-leq-Poset : (x y : type-Poset) → is-prop (leq-Poset x y)
  is-prop-leq-Poset = {!!}

  concatenate-eq-leq-Poset :
    {x y z : type-Poset} → x ＝ y → leq-Poset y z → leq-Poset x z
  concatenate-eq-leq-Poset = {!!}

  concatenate-leq-eq-Poset :
    {x y z : type-Poset} → leq-Poset x y → y ＝ z → leq-Poset x z
  concatenate-leq-eq-Poset = {!!}

  refl-leq-Poset : is-reflexive leq-Poset
  refl-leq-Poset = {!!}

  transitive-leq-Poset : is-transitive leq-Poset
  transitive-leq-Poset = {!!}

  le-Poset-Prop : (x y : type-Poset) → Prop (l1 ⊔ l2)
  le-Poset-Prop = {!!}

  le-Poset : (x y : type-Poset) → UU (l1 ⊔ l2)
  le-Poset = {!!}

  is-prop-le-Poset :
    (x y : type-Poset) → is-prop (le-Poset x y)
  is-prop-le-Poset = {!!}

  antisymmetric-leq-Poset : is-antisymmetric leq-Poset
  antisymmetric-leq-Poset = {!!}

  is-set-type-Poset : is-set type-Poset
  is-set-type-Poset = {!!}

  set-Poset : Set l1
  pr1 set-Poset = {!!}
```

## Reasoning with inequalities in posets

Inequalities in preorders can be constructed by equational reasoning as follows:

```text
calculate-in-Poset X
  chain-of-inequalities
  x ≤ y
      by ineq-1
      in-Poset X
    ≤ z
      by ineq-2
      in-Poset X
    ≤ v
      by ineq-3
      in-Poset X
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
infixl 1 calculate-in-Poset_chain-of-inequalities_
infixl 0 step-calculate-in-Poset

calculate-in-Poset_chain-of-inequalities_ :
  {l1 l2 : Level} (X : Poset l1 l2)
  (x : type-Poset X) → leq-Poset X x x
calculate-in-Poset_chain-of-inequalities_ = {!!}

step-calculate-in-Poset :
  {l1 l2 : Level} (X : Poset l1 l2)
  {x y : type-Poset X} → leq-Poset X x y →
  (z : type-Poset X) → leq-Poset X y z → leq-Poset X x z
step-calculate-in-Poset = {!!}

syntax step-calculate-in-Poset X u z v = {!!}
```

## Properties

### Posets are categories whose underlying hom-sets are propositions

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  precategory-Poset : Precategory l1 l2
  precategory-Poset = {!!}

  is-category-precategory-Poset : is-category-Precategory precategory-Poset
  is-category-precategory-Poset x y = {!!}

  category-Poset : Category l1 l2
  pr1 category-Poset = {!!}

module _
  {l1 l2 : Level} (C : Category l1 l2)
  (is-prop-hom-C : (x y : obj-Category C) → is-prop (hom-Category C x y))
  where

  preorder-is-prop-hom-Category : Preorder l1 l2
  preorder-is-prop-hom-Category = {!!}

  poset-is-prop-hom-Category : Poset l1 l2
  pr1 poset-is-prop-hom-Category = {!!}
```

It remains to show that these constructions form inverses to eachother.
