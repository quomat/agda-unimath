# The substitution functor of group actions

```agda
module group-theory.substitution-functor-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.precategory-of-group-actions
open import group-theory.symmetric-groups
```

</details>

## Idea

Given a [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H`
and an [`H`-set](group-theory.group-actions.md) `Y`, we obtain a `G`-action on
`Y` by `g,x ↦ f(g)x`. This operation is functorial in `Y`.

## Definition

```agda
module _
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : hom-Group G H)
  where

  obj-subst-action-Group :
    {l3 : Level} → action-Group H l3 → action-Group G l3
  obj-subst-action-Group = {!!}

  hom-subst-action-Group :
    {l3 l4 : Level}
    (X : action-Group H l3) (Y : action-Group H l4) →
    hom-action-Group H X Y →
    hom-action-Group G
      ( obj-subst-action-Group X)
      ( obj-subst-action-Group Y)
  hom-subst-action-Group = {!!}

  preserves-id-subst-action-Group :
    {l3 : Level} (X : action-Group H l3) →
    Id
      ( hom-subst-action-Group X X (id-hom-action-Group H X))
      ( id-hom-action-Group G (obj-subst-action-Group X))
  preserves-id-subst-action-Group = {!!}

  preserves-comp-subst-action-Group :
    {l3 l4 l5 : Level} (X : action-Group H l3)
    (Y : action-Group H l4) (Z : action-Group H l5)
    (g : hom-action-Group H Y Z)
    (f : hom-action-Group H X Y) →
    Id
      ( hom-subst-action-Group X Z
        ( comp-hom-action-Group H X Y Z g f))
      ( comp-hom-action-Group G
        ( obj-subst-action-Group X)
        ( obj-subst-action-Group Y)
        ( obj-subst-action-Group Z)
        ( hom-subst-action-Group Y Z g)
        ( hom-subst-action-Group X Y f))
  preserves-comp-subst-action-Group = {!!}

  subst-action-Group :
    functor-Large-Precategory (λ l → l)
      ( action-Group-Large-Precategory H)
      ( action-Group-Large-Precategory G)
  subst-action-Group = {!!}
```

## Properties

### The substitution functor has a left adjoint

```agda
module _
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : hom-Group G H)
  where

  preset-obj-left-adjoint-subst-action-Group :
    {l3 : Level} → action-Group G l3 → Set (l2 ⊔ l3)
  preset-obj-left-adjoint-subst-action-Group = {!!}

  pretype-obj-left-adjoint-subst-action-Group :
    {l3 : Level} → action-Group G l3 → UU (l2 ⊔ l3)
  pretype-obj-left-adjoint-subst-action-Group = {!!}

  is-set-pretype-obj-left-adjoint-subst-action-Group :
    {l3 : Level} (X : action-Group G l3) →
    is-set (pretype-obj-left-adjoint-subst-action-Group X)
  is-set-pretype-obj-left-adjoint-subst-action-Group = {!!}

  equivalence-relation-obj-left-adjoint-subst-action-Group :
    {l3 : Level} (X : action-Group G l3) →
    equivalence-relation
      ( l1 ⊔ l2 ⊔ l3)
      ( pretype-obj-left-adjoint-subst-action-Group X)
  equivalence-relation-obj-left-adjoint-subst-action-Group = {!!}

  set-left-adjoint-subst-action-Group :
    {l3 : Level} → action-Group G l3 →
    Set (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  set-left-adjoint-subst-action-Group = {!!}
```
