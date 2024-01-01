# Cartesian products of concrete groups

```agda
module group-theory.cartesian-products-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups

open import higher-group-theory.cartesian-products-higher-groups
open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The cartesian product of two concrete groups is defined as the cartesian product
of their underlying `∞-group`

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (R : Concrete-Group l2)
  where

  product-Concrete-Group : Concrete-Group (l1 ⊔ l2)
  pr1 product-Concrete-Group = {!!}
  pr2 product-Concrete-Group = {!!}

  ∞-group-product-Concrete-Group : ∞-Group (l1 ⊔ l2)
  ∞-group-product-Concrete-Group = {!!}

  classifying-pointed-type-product-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  classifying-pointed-type-product-Concrete-Group = {!!}

  classifying-type-product-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-product-Concrete-Group = {!!}

  shape-product-Concrete-Group : classifying-type-product-Concrete-Group
  shape-product-Concrete-Group = {!!}

  is-0-connected-classifying-type-product-Concrete-Group :
    is-0-connected classifying-type-product-Concrete-Group
  is-0-connected-classifying-type-product-Concrete-Group = {!!}

  mere-eq-classifying-type-product-Concrete-Group :
    (X Y : classifying-type-product-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-product-Concrete-Group = {!!}

  elim-prop-classifying-type-product-Concrete-Group :
    {l2 : Level} (P : classifying-type-product-Concrete-Group → Prop l2) →
    type-Prop (P shape-product-Concrete-Group) →
    ((X : classifying-type-product-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-product-Concrete-Group = {!!}

  type-product-Concrete-Group : UU (l1 ⊔ l2)
  type-product-Concrete-Group = {!!}

  is-set-type-product-Concrete-Group : is-set type-product-Concrete-Group
  is-set-type-product-Concrete-Group = {!!}

  set-product-Concrete-Group : Set (l1 ⊔ l2)
  set-product-Concrete-Group = {!!}

  abstract
    is-1-type-classifying-type-product-Concrete-Group :
      is-trunc one-𝕋 classifying-type-product-Concrete-Group
    is-1-type-classifying-type-product-Concrete-Group X Y = {!!}

  classifying-1-type-product-Concrete-Group : Truncated-Type (l1 ⊔ l2) one-𝕋
  classifying-1-type-product-Concrete-Group = {!!}

  Id-product-BG-Set :
    (X Y : classifying-type-product-Concrete-Group) → Set (l1 ⊔ l2)
  Id-product-BG-Set X Y = {!!}

  unit-product-Concrete-Group : type-product-Concrete-Group
  unit-product-Concrete-Group = {!!}

  mul-product-Concrete-Group :
    (x y : type-product-Concrete-Group) → type-product-Concrete-Group
  mul-product-Concrete-Group = {!!}

  mul-product-Concrete-Group' :
    (x y : type-product-Concrete-Group) → type-product-Concrete-Group
  mul-product-Concrete-Group' x y = {!!}

  associative-mul-product-Concrete-Group :
    (x y z : type-product-Concrete-Group) →
    Id
      (mul-product-Concrete-Group (mul-product-Concrete-Group x y) z)
      (mul-product-Concrete-Group x (mul-product-Concrete-Group y z))
  associative-mul-product-Concrete-Group = {!!}

  left-unit-law-mul-product-Concrete-Group :
    (x : type-product-Concrete-Group) →
    Id (mul-product-Concrete-Group unit-product-Concrete-Group x) x
  left-unit-law-mul-product-Concrete-Group = {!!}

  right-unit-law-mul-product-Concrete-Group :
    (y : type-product-Concrete-Group) →
    Id (mul-product-Concrete-Group y unit-product-Concrete-Group) y
  right-unit-law-mul-product-Concrete-Group = {!!}

  coherence-unit-laws-mul-product-Concrete-Group :
    Id
      ( left-unit-law-mul-product-Concrete-Group unit-product-Concrete-Group)
      ( right-unit-law-mul-product-Concrete-Group unit-product-Concrete-Group)
  coherence-unit-laws-mul-product-Concrete-Group = {!!}

  inv-product-Concrete-Group :
    type-product-Concrete-Group → type-product-Concrete-Group
  inv-product-Concrete-Group = {!!}

  left-inverse-law-mul-product-Concrete-Group :
    (x : type-product-Concrete-Group) →
    Id
      ( mul-product-Concrete-Group (inv-product-Concrete-Group x) x)
      ( unit-product-Concrete-Group)
  left-inverse-law-mul-product-Concrete-Group = {!!}

  right-inverse-law-mul-product-Concrete-Group :
    (x : type-product-Concrete-Group) →
    Id
      ( mul-product-Concrete-Group x (inv-product-Concrete-Group x))
      ( unit-product-Concrete-Group)
  right-inverse-law-mul-product-Concrete-Group = {!!}

  group-product-Concrete-Group : Group (l1 ⊔ l2)
  pr1 (pr1 group-product-Concrete-Group) = {!!}
  pr1 (pr2 (pr1 group-product-Concrete-Group)) = {!!}
  pr2 (pr2 (pr1 group-product-Concrete-Group)) = {!!}
  pr1 (pr1 (pr2 group-product-Concrete-Group)) = {!!}
  pr1 (pr2 (pr1 (pr2 group-product-Concrete-Group))) = {!!}
  pr2 (pr2 (pr1 (pr2 group-product-Concrete-Group))) = {!!}
  pr1 (pr2 (pr2 group-product-Concrete-Group)) = {!!}
  pr1 (pr2 (pr2 (pr2 group-product-Concrete-Group))) = {!!}
  pr2 (pr2 (pr2 (pr2 group-product-Concrete-Group))) = {!!}

  op-group-product-Concrete-Group : Group (l1 ⊔ l2)
  pr1 (pr1 op-group-product-Concrete-Group) = {!!}
  pr1 (pr2 (pr1 op-group-product-Concrete-Group)) = {!!}
  pr2 (pr2 (pr1 op-group-product-Concrete-Group)) x y z = {!!}
  pr1 (pr1 (pr2 op-group-product-Concrete-Group)) = {!!}
  pr1 (pr2 (pr1 (pr2 op-group-product-Concrete-Group))) = {!!}
  pr2 (pr2 (pr1 (pr2 op-group-product-Concrete-Group))) = {!!}
  pr1 (pr2 (pr2 op-group-product-Concrete-Group)) = {!!}
  pr1 (pr2 (pr2 (pr2 op-group-product-Concrete-Group))) = {!!}
  pr2 (pr2 (pr2 (pr2 op-group-product-Concrete-Group))) = {!!}
```

## Property

```agda
  equiv-type-Concrete-Group-product-Concrete-Group :
    type-product-Concrete-Group ≃
    ( type-Concrete-Group G × type-Concrete-Group R)
  equiv-type-Concrete-Group-product-Concrete-Group = {!!}
```
