# The poset of right ideals of a ring

```agda
module ring-theory.poset-of-right-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-posets

open import ring-theory.right-ideals-rings
open import ring-theory.rings
```

</details>

## Idea

The [right ideals](ring-theory.right-ideals-rings.md) of a
[ring](ring-theory.rings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  leq-prop-right-ideal-Ring :
    {l2 l3 : Level} →
    right-ideal-Ring l2 R → right-ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-right-ideal-Ring = {!!}

  leq-right-ideal-Ring :
    {l2 l3 : Level} →
    right-ideal-Ring l2 R → right-ideal-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-right-ideal-Ring = {!!}

  is-prop-leq-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    is-prop (leq-right-ideal-Ring I J)
  is-prop-leq-right-ideal-Ring = {!!}

  refl-leq-right-ideal-Ring :
    {l2 : Level} → is-reflexive (leq-right-ideal-Ring {l2})
  refl-leq-right-ideal-Ring = {!!}

  transitive-leq-right-ideal-Ring :
    {l2 l3 l4 : Level}
    (I : right-ideal-Ring l2 R)
    (J : right-ideal-Ring l3 R)
    (K : right-ideal-Ring l4 R) →
    leq-right-ideal-Ring J K →
    leq-right-ideal-Ring I J →
    leq-right-ideal-Ring I K
  transitive-leq-right-ideal-Ring = {!!}

  antisymmetric-leq-right-ideal-Ring :
    {l2 : Level} → is-antisymmetric (leq-right-ideal-Ring {l2})
  antisymmetric-leq-right-ideal-Ring = {!!}
```

### The large poset of right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  right-ideal-Ring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  right-ideal-Ring-Large-Preorder = {!!}

  right-ideal-Ring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  right-ideal-Ring-Large-Poset = {!!}
```

### The similarity relation on right ideals in a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  sim-prop-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-right-ideal-Ring = {!!}

  sim-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-right-ideal-Ring = {!!}

  is-prop-sim-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    is-prop (sim-right-ideal-Ring I J)
  is-prop-sim-right-ideal-Ring = {!!}

  eq-sim-right-ideal-Ring :
    {l2 : Level} (I J : right-ideal-Ring l2 R) →
    sim-right-ideal-Ring I J → I ＝ J
  eq-sim-right-ideal-Ring = {!!}
```

## Properties

### The forgetful function from right ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-order-subset-right-ideal-Ring :
    {l1 l2 : Level} (I : right-ideal-Ring l1 R) (J : right-ideal-Ring l2 R) →
    leq-right-ideal-Ring R I J →
    subset-right-ideal-Ring R I ⊆ subset-right-ideal-Ring R J
  preserves-order-subset-right-ideal-Ring = {!!}

  subset-right-ideal-hom-large-poset-Ring :
    hom-Large-Poset
      ( λ l → l)
      ( right-ideal-Ring-Large-Poset R)
      ( powerset-Large-Poset (type-Ring R))
  subset-right-ideal-hom-large-poset-Ring = {!!}
```
