# The poset of ideals of a ring

```agda
module ring-theory.poset-of-ideals-rings where
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

open import ring-theory.ideals-rings
open import ring-theory.rings
```

</details>

## Idea

The [ideals](ring-theory.ideals-rings.md) of a [ring](ring-theory.rings.md) form
a [large poset](order-theory.large-posets.md) ordered by inclusion.

## Definition

### The inclusion relation on ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  leq-prop-ideal-Ring :
    {l2 l3 : Level} → ideal-Ring l2 R → ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-ideal-Ring = {!!}

  leq-ideal-Ring :
    {l2 l3 : Level} → ideal-Ring l2 R → ideal-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-ideal-Ring = {!!}

  is-prop-leq-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    is-prop (leq-ideal-Ring I J)
  is-prop-leq-ideal-Ring = {!!}

  refl-leq-ideal-Ring :
    {l2 : Level} → is-reflexive (leq-ideal-Ring {l2})
  refl-leq-ideal-Ring = {!!}

  transitive-leq-ideal-Ring :
    {l2 l3 l4 : Level}
    (I : ideal-Ring l2 R)
    (J : ideal-Ring l3 R)
    (K : ideal-Ring l4 R) →
    leq-ideal-Ring J K →
    leq-ideal-Ring I J →
    leq-ideal-Ring I K
  transitive-leq-ideal-Ring = {!!}

  antisymmetric-leq-ideal-Ring :
    {l2 : Level} → is-antisymmetric (leq-ideal-Ring {l2})
  antisymmetric-leq-ideal-Ring = {!!}
```

### The large poset of ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  ideal-Ring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  ideal-Ring-Large-Preorder = {!!}

  ideal-Ring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  ideal-Ring-Large-Poset = {!!}
```

### The similarity relation on ideals in a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  sim-prop-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-ideal-Ring = {!!}

  sim-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-ideal-Ring = {!!}

  is-prop-sim-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    is-prop (sim-ideal-Ring I J)
  is-prop-sim-ideal-Ring = {!!}

  eq-sim-ideal-Ring :
    {l2 : Level} (I J : ideal-Ring l2 R) → sim-ideal-Ring I J → I ＝ J
  eq-sim-ideal-Ring = {!!}
```

## Properties

### The forgetful function from ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-order-subset-ideal-Ring :
    {l1 l2 : Level} (I : ideal-Ring l1 R) (J : ideal-Ring l2 R) →
    leq-ideal-Ring R I J → subset-ideal-Ring R I ⊆ subset-ideal-Ring R J
  preserves-order-subset-ideal-Ring = {!!}

  subset-ideal-hom-large-poset-Ring :
    hom-Large-Poset
      ( λ l → l)
      ( ideal-Ring-Large-Poset R)
      ( powerset-Large-Poset (type-Ring R))
  subset-ideal-hom-large-poset-Ring = {!!}
```
