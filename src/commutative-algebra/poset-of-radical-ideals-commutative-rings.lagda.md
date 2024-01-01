# The poset of radical ideals of a commutative ring

```agda
module commutative-algebra.poset-of-radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings

open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-posets
```

</details>

## Idea

The **[large poset](order-theory.large-posets.md) of radical ideals** in a
[commutative ring](commutative-algebra.commutative-rings.md) consists of
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md)
ordered by inclusion.

## Definition

### The ordering of radical ideals in a commutative ring

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  leq-prop-radical-ideal-Commutative-Ring :
    {l2 l3 : Level} →
    radical-ideal-Commutative-Ring l2 A →
    radical-ideal-Commutative-Ring l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-radical-ideal-Commutative-Ring I J = {!!}

  leq-radical-ideal-Commutative-Ring :
    {l2 l3 : Level} →
    radical-ideal-Commutative-Ring l2 A →
    radical-ideal-Commutative-Ring l3 A → UU (l1 ⊔ l2 ⊔ l3)
  leq-radical-ideal-Commutative-Ring I J = {!!}

  is-prop-leq-radical-ideal-Commutative-Ring :
    {l2 l3 : Level}
    (I : radical-ideal-Commutative-Ring l2 A)
    (J : radical-ideal-Commutative-Ring l3 A) →
    is-prop (leq-radical-ideal-Commutative-Ring I J)
  is-prop-leq-radical-ideal-Commutative-Ring I J = {!!}

  refl-leq-radical-ideal-Commutative-Ring :
    {l2 : Level} (I : radical-ideal-Commutative-Ring l2 A) →
    leq-radical-ideal-Commutative-Ring I I
  refl-leq-radical-ideal-Commutative-Ring I = {!!}

  transitive-leq-radical-ideal-Commutative-Ring :
    {l2 l3 l4 : Level}
    (I : radical-ideal-Commutative-Ring l2 A)
    (J : radical-ideal-Commutative-Ring l3 A)
    (K : radical-ideal-Commutative-Ring l4 A) →
    leq-radical-ideal-Commutative-Ring J K →
    leq-radical-ideal-Commutative-Ring I J →
    leq-radical-ideal-Commutative-Ring I K
  transitive-leq-radical-ideal-Commutative-Ring I J K = {!!}

  antisymmetric-leq-radical-ideal-Commutative-Ring :
    {l2 : Level} (I J : radical-ideal-Commutative-Ring l2 A) →
    leq-radical-ideal-Commutative-Ring I J →
    leq-radical-ideal-Commutative-Ring J I → I ＝ J
  antisymmetric-leq-radical-ideal-Commutative-Ring I J H K = {!!}
```

### The large preorder of radical ideals in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  radical-ideal-Commutative-Ring-Large-Preorder :
    Large-Preorder (λ l1 → l ⊔ lsuc l1) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  type-Large-Preorder radical-ideal-Commutative-Ring-Large-Preorder l1 = {!!}
```

### The large poset of radical ideals in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  radical-ideal-Commutative-Ring-Large-Poset :
    Large-Poset (λ l1 → l ⊔ lsuc l1) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  large-preorder-Large-Poset radical-ideal-Commutative-Ring-Large-Poset = {!!}
```

### Similarity of radical ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  sim-prop-radical-ideal-Commutative-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-radical-ideal-Commutative-Ring = {!!}

  sim-radical-ideal-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  sim-radical-ideal-Commutative-Ring = {!!}

  is-prop-sim-radical-ideal-Commutative-Ring :
    is-prop sim-radical-ideal-Commutative-Ring
  is-prop-sim-radical-ideal-Commutative-Ring = {!!}
```

### The inclusion of radical ideals into ideals of a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  preserves-order-ideal-radical-ideal-Commutative-Ring :
    {l1 l2 : Level}
    (I : radical-ideal-Commutative-Ring l1 A)
    (J : radical-ideal-Commutative-Ring l2 A) →
    leq-radical-ideal-Commutative-Ring A I J →
    leq-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A I)
      ( ideal-radical-ideal-Commutative-Ring A J)
  preserves-order-ideal-radical-ideal-Commutative-Ring I J H = {!!}

  ideal-radical-ideal-hom-large-poset-Commutative-Ring :
    hom-Large-Poset
      ( λ l → l)
      ( radical-ideal-Commutative-Ring-Large-Poset A)
      ( ideal-Commutative-Ring-Large-Poset A)
  map-hom-Large-Preorder
    ideal-radical-ideal-hom-large-poset-Commutative-Ring = {!!}
```
