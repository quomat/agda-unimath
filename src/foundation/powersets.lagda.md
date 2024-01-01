# Powersets

```agda
module foundation.powersets where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.sets

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The **powerset** of a type is the set of all
[subtypes](foundation-core.subtypes.md) with respect to a given universe level.

## Definition

```agda
powerset :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
powerset = {!!}
```

## Properties

### The powerset is a set

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  is-set-powerset : {l2 : Level} → is-set (powerset l2 A)
  is-set-powerset = {!!}

  powerset-Set : (l2 : Level) → Set (l1 ⊔ lsuc l2)
  powerset-Set l2 = {!!}
```

### The powerset large preorder

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Preorder :
    Large-Preorder (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder powerset-Large-Preorder l = {!!}
```

### The powerset large poset

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Poset :
    Large-Poset (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset powerset-Large-Poset = {!!}
```

### The powerset preorder at a universe level

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Preorder : (l2 : Level) → Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Preorder = {!!}
```

### The powerset poset at a universe level

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Poset : (l2 : Level) → Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Poset = {!!}
```
