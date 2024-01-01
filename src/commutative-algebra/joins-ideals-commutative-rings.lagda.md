# Joins of ideals of commutative rings

```agda
module commutative-algebra.joins-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.ideals-generated-by-subsets-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.products-ideals-commutative-rings
open import commutative-algebra.products-subsets-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import ring-theory.joins-ideals-rings
```

</details>

## Idea

The **join** of a family of
[ideals](commutative-algebra.ideals-commutative-rings.md) `i ↦ J i` in a
[commutative ring](commutative-algebra.commutative-rings.md) is the least ideal
containing each `J i`.

## Definition

### The universal property of the join of a family of ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {U : UU l2} (I : U → ideal-Commutative-Ring l3 A)
  where

  is-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) → UUω
  is-join-family-of-ideals-Commutative-Ring = {!!}

  inclusion-is-join-family-of-ideals-Commutative-Ring :
    {l4 l5 : Level} (J : ideal-Commutative-Ring l4 A) →
    is-join-family-of-ideals-Commutative-Ring J →
    (K : ideal-Commutative-Ring l5 A) →
    ((α : U) → leq-ideal-Commutative-Ring A (I α) K) →
    leq-ideal-Commutative-Ring A J K
  inclusion-is-join-family-of-ideals-Commutative-Ring = {!!}

  contains-ideal-is-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (J : ideal-Commutative-Ring l4 A) →
    is-join-family-of-ideals-Commutative-Ring J →
    {α : U} → leq-ideal-Commutative-Ring A (I α) J
  contains-ideal-is-join-family-of-ideals-Commutative-Ring = {!!}
```

### The join of a family of ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {U : UU l2} (I : U → ideal-Commutative-Ring l3 A)
  where

  generating-subset-join-family-of-ideals-Commutative-Ring :
    subset-Commutative-Ring (l2 ⊔ l3) A
  generating-subset-join-family-of-ideals-Commutative-Ring = {!!}

  join-family-of-ideals-Commutative-Ring :
    ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  join-family-of-ideals-Commutative-Ring = {!!}

  forward-inclusion-is-join-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) →
    ((α : U) → leq-ideal-Commutative-Ring A (I α) K) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring K
  forward-inclusion-is-join-join-family-of-ideals-Commutative-Ring = {!!}

  backward-inclusion-is-join-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring K →
    (α : U) → leq-ideal-Commutative-Ring A (I α) K
  backward-inclusion-is-join-join-family-of-ideals-Commutative-Ring = {!!}

  is-join-join-family-of-ideals-Commutative-Ring :
    is-join-family-of-ideals-Commutative-Ring A I
      join-family-of-ideals-Commutative-Ring
  is-join-join-family-of-ideals-Commutative-Ring = {!!}

  inclusion-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (J : ideal-Commutative-Ring l4 A) →
    ((α : U) → leq-ideal-Commutative-Ring A (I α) J) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring J
  inclusion-join-family-of-ideals-Commutative-Ring = {!!}

  contains-ideal-join-family-of-ideals-Commutative-Ring :
    {α : U} →
    leq-ideal-Commutative-Ring A (I α) join-family-of-ideals-Commutative-Ring
  contains-ideal-join-family-of-ideals-Commutative-Ring = {!!}
```

## Properties

### If `I α ⊆ J α` for each `α`, then `⋁ I ⊆ ⋁ J`

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  {U : UU l2}
  (I : U → ideal-Commutative-Ring l3 A)
  (J : U → ideal-Commutative-Ring l4 A)
  (H : (α : U) → leq-ideal-Commutative-Ring A (I α) (J α))
  where

  preserves-order-join-family-of-ideals-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( join-family-of-ideals-Commutative-Ring A I)
      ( join-family-of-ideals-Commutative-Ring A J)
  preserves-order-join-family-of-ideals-Commutative-Ring = {!!}
```

### Products distribute over joins of families of ideals

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → ideal-Commutative-Ring l4 A)
  where

  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-ideals-Commutative-Ring A J))
      ( join-family-of-ideals-Commutative-Ring A
        ( λ α →
          product-ideal-Commutative-Ring A I (J α)))
  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring
    x p = {!!}

  backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( join-family-of-ideals-Commutative-Ring A
        ( λ α →
          product-ideal-Commutative-Ring A I (J α)))
      ( product-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-ideals-Commutative-Ring A J))
  backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring
    = {!!}

  sim-distributive-product-join-family-of-ideals-Commutative-Ring :
    sim-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I
        ( join-family-of-ideals-Commutative-Ring A J))
      ( join-family-of-ideals-Commutative-Ring A
        ( λ α → product-ideal-Commutative-Ring A I (J α)))
  pr1 sim-distributive-product-join-family-of-ideals-Commutative-Ring = {!!}

  distributive-product-join-family-of-ideals-Commutative-Ring :
    product-ideal-Commutative-Ring A I
      ( join-family-of-ideals-Commutative-Ring A J) ＝
    join-family-of-ideals-Commutative-Ring A
      ( λ α → product-ideal-Commutative-Ring A I (J α))
  distributive-product-join-family-of-ideals-Commutative-Ring = {!!}
```
