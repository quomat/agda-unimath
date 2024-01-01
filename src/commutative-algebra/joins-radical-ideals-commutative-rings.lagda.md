# Joins of radical ideals of commutative rings

```agda
module commutative-algebra.joins-radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.intersections-radical-ideals-commutative-rings
open import commutative-algebra.joins-ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.products-ideals-commutative-rings
open import commutative-algebra.products-radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-generated-by-subsets-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

The **join** of a family of
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md)
`α ↦ J α` in a [commutative ring](commutative-algebra.commutative-rings.md) is
the least radical ideal containing each `J α`.

## Definitions

### The universal property of the join of a family of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {U : UU l2} (I : U → radical-ideal-Commutative-Ring l3 A)
  where

  is-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) → UUω
  is-join-family-of-radical-ideals-Commutative-Ring = {!!}

  inclusion-is-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (J : radical-ideal-Commutative-Ring l4 A) →
    is-join-family-of-radical-ideals-Commutative-Ring J →
    {l5 : Level} (K : radical-ideal-Commutative-Ring l5 A) →
    ((α : U) → leq-radical-ideal-Commutative-Ring A (I α) K) →
    leq-radical-ideal-Commutative-Ring A J K
  inclusion-is-join-family-of-radical-ideals-Commutative-Ring = {!!}

  contains-ideal-is-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (J : radical-ideal-Commutative-Ring l4 A) →
    is-join-family-of-radical-ideals-Commutative-Ring J →
    {α : U} → leq-radical-ideal-Commutative-Ring A (I α) J
  contains-ideal-is-join-family-of-radical-ideals-Commutative-Ring J H {α} = {!!}
```

### The join of a family of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {I : UU l2} (J : I → radical-ideal-Commutative-Ring l3 A)
  where

  generating-subset-join-family-of-radical-ideals-Commutative-Ring :
    subset-Commutative-Ring (l2 ⊔ l3) A
  generating-subset-join-family-of-radical-ideals-Commutative-Ring = {!!}

  join-family-of-radical-ideals-Commutative-Ring :
    radical-ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  join-family-of-radical-ideals-Commutative-Ring = {!!}

  forward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    ((i : I) → leq-radical-ideal-Commutative-Ring A (J i) K) →
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring)
      ( K)
  forward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ring
    K H = {!!}

  backward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring)
      ( K) →
    (i : I) → leq-radical-ideal-Commutative-Ring A (J i) K
  backward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ring
    K H i x p = {!!}

  is-join-join-family-of-radical-ideals-Commutative-Ring :
    is-join-family-of-radical-ideals-Commutative-Ring A J
      join-family-of-radical-ideals-Commutative-Ring
  pr1 (is-join-join-family-of-radical-ideals-Commutative-Ring K) = {!!}
```

### The large suplattice of radical ideals in a commutative ring

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  is-large-suplattice-radical-ideal-Commutative-Ring :
    is-large-suplattice-Large-Poset l1
      ( radical-ideal-Commutative-Ring-Large-Poset A)
  sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-radical-ideal-Commutative-Ring I) = {!!}

  radical-ideal-Commutative-Ring-Large-Suplattice :
    Large-Suplattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3) l1
  large-poset-Large-Suplattice
    radical-ideal-Commutative-Ring-Large-Suplattice = {!!}
```

## Properties

### Join is an order preserving operation

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  {U : UU l2}
  (I : U → radical-ideal-Commutative-Ring l3 A)
  (J : U → radical-ideal-Commutative-Ring l4 A)
  (H : (α : U) → leq-radical-ideal-Commutative-Ring A (I α) (J α))
  where

  preserves-order-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring A I)
      ( join-family-of-radical-ideals-Commutative-Ring A J)
  preserves-order-join-family-of-radical-ideals-Commutative-Ring = {!!}
```

### `√ (⋁_α √ I_α) ＝ √ (⋁_α I_α)` for any family `I` of ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {U : UU l2} (I : U → ideal-Commutative-Ring l3 A)
  where

  forward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → radical-of-ideal-Commutative-Ring A (I α)))
      ( radical-of-ideal-Commutative-Ring A
        ( join-family-of-ideals-Commutative-Ring A I))
  forward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ring = {!!}

  backward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( radical-of-ideal-Commutative-Ring A
        ( join-family-of-ideals-Commutative-Ring A I))
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → radical-of-ideal-Commutative-Ring A (I α)))
  backward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ring = {!!}

  radical-law-join-family-of-radical-ideals-Commutative-Ring :
    join-family-of-radical-ideals-Commutative-Ring A
      ( λ α → radical-of-ideal-Commutative-Ring A (I α)) ＝
    radical-of-ideal-Commutative-Ring A
      ( join-family-of-ideals-Commutative-Ring A I)
  radical-law-join-family-of-radical-ideals-Commutative-Ring = {!!}
```

### Products of radical ideals distribute over joins

Consider a radical ideal `I` and a family of radical ideals `J_α` indexed by
`α : U`. To prove distributivity, we make the following calculation where we
will write `·r` for the product of radical ideals and `⋁r` for the join of a
family of radical ideals.

```text
  I ·r (⋁r_α J_α) ＝ √ (I · √ (⋁_α J_α))
                  ＝ √ (I · (⋁_α J_α))
                  ＝ √ (⋁_α (I · J_α))
                  ＝ √ (⋁_α √ (I · J_α))
                  ＝ ⋁r_α (I ·r J_α)
```

The proof below proceeds by proving inclusions in both directions along the
computation steps above.

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → radical-ideal-Commutative-Ring l4 A)
  where

  forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( product-radical-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-radical-ideals-Commutative-Ring A J))
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → product-radical-ideal-Commutative-Ring A I (J α)))
  forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ring = {!!}

  backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → product-radical-ideal-Commutative-Ring A I (J α)))
      ( product-radical-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-radical-ideals-Commutative-Ring A J))
  backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ring = {!!}

  sim-distributive-product-join-family-of-radical-ideals-Commutative-Ring :
    sim-radical-ideal-Commutative-Ring A
      ( product-radical-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-radical-ideals-Commutative-Ring A J))
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → product-radical-ideal-Commutative-Ring A I (J α)))
  pr1 sim-distributive-product-join-family-of-radical-ideals-Commutative-Ring = {!!}

  distributive-product-join-family-of-radical-ideals-Commutative-Ring :
    product-radical-ideal-Commutative-Ring A
      ( I)
      ( join-family-of-radical-ideals-Commutative-Ring A J) ＝
    join-family-of-radical-ideals-Commutative-Ring A
      ( λ α → product-radical-ideal-Commutative-Ring A I (J α))
  distributive-product-join-family-of-radical-ideals-Commutative-Ring = {!!}
```

### Intersections of radical ideals distribute over joins

Since the
[intersection](commutative-algebra.intersections-radical-ideals-commutative-rings.md)
`I ∩ J` of two radical ideals is the
[product](commutative-algebra.products-radical-ideals-commutative-rings.md) `IJ`
of radical ideals, it follows that intersections distribute over joins of
radical ideals.

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → radical-ideal-Commutative-Ring l4 A)
  where

  forward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( intersection-radical-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-radical-ideals-Commutative-Ring A J))
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → intersection-radical-ideal-Commutative-Ring A I (J α)))
  forward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ring = {!!}

  backward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → intersection-radical-ideal-Commutative-Ring A I (J α)))
      ( intersection-radical-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-radical-ideals-Commutative-Ring A J))
  backward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ring = {!!}

  distributive-intersection-join-family-of-radical-ideals-Commutative-Ring :
    intersection-radical-ideal-Commutative-Ring A
      ( I)
      ( join-family-of-radical-ideals-Commutative-Ring A J) ＝
    join-family-of-radical-ideals-Commutative-Ring A
      ( λ α → intersection-radical-ideal-Commutative-Ring A I (J α))
  distributive-intersection-join-family-of-radical-ideals-Commutative-Ring = {!!}
```
