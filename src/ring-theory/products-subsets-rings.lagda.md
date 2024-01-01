# Products of subsets of rings

```agda
module ring-theory.products-subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

The **product** of two [subsets](ring-theory.subsets-rings.md) `S` and `T` of a
[ring](ring-theory.rings.md) `R` consists of elements of the form `st` where
`s ∈ S` and `t ∈ T`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (A : Ring l1)
  (S : subset-Ring l2 A) (T : subset-Ring l3 A)
  where

  product-subset-Ring : subset-Ring (l1 ⊔ l2 ⊔ l3) A
  product-subset-Ring x = {!!}
```

## Properties

### Products distribute over unions of families of subsets

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Ring l1) (S : subset-Ring l2 A)
  {I : UU l3} (T : I → subset-Ring l4 A)
  where

  abstract
    forward-inclusion-distributive-product-union-family-of-subsets-Ring :
      product-subset-Ring A S (union-family-of-subtypes T) ⊆
      union-family-of-subtypes (λ i → product-subset-Ring A S (T i))
    forward-inclusion-distributive-product-union-family-of-subsets-Ring x p = {!!}

  abstract
    backward-inclusion-distributive-product-union-family-of-subsets-Ring :
      union-family-of-subtypes (λ i → product-subset-Ring A S (T i)) ⊆
      product-subset-Ring A S (union-family-of-subtypes T)
    backward-inclusion-distributive-product-union-family-of-subsets-Ring x p = {!!}

  distributive-product-union-family-of-subsets-Ring :
    product-subset-Ring A S (union-family-of-subtypes T) ＝
    union-family-of-subtypes (λ i → product-subset-Ring A S (T i))
  distributive-product-union-family-of-subsets-Ring = {!!}
```

### The product of subsets of commutative rings is associative

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Ring l1)
  (R : subset-Ring l2 A)
  (S : subset-Ring l3 A)
  (T : subset-Ring l4 A)
  where

  abstract
    forward-inclusion-associative-product-subset-Ring :
      ( product-subset-Ring A
        ( product-subset-Ring A R S)
        ( T)) ⊆
      ( product-subset-Ring A
        ( R)
        ( product-subset-Ring A S T))
    forward-inclusion-associative-product-subset-Ring x H = {!!}

  abstract
    backward-inclusion-associative-product-subset-Ring :
      ( product-subset-Ring A
        ( R)
        ( product-subset-Ring A S T)) ⊆
      ( product-subset-Ring A
        ( product-subset-Ring A R S)
        ( T))
    backward-inclusion-associative-product-subset-Ring x H = {!!}

  associative-product-subset-Ring :
    product-subset-Ring A
      ( product-subset-Ring A R S)
      ( T) ＝
    product-subset-Ring A
      ( R)
      ( product-subset-Ring A S T)
  associative-product-subset-Ring = {!!}
```
