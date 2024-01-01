# Products of radical ideals of a commutative ring

```agda
module commutative-algebra.products-radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.products-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

The **product** of two
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md) `I`
and `J` is the
[radical](commutative-algebra.radicals-of-ideals-commutative-rings.md) of the
[product](commutative-algebra.products-ideals-commutative-rings.md) of `I` and
`J`. In other words, the product of two radical ideals `I` and `J` is the least
radical ideal that contains the products of elements in `I` and in `J`.

## Definitions

### The universal property of the product of two radical ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  contains-product-radical-ideal-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  contains-product-radical-ideal-Commutative-Ring K = {!!}

  is-product-radical-ideal-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    contains-product-radical-ideal-Commutative-Ring K → UUω
  is-product-radical-ideal-Commutative-Ring K H = {!!}
```

### The product of two radical ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  generating-subset-product-radical-ideal-Commutative-Ring :
    subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  generating-subset-product-radical-ideal-Commutative-Ring = {!!}

  product-radical-ideal-Commutative-Ring :
    radical-ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-radical-ideal-Commutative-Ring = {!!}

  ideal-product-radical-ideal-Commutative-Ring :
    ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  ideal-product-radical-ideal-Commutative-Ring = {!!}

  is-in-product-radical-ideal-Commutative-Ring :
    type-Commutative-Ring A → UU (l1 ⊔ l2 ⊔ l3)
  is-in-product-radical-ideal-Commutative-Ring = {!!}

  contains-product-product-radical-ideal-Commutative-Ring :
    contains-product-radical-ideal-Commutative-Ring A I J
      product-radical-ideal-Commutative-Ring
  contains-product-product-radical-ideal-Commutative-Ring x y H K = {!!}

  is-product-product-radical-ideal-Commutative-Ring :
    is-product-radical-ideal-Commutative-Ring A I J
      product-radical-ideal-Commutative-Ring
      contains-product-product-radical-ideal-Commutative-Ring
  is-product-product-radical-ideal-Commutative-Ring K H = {!!}
```

## Properties

### Radical laws for products of ideals

#### `√ (I · √ J) ＝ √ IJ`

For the forward inclusion, assume that `x ∈ I` and `y ∈ √ J`. Then there exists
an `n` such that `yⁿ ∈ J`. It follows that

```text
  (xy)ⁿ⁺¹ ＝ xⁿ⁺¹yⁿ⁺¹ = {!!}
```

and hence `xy ∈ √ IJ`. The backwards inclusion is clear, since `J ⊆ √ J`.

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : ideal-Commutative-Ring l3 A)
  where

  forward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( product-radical-ideal-Commutative-Ring A
        ( I)
        ( radical-of-ideal-Commutative-Ring A J))
      ( radical-of-ideal-Commutative-Ring A
        ( product-ideal-Commutative-Ring A
          ( ideal-radical-ideal-Commutative-Ring A I)
          ( J)))
  forward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ring = {!!}

  backward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( radical-of-ideal-Commutative-Ring A
        ( product-ideal-Commutative-Ring A
          ( ideal-radical-ideal-Commutative-Ring A I)
          ( J)))
      ( product-radical-ideal-Commutative-Ring A
        ( I)
        ( radical-of-ideal-Commutative-Ring A J))
  backward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ring = {!!}

  right-radical-law-product-radical-ideal-Commutative-Ring :
    product-radical-ideal-Commutative-Ring A
      ( I)
      ( radical-of-ideal-Commutative-Ring A J) ＝
    radical-of-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( J))
  right-radical-law-product-radical-ideal-Commutative-Ring = {!!}
```
