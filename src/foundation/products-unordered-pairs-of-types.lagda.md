# Products of unordered pairs of types

```agda
module foundation.products-unordered-pairs-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.symmetric-operations
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs
open import foundation.unordered-pairs-of-types

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.universal-property-standard-finite-types
```

</details>

## Idea

Given an unordered pair of types, we can take their product. This is a symmetric
version of the cartesian product operation on types.

## Definition

```agda
product-unordered-pair-types :
  {l : Level} → symmetric-operation (UU l) (UU l)
product-unordered-pair-types = {!!}

pr-product-unordered-pair-types :
  {l : Level} (p : unordered-pair-types l) (i : type-unordered-pair p) →
  product-unordered-pair-types p → element-unordered-pair p i
pr-product-unordered-pair-types = {!!}

equiv-pr-product-unordered-pair-types :
  {l : Level} (A : unordered-pair-types l) (i : type-unordered-pair A) →
  product-unordered-pair-types A ≃
  (element-unordered-pair A i × other-element-unordered-pair A i)
equiv-pr-product-unordered-pair-types = {!!}

equiv-pair-product-unordered-pair-types :
  {l : Level} (A : unordered-pair-types l) (i : type-unordered-pair A) →
  (element-unordered-pair A i × other-element-unordered-pair A i) ≃
  product-unordered-pair-types A
equiv-pair-product-unordered-pair-types = {!!}

pair-product-unordered-pair-types :
  {l : Level} (A : unordered-pair-types l) (i : type-unordered-pair A) →
  element-unordered-pair A i → other-element-unordered-pair A i →
  product-unordered-pair-types A
pair-product-unordered-pair-types = {!!}
```

### Equivalences of products of unordered pairs of types

```agda
module _
  {l1 l2 : Level} (A : unordered-pair-types l1) (B : unordered-pair-types l2)
  where

  equiv-product-unordered-pair-types :
    equiv-unordered-pair-types A B →
    product-unordered-pair-types A ≃ product-unordered-pair-types B
  equiv-product-unordered-pair-types = {!!}
```
