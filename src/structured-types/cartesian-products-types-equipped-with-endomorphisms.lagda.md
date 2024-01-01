# Cartesian products of types equipped with endomorphisms

```agda
module structured-types.cartesian-products-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The **cartesian product** of two
[types equipped with an endomorphism](structured-types.types-equipped-with-endomorphisms.md)
`(A , f)` and `(B , g)` is defined as `(A × B , f × g)`

## Definitions

```agda
module _
  {l1 l2 : Level}
  (A : Type-With-Endomorphism l1) (B : Type-With-Endomorphism l2)
  where

  type-prod-Type-With-Endomorphism : UU (l1 ⊔ l2)
  type-prod-Type-With-Endomorphism = {!!}

  endomorphism-prod-Type-With-Endomorphism :
    type-prod-Type-With-Endomorphism → type-prod-Type-With-Endomorphism
  endomorphism-prod-Type-With-Endomorphism = {!!}

  prod-Type-With-Endomorphism :
    Type-With-Endomorphism (l1 ⊔ l2)
  pr1 prod-Type-With-Endomorphism = {!!}
```
