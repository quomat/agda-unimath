# Dependent products of H-spaces

```agda
module structured-types.dependent-products-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.dependent-products-pointed-types
open import structured-types.h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

Given a family of [H-spaces](structured-types.h-spaces.md) `Mᵢ` indexed by
`i : I`, the dependent product `Π(i : I), Mᵢ` is a H-space consisting of
dependent functions taking `i : I` to an element of the underlying type of `Mᵢ`.
The multiplicative operation and the unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → H-Space l2)
  where

  pointed-type-Π-H-Space : Pointed-Type (l1 ⊔ l2)
  pointed-type-Π-H-Space = {!!}

  type-Π-H-Space : UU (l1 ⊔ l2)
  type-Π-H-Space = {!!}

  unit-Π-H-Space : type-Π-H-Space
  unit-Π-H-Space = {!!}

  mul-Π-H-Space :
    type-Π-H-Space → type-Π-H-Space → type-Π-H-Space
  mul-Π-H-Space f g i = {!!}

  left-unit-law-mul-Π-H-Space :
    (f : type-Π-H-Space) →
    mul-Π-H-Space unit-Π-H-Space f ＝ f
  left-unit-law-mul-Π-H-Space f = {!!}

  right-unit-law-mul-Π-H-Space :
    (f : type-Π-H-Space) →
    mul-Π-H-Space f unit-Π-H-Space ＝ f
  right-unit-law-mul-Π-H-Space f = {!!}

  is-unital-mul-Π-H-Space : is-unital mul-Π-H-Space
  pr1 is-unital-mul-Π-H-Space = {!!}

  coh-unit-laws-mul-Π-H-Space :
    coh-unit-laws
      ( mul-Π-H-Space)
      ( unit-Π-H-Space)
      ( left-unit-law-mul-Π-H-Space)
      ( right-unit-law-mul-Π-H-Space)
  coh-unit-laws-mul-Π-H-Space = {!!}

  coherent-unit-laws-mul-Π-H-Space :
    coherent-unit-laws mul-Π-H-Space unit-Π-H-Space
  pr1 coherent-unit-laws-mul-Π-H-Space = {!!}
  pr1 (pr2 coherent-unit-laws-mul-Π-H-Space) = {!!}
  pr2 (pr2 coherent-unit-laws-mul-Π-H-Space) = {!!}

  is-coherently-unital-mul-Π-H-Space :
    is-coherently-unital mul-Π-H-Space
  pr1 is-coherently-unital-mul-Π-H-Space = {!!}

  coherent-unital-mul-Π-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-Π-H-Space
  pr1 coherent-unital-mul-Π-H-Space = {!!}

  Π-H-Space : H-Space (l1 ⊔ l2)
  pr1 Π-H-Space = {!!}
```
