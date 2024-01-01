# H-spaces

```agda
module structured-types.h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import foundation-core.endomorphisms

open import structured-types.magmas
open import structured-types.noncoherent-h-spaces
open import structured-types.pointed-sections
open import structured-types.pointed-types
```

</details>

## Idea

A **(coherent) H-space** is a "wild unital magma", i.e., it is a
[pointed type](structured-types.pointed-types.md)
[equipped](foundation.structure.md) with a binary operation for which the base
point is a unit, with a coherence law between the left and the right unit laws.

## Definitions

### Unital binary operations on pointed types

```agda
coherent-unit-laws-mul-Pointed-Type :
  {l : Level} (A : Pointed-Type l)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A) → UU l
coherent-unit-laws-mul-Pointed-Type A μ = {!!}

coherent-unital-mul-Pointed-Type :
  {l : Level} → Pointed-Type l → UU l
coherent-unital-mul-Pointed-Type A = {!!}
```

### H-spaces

```agda
H-Space : (l : Level) → UU (lsuc l)
H-Space l = {!!}

module _
  {l : Level} (M : H-Space l)
  where

  pointed-type-H-Space : Pointed-Type l
  pointed-type-H-Space = {!!}

  type-H-Space : UU l
  type-H-Space = {!!}

  unit-H-Space : type-H-Space
  unit-H-Space = {!!}

  coherent-unital-mul-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-H-Space
  coherent-unital-mul-H-Space = {!!}

  mul-H-Space :
    type-H-Space → type-H-Space → type-H-Space
  mul-H-Space = {!!}

  mul-H-Space' :
    type-H-Space → type-H-Space → type-H-Space
  mul-H-Space' x y = {!!}

  ap-mul-H-Space :
    {a b c d : type-H-Space} → Id a b → Id c d →
    Id (mul-H-Space a c) (mul-H-Space b d)
  ap-mul-H-Space p q = {!!}

  magma-H-Space : Magma l
  pr1 magma-H-Space = {!!}

  coherent-unit-laws-mul-H-Space :
    coherent-unit-laws mul-H-Space unit-H-Space
  coherent-unit-laws-mul-H-Space = {!!}

  left-unit-law-mul-H-Space :
    (x : type-H-Space) →
    Id (mul-H-Space unit-H-Space x) x
  left-unit-law-mul-H-Space = {!!}

  right-unit-law-mul-H-Space :
    (x : type-H-Space) →
    Id (mul-H-Space x unit-H-Space) x
  right-unit-law-mul-H-Space = {!!}

  coh-unit-laws-mul-H-Space :
    Id
      ( left-unit-law-mul-H-Space unit-H-Space)
      ( right-unit-law-mul-H-Space unit-H-Space)
  coh-unit-laws-mul-H-Space = {!!}

  unit-laws-mul-H-Space :
    unit-laws mul-H-Space unit-H-Space
  pr1 unit-laws-mul-H-Space = {!!}

  is-unital-mul-H-Space : is-unital mul-H-Space
  pr1 is-unital-mul-H-Space = {!!}

  is-coherently-unital-mul-H-Space :
    is-coherently-unital mul-H-Space
  pr1 is-coherently-unital-mul-H-Space = {!!}
```

## Properties

### Every non-coherent H-space can be upgraded to a coherent H-space

```agda
h-space-Noncoherent-H-Space :
  {l : Level} → Noncoherent-H-Space l → H-Space l
pr1 (h-space-Noncoherent-H-Space A) = {!!}
pr1 (pr2 (h-space-Noncoherent-H-Space A)) = {!!}
pr2 (pr2 (h-space-Noncoherent-H-Space A)) = {!!}
```

### The type of H-space structures on `A` is equivalent to the type of sections of `ev-point : (A → A) →∗ A`

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  pointed-section-ev-point-Pointed-Type : UU l
  pointed-section-ev-point-Pointed-Type = {!!}

compute-pointed-section-ev-point-Pointed-Type :
  {l : Level} (A : Pointed-Type l) →
  pointed-section-ev-point-Pointed-Type A ≃ coherent-unital-mul-Pointed-Type A
compute-pointed-section-ev-point-Pointed-Type (pair A a) = {!!}
```
