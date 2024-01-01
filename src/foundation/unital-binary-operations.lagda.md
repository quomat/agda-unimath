# Unital binary operations

```agda
module foundation.unital-binary-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A binary operation of type `A → A → A` is **unital** if there is a unit of type
`A` that satisfies both the left and right unit laws. Furthermore, a binary
operation is **coherently unital** if the proofs of the left and right unit laws
agree on the case where both arguments of the operation are the unit.

## Definitions

### Unit laws

```agda
module _
  {l : Level} {A : UU l} (μ : A → A → A) (e : A)
  where

  left-unit-law : UU l
  left-unit-law = {!!}

  right-unit-law : UU l
  right-unit-law = {!!}

  coh-unit-laws : left-unit-law → right-unit-law → UU l
  coh-unit-laws α β = {!!}

  unit-laws : UU l
  unit-laws = {!!}

  coherent-unit-laws : UU l
  coherent-unit-laws = {!!}
```

### Unital binary operations

```agda
is-unital : {l : Level} {A : UU l} (μ : A → A → A) → UU l
is-unital {A = A} μ = {!!}
```

### Coherently unital binary operations

```agda
is-coherently-unital : {l : Level} {A : UU l} (μ : A → A → A) → UU l
is-coherently-unital {A = A} μ = {!!}
```

## Properties

### The unit laws for an operation `μ` with unit `e` can be upgraded to coherent unit laws

```agda
module _
  {l : Level} {A : UU l} (μ : A → A → A) {e : A}
  where

  coherent-unit-laws-unit-laws : unit-laws μ e → coherent-unit-laws μ e
  pr1 (coherent-unit-laws-unit-laws (pair H K)) = {!!}

module _
  {l : Level} {A : UU l} {μ : A → A → A}
  where

  is-coherently-unital-is-unital : is-unital μ → is-coherently-unital μ
  pr1 (is-coherently-unital-is-unital (pair e H)) = {!!}
```
