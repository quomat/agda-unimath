# Idempotent elements in rings

```agda
module ring-theory.idempotent-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

An idempotent element in a ring is an element `x` such that `x² = {!!}

## Definition

```agda
module _
  {l : Level} (R : Ring l) (x : type-Ring R)
  where

  is-idempotent-element-ring-Prop : Prop l
  is-idempotent-element-ring-Prop = {!!}

  is-idempotent-element-Ring : UU l
  is-idempotent-element-Ring = {!!}

  is-prop-is-idempotent-element-Ring : is-prop is-idempotent-element-Ring
  is-prop-is-idempotent-element-Ring = {!!}

idempotent-element-Ring :
  {l : Level} (R : Ring l) → UU l
idempotent-element-Ring = {!!}

module _
  {l : Level} (R : Ring l) (x : idempotent-element-Ring R)
  where

  element-idempotent-element-Ring : type-Ring R
  element-idempotent-element-Ring = {!!}

  is-idempotent-element-idempotent-element-Ring :
    is-idempotent-element-Ring R element-idempotent-element-Ring
  is-idempotent-element-idempotent-element-Ring = {!!}
```
