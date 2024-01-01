# Discrete types

```agda
module foundation-core.discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.sets
```

</details>

## Idea

A discrete type is a type that has decidable equality.

## Definition

```agda
Discrete-Type : (l : Level) → UU (lsuc l)
Discrete-Type l = {!!}

module _
  {l : Level} (X : Discrete-Type l)
  where

  type-Discrete-Type : UU l
  type-Discrete-Type = {!!}

  has-decidable-equality-type-Discrete-Type :
    has-decidable-equality type-Discrete-Type
  has-decidable-equality-type-Discrete-Type = {!!}

  is-set-type-Discrete-Type : is-set type-Discrete-Type
  is-set-type-Discrete-Type = {!!}

  set-Discrete-Type : Set l
  pr1 set-Discrete-Type = {!!}
```
