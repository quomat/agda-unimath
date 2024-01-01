# Boolean rings

```agda
module commutative-algebra.boolean-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.idempotent-elements-rings
```

</details>

## Idea

A **boolean ring** is a commutative ring in wich every element is idempotent.

## Definition

```agda
is-boolean-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → UU l
is-boolean-Commutative-Ring = {!!}

Boolean-Ring : (l : Level) → UU (lsuc l)
Boolean-Ring l = {!!}

module _
  {l : Level} (A : Boolean-Ring l)
  where

  commutative-ring-Boolean-Ring : Commutative-Ring l
  commutative-ring-Boolean-Ring = {!!}
```
