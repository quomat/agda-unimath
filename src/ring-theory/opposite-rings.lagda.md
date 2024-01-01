# Opposite rings

```agda
module ring-theory.opposite-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

The opposite of a ring R is a ring with the same underlying abelian group, but
with multiplication given by `x·y := {!!}

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  op-Ring : Ring l
  op-Ring = {!!}
```
