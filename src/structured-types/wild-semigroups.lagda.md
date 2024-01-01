# Wild semigroups

```agda
module structured-types.wild-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A wild semigroup is a magma of with associative multiplication

## Definition

```agda
Wild-Semigroup : (l : Level) → UU (lsuc l)
Wild-Semigroup l = {!!}

module _
  {l : Level} (G : Wild-Semigroup l)
  where

  magma-Wild-Semigroup : Magma l
  magma-Wild-Semigroup = {!!}

  type-Wild-Semigroup : UU l
  type-Wild-Semigroup = {!!}

  mul-Wild-Semigroup : (x y : type-Wild-Semigroup) → type-Wild-Semigroup
  mul-Wild-Semigroup = {!!}

  mul-Wild-Semigroup' : (x y : type-Wild-Semigroup) → type-Wild-Semigroup
  mul-Wild-Semigroup' = {!!}

  associative-mul-Wild-Semigroup :
    (x y z : type-Wild-Semigroup) →
    Id
      ( mul-Wild-Semigroup (mul-Wild-Semigroup x y) z)
      ( mul-Wild-Semigroup x (mul-Wild-Semigroup y z))
  associative-mul-Wild-Semigroup = {!!}
```
