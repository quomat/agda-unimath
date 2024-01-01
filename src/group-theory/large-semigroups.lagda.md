# Large semigroups

```agda
module group-theory.large-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A **large semigroup** with universe indexing function `α : Level → Level`
consists of:

- For each universe level `l` a set `X l : UU (α l)`
- For any two universe levels `l1` and `l2` a binary operation
  `μ l1 l2 : X l1 → X l2 → X (l1 ⊔ l2)` satisfying the following associativity
  law:

```text
  μ (l1 ⊔ l2) l3 (μ l1 l2 x y) z ＝ μ l1 (l2 ⊔ l3) x (μ l2 l3 y z).
```

## Definitions

```agda
record Large-Semigroup (α : Level → Level) : UUω where
  constructor
    make-Large-Semigroup
  field
    set-Large-Semigroup :
      (l : Level) → Set (α l)
    set-Large-Semigroup = {!!}

  is-set-type-Large-Semigroup :
    {l : Level} → is-set (type-Large-Semigroup l)
  is-set-type-Large-Semigroup = {!!}
```

### Small semigroups from large semigroups

```agda
module _
  {α : Level → Level} (G : Large-Semigroup α)
  where

  semigroup-Large-Semigroup : (l : Level) → Semigroup (α l)
  semigroup-Large-Semigroup = {!!}
```
