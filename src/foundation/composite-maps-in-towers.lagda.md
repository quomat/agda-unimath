# Composite maps in towers

```agda
module foundation.composite-maps-in-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-towers
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Given a ([dependent](foundation.dependent-towers.md))
[tower](foundation.towers.md) `A`, we can extract the **composite map from
`Aₙ₊ᵣ` to `Aₙ`**.

## Definitions

### Composite maps in towers

```agda
comp-map-tower :
  {l : Level} (A : tower l) (n r : ℕ) → type-tower A (n +ℕ r) → type-tower A n
comp-map-tower = {!!}
```

### Composite maps in dependent towers

```agda
comp-map-dependent-tower :
  {l1 l2 : Level} {A : tower l1} (B : dependent-tower l2 A)
  (n r : ℕ) (x : type-tower A (n +ℕ r)) →
  family-dependent-tower B (n +ℕ r) x →
  family-dependent-tower B n (comp-map-tower A n r x)
comp-map-dependent-tower = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
