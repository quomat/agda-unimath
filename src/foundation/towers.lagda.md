# Towers of types

```agda
module foundation.towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.iterating-functions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A **tower of types** `A` is a [sequence](foundation.sequences.md) of types
together with maps between every two consecutive types

```text
  fₙ : Aₙ₊₁ → Aₙ
```

giving a sequential diagram of maps that extend infinitely to the left:

```text
     f₃      f₂      f₁      f₀
  ⋯ ---> A₃ ---> A₂ ---> A₁ ---> A₀.
```

## Definitions

### Towers of types

```agda
sequence-map-tower : {l : Level} → (ℕ → UU l) → UU l
sequence-map-tower A = {!!}

tower : (l : Level) → UU (lsuc l)
tower l = {!!}

type-tower : {l : Level} → tower l → ℕ → UU l
type-tower = {!!}

map-tower :
  {l : Level} (A : tower l) (n : ℕ) → type-tower A (succ-ℕ n) → type-tower A n
map-tower = {!!}
```

## Operations

### Right shifting a tower

We can **right shift** a tower of types by forgetting the first terms.

```agda
right-shift-tower : {l : Level} → tower l → tower l
pr1 (right-shift-tower A) n = {!!}
pr2 (right-shift-tower A) n = {!!}

iterated-right-shift-tower : {l : Level} (n : ℕ) → tower l → tower l
iterated-right-shift-tower n = {!!}
```

### Left shifting a tower

We can **left shift** a tower of types by padding it with the
[terminal type](foundation.unit-type.md) `unit`.

```agda
left-shift-tower : {l : Level} → tower l → tower l
pr1 (left-shift-tower {l} A) zero-ℕ = {!!}
pr1 (left-shift-tower A) (succ-ℕ n) = {!!}
pr2 (left-shift-tower A) zero-ℕ = {!!}
pr2 (left-shift-tower A) (succ-ℕ n) = {!!}

iterated-left-shift-tower : {l : Level} (n : ℕ) → tower l → tower l
iterated-left-shift-tower n = {!!}
```

### Postcomposition towers

Given a tower `A` and a type `X` there is a tower `X → A` defined by levelwise
postcomposition

```text
                    (f₂ ∘ -)          (f₁ ∘ -)          (f₀ ∘ -)
  ⋯ -----> (X → A₃) -------> (X → A₂) -------> (X → A₁) -------> (X → A₀).
```

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : tower l2)
  where

  postcomp-tower : tower (l1 ⊔ l2)
  pr1 postcomp-tower n = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
