# Cubes of natural numbers

```agda
module elementary-number-theory.cubes-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "cube" Disambiguation="natural number"}} `n³` of a
[natural number](elementary-number-theory.natural-numbers.md) `n` is the triple
[product](elementary-number-theory.multiplication-natural-numbers.md)

```text
  n³ := {!!}
```

of `n` with itself.

## Definitions

### Cubes of natural numbers

```agda
cube-ℕ : ℕ → ℕ
cube-ℕ n = {!!}
```

### The predicate of being a cube of natural numbers

```agda
is-cube-ℕ : ℕ → UU lzero
is-cube-ℕ = {!!}
```

### The cubic root of cubic natural numbers

```agda
cubic-root-ℕ : (n : ℕ) → is-cube-ℕ n → ℕ
cubic-root-ℕ n = {!!}
```

## See also

- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
