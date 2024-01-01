# The multiplicative monoid of natural numbers

```agda
module elementary-number-theory.multiplicative-monoid-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The **multiplicative monoid of natural numbers** consists of
[natural numbers](elementary-number-theory.natural-numbers.md), and is equipped
with the
[multiplication operation](elementary-number-theory.multiplication-natural-numbers.md)
of the natural numbers as its multiplicative structure.

## Definitions

### The multiplicative semigroup of natural numbers

```agda
ℕ*-Semigroup : Semigroup lzero
ℕ*-Semigroup = {!!}
pr1 (pr2 ℕ*-Semigroup) = {!!}
pr2 (pr2 ℕ*-Semigroup) = {!!}
```

### The multiplicative monoid of natural numbers

```agda
ℕ*-Monoid : Monoid lzero
ℕ*-Monoid = {!!}
pr1 (pr2 ℕ*-Monoid) = {!!}
pr1 (pr2 (pr2 ℕ*-Monoid)) = {!!}
pr2 (pr2 (pr2 ℕ*-Monoid)) = {!!}
```
