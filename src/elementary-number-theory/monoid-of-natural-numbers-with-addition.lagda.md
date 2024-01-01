# The monoid of natural numbers with addition

```agda
module elementary-number-theory.monoid-of-natural-numbers-with-addition where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The natural numbers equipped with `0` and addition is a commutative monoid.

## Definitions

### The Semigroup of natural numbers

```agda
ℕ-Semigroup : Semigroup lzero
ℕ-Semigroup = {!!}
pr1 (pr2 ℕ-Semigroup) = {!!}
pr2 (pr2 ℕ-Semigroup) = {!!}
```

### The monoid of natural numbers

```agda
ℕ-Monoid : Monoid lzero
ℕ-Monoid = {!!}
pr1 (pr2 ℕ-Monoid) = {!!}
pr1 (pr2 (pr2 ℕ-Monoid)) = {!!}
pr2 (pr2 (pr2 ℕ-Monoid)) = {!!}
```

### The commutative monoid of natural numbers

```agda
ℕ-Commutative-Monoid : Commutative-Monoid lzero
ℕ-Commutative-Monoid = {!!}
pr2 ℕ-Commutative-Monoid = {!!}
```
