# The monoid of the natural numbers with maximum

```agda
module elementary-number-theory.monoid-of-natural-numbers-with-maximum where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.initial-segments-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.normal-submonoids-commutative-monoids
open import group-theory.semigroups
open import group-theory.submonoids-commutative-monoids
```

</details>

## Idea

The type `ℕ` of natural numbers equipped with `0` and `max-ℕ` forms a monoid.
Normal submonoids of this monoid are initial segments of the natural numbers.
Furthermore, the identity relation is a nonsaturated congruence relation on
`ℕ-Max`.

## Definition

```agda
semigroup-ℕ-Max : Semigroup lzero
pr1 semigroup-ℕ-Max = {!!}
pr1 (pr2 semigroup-ℕ-Max) = {!!}
pr2 (pr2 semigroup-ℕ-Max) = {!!}

monoid-ℕ-Max : Monoid lzero
pr1 monoid-ℕ-Max = {!!}
pr1 (pr2 monoid-ℕ-Max) = {!!}
pr1 (pr2 (pr2 monoid-ℕ-Max)) = {!!}
pr2 (pr2 (pr2 monoid-ℕ-Max)) = {!!}

ℕ-Max : Commutative-Monoid lzero
pr1 ℕ-Max = {!!}
pr2 ℕ-Max = {!!}
```

## Properties

### Normal Submonoids of `ℕ-Max` are initial segments of the natural numbers

```agda
module _
  {l : Level} (N : Normal-Commutative-Submonoid l ℕ-Max)
  where

  is-initial-segment-Normal-Commutative-Submonoid-ℕ-Max :
    is-initial-segment-subset-ℕ
      ( subset-Normal-Commutative-Submonoid ℕ-Max N)
  is-initial-segment-Normal-Commutative-Submonoid-ℕ-Max x H = {!!}

  initial-segment-Normal-Submonoid-ℕ-Max : initial-segment-ℕ l
  pr1 initial-segment-Normal-Submonoid-ℕ-Max = {!!}
```

### Initial segments of the natural numbers are normal submonoids of `ℕ-Max`

```agda
submonoid-initial-segment-ℕ-Max :
  {l : Level} (I : initial-segment-ℕ l) (i0 : is-in-initial-segment-ℕ I 0) →
  Commutative-Submonoid l ℕ-Max
pr1 (submonoid-initial-segment-ℕ-Max I i0) = {!!}
pr1 (pr2 (submonoid-initial-segment-ℕ-Max I i0)) = {!!}
pr2 (pr2 (submonoid-initial-segment-ℕ-Max I i0)) = {!!}

is-normal-submonoid-initial-segment-ℕ-Max :
  {l : Level} (I : initial-segment-ℕ l) (i0 : is-in-initial-segment-ℕ I 0) →
  is-normal-Commutative-Submonoid
    ℕ-Max
    (submonoid-initial-segment-ℕ-Max I i0)
is-normal-submonoid-initial-segment-ℕ-Max I i0 u zero-ℕ H K = {!!}
is-normal-submonoid-initial-segment-ℕ-Max I i0 zero-ℕ (succ-ℕ x) H K = {!!}
is-normal-submonoid-initial-segment-ℕ-Max I i0 (succ-ℕ u) (succ-ℕ x) H K = {!!}
```
