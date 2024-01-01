# The commutative semiring of natural numbers

```agda
module elementary-number-theory.commutative-semiring-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.monoid-of-natural-numbers-with-addition
open import elementary-number-theory.multiplication-natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.semirings
```

</details>

## Definition

### The commutative semiring of natural numbers

```agda
has-mul-ℕ-Commutative-Monoid :
  has-mul-Commutative-Monoid ℕ-Commutative-Monoid
pr1 (pr1 has-mul-ℕ-Commutative-Monoid) = {!!}
pr2 (pr1 has-mul-ℕ-Commutative-Monoid) = {!!}
pr1 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid)) = {!!}
pr1 (pr2 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid))) = {!!}
pr2 (pr2 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid))) = {!!}
pr1 (pr2 (pr2 has-mul-ℕ-Commutative-Monoid)) = {!!}
pr2 (pr2 (pr2 has-mul-ℕ-Commutative-Monoid)) = {!!}

ℕ-Semiring : Semiring lzero
ℕ-Semiring = {!!}
pr1 (pr2 ℕ-Semiring) = {!!}
pr1 (pr2 (pr2 ℕ-Semiring)) = {!!}
pr2 (pr2 (pr2 ℕ-Semiring)) = {!!}

ℕ-Commutative-Semiring : Commutative-Semiring lzero
ℕ-Commutative-Semiring = {!!}
pr2 ℕ-Commutative-Semiring = {!!}
```
