# The abstract quaternion group of order `8`

```agda
module finite-group-theory.abstract-quaternion-group where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.semigroups

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The abstract quaternion group of order 8 is the group of the quaternions `1`,
`-1`, `i`, `-i`, `j`, `-j`, `k`, and `-k`.

## Definition

```agda
data Q8 : UU lzero where
  e-Q8 : Q8
  -e-Q8 : Q8
  i-Q8 : Q8
  -i-Q8 : Q8
  j-Q8 : Q8
  -j-Q8 : Q8
  k-Q8 : Q8
  -k-Q8 : Q8

mul-Q8 : Q8 → Q8 → Q8
mul-Q8 e-Q8 e-Q8 = {!!}
mul-Q8 e-Q8 -e-Q8 = {!!}
mul-Q8 e-Q8 i-Q8 = {!!}
mul-Q8 e-Q8 -i-Q8 = {!!}
mul-Q8 e-Q8 j-Q8 = {!!}
mul-Q8 e-Q8 -j-Q8 = {!!}
mul-Q8 e-Q8 k-Q8 = {!!}
mul-Q8 e-Q8 -k-Q8 = {!!}
mul-Q8 -e-Q8 e-Q8 = {!!}
mul-Q8 -e-Q8 -e-Q8 = {!!}
mul-Q8 -e-Q8 i-Q8 = {!!}
mul-Q8 -e-Q8 -i-Q8 = {!!}
mul-Q8 -e-Q8 j-Q8 = {!!}
mul-Q8 -e-Q8 -j-Q8 = {!!}
mul-Q8 -e-Q8 k-Q8 = {!!}
mul-Q8 -e-Q8 -k-Q8 = {!!}
mul-Q8 i-Q8 e-Q8 = {!!}
mul-Q8 i-Q8 -e-Q8 = {!!}
mul-Q8 i-Q8 i-Q8 = {!!}
mul-Q8 i-Q8 -i-Q8 = {!!}
mul-Q8 i-Q8 j-Q8 = {!!}
mul-Q8 i-Q8 -j-Q8 = {!!}
mul-Q8 i-Q8 k-Q8 = {!!}
mul-Q8 i-Q8 -k-Q8 = {!!}
mul-Q8 -i-Q8 e-Q8 = {!!}
mul-Q8 -i-Q8 -e-Q8 = {!!}
mul-Q8 -i-Q8 i-Q8 = {!!}
mul-Q8 -i-Q8 -i-Q8 = {!!}
mul-Q8 -i-Q8 j-Q8 = {!!}
mul-Q8 -i-Q8 -j-Q8 = {!!}
mul-Q8 -i-Q8 k-Q8 = {!!}
mul-Q8 -i-Q8 -k-Q8 = {!!}
mul-Q8 j-Q8 e-Q8 = {!!}
mul-Q8 j-Q8 -e-Q8 = {!!}
mul-Q8 j-Q8 i-Q8 = {!!}
mul-Q8 j-Q8 -i-Q8 = {!!}
mul-Q8 j-Q8 j-Q8 = {!!}
mul-Q8 j-Q8 -j-Q8 = {!!}
mul-Q8 j-Q8 k-Q8 = {!!}
mul-Q8 j-Q8 -k-Q8 = {!!}
mul-Q8 -j-Q8 e-Q8 = {!!}
mul-Q8 -j-Q8 -e-Q8 = {!!}
mul-Q8 -j-Q8 i-Q8 = {!!}
mul-Q8 -j-Q8 -i-Q8 = {!!}
mul-Q8 -j-Q8 j-Q8 = {!!}
mul-Q8 -j-Q8 -j-Q8 = {!!}
mul-Q8 -j-Q8 k-Q8 = {!!}
mul-Q8 -j-Q8 -k-Q8 = {!!}
mul-Q8 k-Q8 e-Q8 = {!!}
mul-Q8 k-Q8 -e-Q8 = {!!}
mul-Q8 k-Q8 i-Q8 = {!!}
mul-Q8 k-Q8 -i-Q8 = {!!}
mul-Q8 k-Q8 j-Q8 = {!!}
mul-Q8 k-Q8 -j-Q8 = {!!}
mul-Q8 k-Q8 k-Q8 = {!!}
mul-Q8 k-Q8 -k-Q8 = {!!}
mul-Q8 -k-Q8 e-Q8 = {!!}
mul-Q8 -k-Q8 -e-Q8 = {!!}
mul-Q8 -k-Q8 i-Q8 = {!!}
mul-Q8 -k-Q8 -i-Q8 = {!!}
mul-Q8 -k-Q8 j-Q8 = {!!}
mul-Q8 -k-Q8 -j-Q8 = {!!}
mul-Q8 -k-Q8 k-Q8 = {!!}
mul-Q8 -k-Q8 -k-Q8 = {!!}

inv-Q8 : Q8 → Q8
inv-Q8 e-Q8 = {!!}
inv-Q8 -e-Q8 = {!!}
inv-Q8 i-Q8 = {!!}
inv-Q8 -i-Q8 = {!!}
inv-Q8 j-Q8 = {!!}
inv-Q8 -j-Q8 = {!!}
inv-Q8 k-Q8 = {!!}
inv-Q8 -k-Q8 = {!!}

left-unit-law-mul-Q8 : (x : Q8) → Id (mul-Q8 e-Q8 x) x
left-unit-law-mul-Q8 e-Q8 = {!!}
left-unit-law-mul-Q8 -e-Q8 = {!!}
left-unit-law-mul-Q8 i-Q8 = {!!}
left-unit-law-mul-Q8 -i-Q8 = {!!}
left-unit-law-mul-Q8 j-Q8 = {!!}
left-unit-law-mul-Q8 -j-Q8 = {!!}
left-unit-law-mul-Q8 k-Q8 = {!!}
left-unit-law-mul-Q8 -k-Q8 = {!!}

right-unit-law-mul-Q8 : (x : Q8) → Id (mul-Q8 x e-Q8) x
right-unit-law-mul-Q8 e-Q8 = {!!}
right-unit-law-mul-Q8 -e-Q8 = {!!}
right-unit-law-mul-Q8 i-Q8 = {!!}
right-unit-law-mul-Q8 -i-Q8 = {!!}
right-unit-law-mul-Q8 j-Q8 = {!!}
right-unit-law-mul-Q8 -j-Q8 = {!!}
right-unit-law-mul-Q8 k-Q8 = {!!}
right-unit-law-mul-Q8 -k-Q8 = {!!}

associative-mul-Q8 :
  (x y z : Q8) → Id (mul-Q8 (mul-Q8 x y) z) (mul-Q8 x (mul-Q8 y z))
associative-mul-Q8 e-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 e-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 -e-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 i-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 -i-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 j-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 -j-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 k-Q8 -k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -e-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -i-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -j-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 k-Q8 -k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 -e-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 -i-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 -j-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 k-Q8 = {!!}
associative-mul-Q8 -k-Q8 -k-Q8 -k-Q8 = {!!}

left-inverse-law-mul-Q8 : (x : Q8) → Id (mul-Q8 (inv-Q8 x) x) e-Q8
left-inverse-law-mul-Q8 e-Q8 = {!!}
left-inverse-law-mul-Q8 -e-Q8 = {!!}
left-inverse-law-mul-Q8 i-Q8 = {!!}
left-inverse-law-mul-Q8 -i-Q8 = {!!}
left-inverse-law-mul-Q8 j-Q8 = {!!}
left-inverse-law-mul-Q8 -j-Q8 = {!!}
left-inverse-law-mul-Q8 k-Q8 = {!!}
left-inverse-law-mul-Q8 -k-Q8 = {!!}

right-inverse-law-mul-Q8 : (x : Q8) → Id (mul-Q8 x (inv-Q8 x)) e-Q8
right-inverse-law-mul-Q8 e-Q8 = {!!}
right-inverse-law-mul-Q8 -e-Q8 = {!!}
right-inverse-law-mul-Q8 i-Q8 = {!!}
right-inverse-law-mul-Q8 -i-Q8 = {!!}
right-inverse-law-mul-Q8 j-Q8 = {!!}
right-inverse-law-mul-Q8 -j-Q8 = {!!}
right-inverse-law-mul-Q8 k-Q8 = {!!}
right-inverse-law-mul-Q8 -k-Q8 = {!!}

Eq-Q8 : Q8 → Q8 → UU lzero
Eq-Q8 e-Q8 e-Q8 = {!!}
Eq-Q8 e-Q8 -e-Q8 = {!!}
Eq-Q8 e-Q8 i-Q8 = {!!}
Eq-Q8 e-Q8 -i-Q8 = {!!}
Eq-Q8 e-Q8 j-Q8 = {!!}
Eq-Q8 e-Q8 -j-Q8 = {!!}
Eq-Q8 e-Q8 k-Q8 = {!!}
Eq-Q8 e-Q8 -k-Q8 = {!!}
Eq-Q8 -e-Q8 e-Q8 = {!!}
Eq-Q8 -e-Q8 -e-Q8 = {!!}
Eq-Q8 -e-Q8 i-Q8 = {!!}
Eq-Q8 -e-Q8 -i-Q8 = {!!}
Eq-Q8 -e-Q8 j-Q8 = {!!}
Eq-Q8 -e-Q8 -j-Q8 = {!!}
Eq-Q8 -e-Q8 k-Q8 = {!!}
Eq-Q8 -e-Q8 -k-Q8 = {!!}
Eq-Q8 i-Q8 e-Q8 = {!!}
Eq-Q8 i-Q8 -e-Q8 = {!!}
Eq-Q8 i-Q8 i-Q8 = {!!}
Eq-Q8 i-Q8 -i-Q8 = {!!}
Eq-Q8 i-Q8 j-Q8 = {!!}
Eq-Q8 i-Q8 -j-Q8 = {!!}
Eq-Q8 i-Q8 k-Q8 = {!!}
Eq-Q8 i-Q8 -k-Q8 = {!!}
Eq-Q8 -i-Q8 e-Q8 = {!!}
Eq-Q8 -i-Q8 -e-Q8 = {!!}
Eq-Q8 -i-Q8 i-Q8 = {!!}
Eq-Q8 -i-Q8 -i-Q8 = {!!}
Eq-Q8 -i-Q8 j-Q8 = {!!}
Eq-Q8 -i-Q8 -j-Q8 = {!!}
Eq-Q8 -i-Q8 k-Q8 = {!!}
Eq-Q8 -i-Q8 -k-Q8 = {!!}
Eq-Q8 j-Q8 e-Q8 = {!!}
Eq-Q8 j-Q8 -e-Q8 = {!!}
Eq-Q8 j-Q8 i-Q8 = {!!}
Eq-Q8 j-Q8 -i-Q8 = {!!}
Eq-Q8 j-Q8 j-Q8 = {!!}
Eq-Q8 j-Q8 -j-Q8 = {!!}
Eq-Q8 j-Q8 k-Q8 = {!!}
Eq-Q8 j-Q8 -k-Q8 = {!!}
Eq-Q8 -j-Q8 e-Q8 = {!!}
Eq-Q8 -j-Q8 -e-Q8 = {!!}
Eq-Q8 -j-Q8 i-Q8 = {!!}
Eq-Q8 -j-Q8 -i-Q8 = {!!}
Eq-Q8 -j-Q8 j-Q8 = {!!}
Eq-Q8 -j-Q8 -j-Q8 = {!!}
Eq-Q8 -j-Q8 k-Q8 = {!!}
Eq-Q8 -j-Q8 -k-Q8 = {!!}
Eq-Q8 k-Q8 e-Q8 = {!!}
Eq-Q8 k-Q8 -e-Q8 = {!!}
Eq-Q8 k-Q8 i-Q8 = {!!}
Eq-Q8 k-Q8 -i-Q8 = {!!}
Eq-Q8 k-Q8 j-Q8 = {!!}
Eq-Q8 k-Q8 -j-Q8 = {!!}
Eq-Q8 k-Q8 k-Q8 = {!!}
Eq-Q8 k-Q8 -k-Q8 = {!!}
Eq-Q8 -k-Q8 e-Q8 = {!!}
Eq-Q8 -k-Q8 -e-Q8 = {!!}
Eq-Q8 -k-Q8 i-Q8 = {!!}
Eq-Q8 -k-Q8 -i-Q8 = {!!}
Eq-Q8 -k-Q8 j-Q8 = {!!}
Eq-Q8 -k-Q8 -j-Q8 = {!!}
Eq-Q8 -k-Q8 k-Q8 = {!!}
Eq-Q8 -k-Q8 -k-Q8 = {!!}

refl-Eq-Q8 : (x : Q8) → Eq-Q8 x x
refl-Eq-Q8 e-Q8 = {!!}
refl-Eq-Q8 -e-Q8 = {!!}
refl-Eq-Q8 i-Q8 = {!!}
refl-Eq-Q8 -i-Q8 = {!!}
refl-Eq-Q8 j-Q8 = {!!}
refl-Eq-Q8 -j-Q8 = {!!}
refl-Eq-Q8 k-Q8 = {!!}
refl-Eq-Q8 -k-Q8 = {!!}

Eq-eq-Q8 : {x y : Q8} → Id x y → Eq-Q8 x y
Eq-eq-Q8 {x} refl = {!!}

eq-Eq-Q8 : (x y : Q8) → Eq-Q8 x y → Id x y
eq-Eq-Q8 e-Q8 e-Q8 e = {!!}
eq-Eq-Q8 -e-Q8 -e-Q8 e = {!!}
eq-Eq-Q8 i-Q8 i-Q8 e = {!!}
eq-Eq-Q8 -i-Q8 -i-Q8 e = {!!}
eq-Eq-Q8 j-Q8 j-Q8 e = {!!}
eq-Eq-Q8 -j-Q8 -j-Q8 e = {!!}
eq-Eq-Q8 k-Q8 k-Q8 e = {!!}
eq-Eq-Q8 -k-Q8 -k-Q8 e = {!!}

is-decidable-Eq-Q8 : (x y : Q8) → is-decidable (Eq-Q8 x y)
is-decidable-Eq-Q8 e-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 e-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 -e-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 i-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 -i-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 j-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 -j-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 k-Q8 -k-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 e-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 -e-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 i-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 -i-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 j-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 -j-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 k-Q8 = {!!}
is-decidable-Eq-Q8 -k-Q8 -k-Q8 = {!!}

has-decidable-equality-Q8 : has-decidable-equality Q8
has-decidable-equality-Q8 x y = {!!}

is-set-Q8 : is-set Q8
is-set-Q8 = {!!}

Q8-Set : Set lzero
Q8-Set = {!!}

Q8-Semigroup : Semigroup lzero
Q8-Semigroup = {!!}

Q8-Group : Group lzero
Q8-Group = {!!}

is-noncommutative-mul-Q8 :
  ¬ ((x y : Q8) → Id (mul-Q8 x y) (mul-Q8 y x))
is-noncommutative-mul-Q8 f = {!!}

map-equiv-count-Q8 : Fin 8 → Q8
map-equiv-count-Q8 (inl (inl (inl (inl (inl (inl (inl (inr star)))))))) = {!!}
map-equiv-count-Q8 (inl (inl (inl (inl (inl (inl (inr star))))))) = {!!}
map-equiv-count-Q8 (inl (inl (inl (inl (inl (inr star)))))) = {!!}
map-equiv-count-Q8 (inl (inl (inl (inl (inr star))))) = {!!}
map-equiv-count-Q8 (inl (inl (inl (inr star)))) = {!!}
map-equiv-count-Q8 (inl (inl (inr star))) = {!!}
map-equiv-count-Q8 (inl (inr star)) = {!!}
map-equiv-count-Q8 (inr star) = {!!}

map-inv-equiv-count-Q8 : Q8 → Fin 8
map-inv-equiv-count-Q8 e-Q8 = {!!}
map-inv-equiv-count-Q8 -e-Q8 = {!!}
map-inv-equiv-count-Q8 i-Q8 = {!!}
map-inv-equiv-count-Q8 -i-Q8 = {!!}
map-inv-equiv-count-Q8 j-Q8 = {!!}
map-inv-equiv-count-Q8 -j-Q8 = {!!}
map-inv-equiv-count-Q8 k-Q8 = {!!}
map-inv-equiv-count-Q8 -k-Q8 = {!!}

is-section-map-inv-equiv-count-Q8 :
  ( map-equiv-count-Q8 ∘ map-inv-equiv-count-Q8) ~ id
is-section-map-inv-equiv-count-Q8 e-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 -e-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 i-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 -i-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 j-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 -j-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 k-Q8 = {!!}
is-section-map-inv-equiv-count-Q8 -k-Q8 = {!!}

is-retraction-map-inv-equiv-count-Q8 :
  ( map-inv-equiv-count-Q8 ∘ map-equiv-count-Q8) ~ id
is-retraction-map-inv-equiv-count-Q8
  (inl (inl (inl (inl (inl (inl (inl (inr star)))))))) = {!!}
is-retraction-map-inv-equiv-count-Q8
  (inl (inl (inl (inl (inl (inl (inr star))))))) = {!!}
is-retraction-map-inv-equiv-count-Q8 (inl (inl (inl (inl (inl (inr star)))))) = {!!}
is-retraction-map-inv-equiv-count-Q8 (inl (inl (inl (inl (inr star))))) = {!!}
is-retraction-map-inv-equiv-count-Q8 (inl (inl (inl (inr star)))) = {!!}
is-retraction-map-inv-equiv-count-Q8 (inl (inl (inr star))) = {!!}
is-retraction-map-inv-equiv-count-Q8 (inl (inr star)) = {!!}
is-retraction-map-inv-equiv-count-Q8 (inr star) = {!!}

is-equiv-map-equiv-count-Q8 : is-equiv map-equiv-count-Q8
is-equiv-map-equiv-count-Q8 = {!!}

equiv-count-Q8 : Fin 8 ≃ Q8
equiv-count-Q8 = {!!}

count-Q8 : count Q8
count-Q8 = {!!}

is-finite-Q8 : is-finite Q8
is-finite-Q8 = {!!}

Q8-𝔽 : 𝔽 lzero
Q8-𝔽 = {!!}

has-cardinality-eight-Q8 : has-cardinality 8 Q8
has-cardinality-eight-Q8 = {!!}

Q8-UU-Fin-8 : UU-Fin lzero 8
Q8-UU-Fin-8 = {!!}

has-finite-cardinality-Q8 : has-finite-cardinality Q8
has-finite-cardinality-Q8 = {!!}
```
