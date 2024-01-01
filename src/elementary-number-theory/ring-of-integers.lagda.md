# The ring of integers

```agda
module elementary-number-theory.ring-of-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.free-groups-with-one-generator
open import group-theory.homomorphisms-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.initial-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Definition

```agda
ℤ-Ring : Ring lzero
ℤ-Ring = {!!}
pr1 (pr1 (pr2 ℤ-Ring)) = {!!}
pr2 (pr1 (pr2 ℤ-Ring)) = {!!}
pr1 (pr1 (pr2 (pr2 ℤ-Ring))) = {!!}
pr1 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = {!!}
pr2 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = {!!}
pr1 (pr2 (pr2 (pr2 ℤ-Ring))) = {!!}
pr2 (pr2 (pr2 (pr2 ℤ-Ring))) = {!!}

ℤ-Commutative-Ring : Commutative-Ring lzero
ℤ-Commutative-Ring = {!!}
pr2 ℤ-Commutative-Ring = {!!}
```

## Properties

### The integer multiples in `ℤ-Ring` coincide with multiplication in `ℤ`

```agda
is-mul-integer-multiple-ℤ-Ring :
  (k l : ℤ) → integer-multiple-Ring ℤ-Ring k l ＝ mul-ℤ k l
is-mul-integer-multiple-ℤ-Ring = {!!}

is-integer-multiple-ℤ :
  (k : ℤ) → integer-multiple-Ring ℤ-Ring k one-ℤ ＝ k
is-integer-multiple-ℤ = {!!}
```

### The ring of integers is the initial ring

#### The homomorphism from `ℤ` to a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  hom-group-initial-hom-Ring : hom-Group ℤ-Group (group-Ring R)
  hom-group-initial-hom-Ring = {!!}

  map-initial-hom-Ring : ℤ → type-Ring R
  map-initial-hom-Ring = {!!}

  preserves-add-initial-hom-Ring :
    (k l : ℤ) →
    map-initial-hom-Ring (add-ℤ k l) ＝
    add-Ring R (map-initial-hom-Ring k) (map-initial-hom-Ring l)
  preserves-add-initial-hom-Ring = {!!}

  preserves-one-initial-hom-Ring : map-initial-hom-Ring one-ℤ ＝ one-Ring R
  preserves-one-initial-hom-Ring = {!!}

  preserves-mul-initial-hom-Ring :
    (k l : ℤ) →
    map-initial-hom-Ring (mul-ℤ k l) ＝
    mul-Ring R (map-initial-hom-Ring k) (map-initial-hom-Ring l)
  preserves-mul-initial-hom-Ring = {!!}

  initial-hom-Ring : hom-Ring ℤ-Ring R
  initial-hom-Ring = {!!}
```

#### Any ring homomorphisms from `ℤ` to `R` is equal to the homomorphism `initial-hom-Ring`

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-initial-hom-Ring :
    (f : hom-Ring ℤ-Ring R) → htpy-hom-Ring ℤ-Ring R (initial-hom-Ring R) f
  htpy-initial-hom-Ring = {!!}

  contraction-initial-hom-Ring :
    (f : hom-Ring ℤ-Ring R) → initial-hom-Ring R ＝ f
  contraction-initial-hom-Ring = {!!}
```

#### The ring of integers is the initial ring

```agda
is-initial-ℤ-Ring : is-initial-Ring ℤ-Ring
is-initial-ℤ-Ring = {!!}
pr2 (is-initial-ℤ-Ring S) f = {!!}
```

### Integer multiplication in the ring of integers coincides with multiplication of integers

```agda
integer-multiple-one-ℤ-Ring :
  (k : ℤ) → integer-multiple-Ring ℤ-Ring k one-ℤ ＝ k
integer-multiple-one-ℤ-Ring = {!!}

compute-integer-multiple-ℤ-Ring :
  (k l : ℤ) → integer-multiple-Ring ℤ-Ring k l ＝ mul-ℤ k l
compute-integer-multiple-ℤ-Ring = {!!}
```
