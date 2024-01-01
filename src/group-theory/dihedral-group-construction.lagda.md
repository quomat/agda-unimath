# The dihedral group construction

```agda
module group-theory.dihedral-group-construction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

When `A` is an abelian group, we can put a group structure on the disjoint union
`A+A`, which specializes to the dihedral groups when we take `A := {!!}

## Definitions

```agda
module _
  {l : Level} (A : Ab l)
  where

  set-dihedral-group-Ab : Set l
  set-dihedral-group-Ab = {!!}

  type-dihedral-group-Ab : UU l
  type-dihedral-group-Ab = {!!}

  is-set-type-dihedral-group-Ab : is-set type-dihedral-group-Ab
  is-set-type-dihedral-group-Ab = {!!}

  unit-dihedral-group-Ab : type-dihedral-group-Ab
  unit-dihedral-group-Ab = {!!}

  mul-dihedral-group-Ab :
    (x y : type-dihedral-group-Ab) → type-dihedral-group-Ab
  mul-dihedral-group-Ab = {!!}

  inv-dihedral-group-Ab : type-dihedral-group-Ab → type-dihedral-group-Ab
  inv-dihedral-group-Ab = {!!}

  associative-mul-dihedral-group-Ab :
    (x y z : type-dihedral-group-Ab) →
    (mul-dihedral-group-Ab (mul-dihedral-group-Ab x y) z) ＝
    (mul-dihedral-group-Ab x (mul-dihedral-group-Ab y z))
  associative-mul-dihedral-group-Ab = {!!}

  left-unit-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    (mul-dihedral-group-Ab unit-dihedral-group-Ab x) ＝ x
  left-unit-law-mul-dihedral-group-Ab = {!!}

  right-unit-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    (mul-dihedral-group-Ab x unit-dihedral-group-Ab) ＝ x
  right-unit-law-mul-dihedral-group-Ab = {!!}

  left-inverse-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    ( mul-dihedral-group-Ab (inv-dihedral-group-Ab x) x) ＝
    ( unit-dihedral-group-Ab)
  left-inverse-law-mul-dihedral-group-Ab = {!!}

  right-inverse-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    ( mul-dihedral-group-Ab x (inv-dihedral-group-Ab x)) ＝
    ( unit-dihedral-group-Ab)
  right-inverse-law-mul-dihedral-group-Ab = {!!}

  semigroup-dihedral-group-Ab : Semigroup l
  semigroup-dihedral-group-Ab = {!!}

  monoid-dihedral-group-Ab : Monoid l
  monoid-dihedral-group-Ab = {!!}

  dihedral-group-Ab : Group l
  dihedral-group-Ab = {!!}
```
