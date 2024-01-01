# Inverse semigroups

```agda
module group-theory.inverse-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

An inverse semigroup is an algebraic structure that models partial bijections.
In an inverse semigroup, elements have unique inverses in the sense that for
each `x` there is a unique `y` such that `xyx = {!!}

## Definition

```agda
is-inverse-Semigroup :
  {l : Level} (S : Semigroup l) → UU l
is-inverse-Semigroup = {!!}

Inverse-Semigroup : (l : Level) → UU (lsuc l)
Inverse-Semigroup l = {!!}

module _
  {l : Level} (S : Inverse-Semigroup l)
  where

  semigroup-Inverse-Semigroup : Semigroup l
  semigroup-Inverse-Semigroup = {!!}

  set-Inverse-Semigroup : Set l
  set-Inverse-Semigroup = {!!}

  type-Inverse-Semigroup : UU l
  type-Inverse-Semigroup = {!!}

  is-set-type-Inverse-Semigroup : is-set type-Inverse-Semigroup
  is-set-type-Inverse-Semigroup = {!!}

  mul-Inverse-Semigroup :
    (x y : type-Inverse-Semigroup) → type-Inverse-Semigroup
  mul-Inverse-Semigroup = {!!}

  mul-Inverse-Semigroup' :
    (x y : type-Inverse-Semigroup) → type-Inverse-Semigroup
  mul-Inverse-Semigroup' = {!!}

  associative-mul-Inverse-Semigroup :
    (x y z : type-Inverse-Semigroup) →
    Id
      ( mul-Inverse-Semigroup (mul-Inverse-Semigroup x y) z)
      ( mul-Inverse-Semigroup x (mul-Inverse-Semigroup y z))
  associative-mul-Inverse-Semigroup = {!!}

  is-inverse-semigroup-Inverse-Semigroup :
    is-inverse-Semigroup semigroup-Inverse-Semigroup
  is-inverse-semigroup-Inverse-Semigroup = {!!}

  inv-Inverse-Semigroup : type-Inverse-Semigroup → type-Inverse-Semigroup
  inv-Inverse-Semigroup x = {!!}

  inner-inverse-law-mul-Inverse-Semigroup :
    (x : type-Inverse-Semigroup) →
    Id
      ( mul-Inverse-Semigroup
        ( mul-Inverse-Semigroup x (inv-Inverse-Semigroup x))
        ( x))
      ( x)
  inner-inverse-law-mul-Inverse-Semigroup = {!!}

  outer-inverse-law-mul-Inverse-Semigroup :
    (x : type-Inverse-Semigroup) →
    Id
      ( mul-Inverse-Semigroup
        ( mul-Inverse-Semigroup (inv-Inverse-Semigroup x) x)
        ( inv-Inverse-Semigroup x))
      ( inv-Inverse-Semigroup x)
  outer-inverse-law-mul-Inverse-Semigroup = {!!}
```
