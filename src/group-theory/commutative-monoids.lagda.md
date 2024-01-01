# Commutative monoids

```agda
module group-theory.commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

A commutative monoid is a monoid `M` in which `xy = {!!}

## Definition

### Commutative monoids

```agda
is-commutative-Monoid :
  {l : Level} (M : Monoid l) → UU l
is-commutative-Monoid = {!!}

Commutative-Monoid : (l : Level) → UU (lsuc l)
Commutative-Monoid l = {!!}

module _
  {l : Level} (M : Commutative-Monoid l)
  where

  monoid-Commutative-Monoid : Monoid l
  monoid-Commutative-Monoid = {!!}

  semigroup-Commutative-Monoid : Semigroup l
  semigroup-Commutative-Monoid = {!!}

  set-Commutative-Monoid : Set l
  set-Commutative-Monoid = {!!}

  type-Commutative-Monoid : UU l
  type-Commutative-Monoid = {!!}

  is-set-type-Commutative-Monoid : is-set type-Commutative-Monoid
  is-set-type-Commutative-Monoid = {!!}
```

### The multiplicative operation of a commutative monoid

```agda
  has-associative-mul-Commutative-Monoid :
    has-associative-mul-Set set-Commutative-Monoid
  has-associative-mul-Commutative-Monoid = {!!}

  mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid) → type-Commutative-Monoid
  mul-Commutative-Monoid = {!!}

  mul-Commutative-Monoid' :
    (x y : type-Commutative-Monoid) → type-Commutative-Monoid
  mul-Commutative-Monoid' = {!!}

  ap-mul-Commutative-Monoid :
    {x x' y y' : type-Commutative-Monoid} →
    x ＝ x' → y ＝ y' →
    mul-Commutative-Monoid x y ＝ mul-Commutative-Monoid x' y'
  ap-mul-Commutative-Monoid = {!!}

  associative-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    ( mul-Commutative-Monoid (mul-Commutative-Monoid x y) z) ＝
    ( mul-Commutative-Monoid x (mul-Commutative-Monoid y z))
  associative-mul-Commutative-Monoid = {!!}

  commutative-mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid) →
    mul-Commutative-Monoid x y ＝ mul-Commutative-Monoid y x
  commutative-mul-Commutative-Monoid = {!!}

  interchange-mul-mul-Commutative-Monoid :
    (x y x' y' : type-Commutative-Monoid) →
    ( mul-Commutative-Monoid
      ( mul-Commutative-Monoid x y)
      ( mul-Commutative-Monoid x' y')) ＝
    ( mul-Commutative-Monoid
      ( mul-Commutative-Monoid x x')
      ( mul-Commutative-Monoid y y'))
  interchange-mul-mul-Commutative-Monoid = {!!}

  right-swap-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    mul-Commutative-Monoid (mul-Commutative-Monoid x y) z ＝
    mul-Commutative-Monoid (mul-Commutative-Monoid x z) y
  right-swap-mul-Commutative-Monoid = {!!}

  left-swap-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    mul-Commutative-Monoid x (mul-Commutative-Monoid y z) ＝
    mul-Commutative-Monoid y (mul-Commutative-Monoid x z)
  left-swap-mul-Commutative-Monoid = {!!}
```

### The unit element of a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  has-unit-Commutative-Monoid : is-unital (mul-Commutative-Monoid M)
  has-unit-Commutative-Monoid = {!!}

  unit-Commutative-Monoid : type-Commutative-Monoid M
  unit-Commutative-Monoid = {!!}

  left-unit-law-mul-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    mul-Commutative-Monoid M unit-Commutative-Monoid x ＝ x
  left-unit-law-mul-Commutative-Monoid = {!!}

  right-unit-law-mul-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    mul-Commutative-Monoid M x unit-Commutative-Monoid ＝ x
  right-unit-law-mul-Commutative-Monoid = {!!}

  is-unit-Commutative-Monoid : type-Commutative-Monoid M → UU l
  is-unit-Commutative-Monoid x = {!!}

  is-unit-prop-Commutative-Monoid : type-Commutative-Monoid M → Prop l
  is-unit-prop-Commutative-Monoid x = {!!}
```
