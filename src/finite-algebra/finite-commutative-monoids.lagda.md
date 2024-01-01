# Finite Commutative monoids

```agda
module finite-algebra.finite-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-monoids

open import foundation.identity-types
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A finite commutative monoid is a finite monoid `M` in which `xy = {!!}
all `x y : M`.

## Definition

### Finite commutative monoids

```agda
is-commutative-Monoid-𝔽 :
  {l : Level} (M : Monoid-𝔽 l) → UU l
is-commutative-Monoid-𝔽 M = {!!}

Commutative-Monoid-𝔽 : (l : Level) → UU (lsuc l)
Commutative-Monoid-𝔽 l = {!!}

module _
  {l : Level} (M : Commutative-Monoid-𝔽 l)
  where

  finite-monoid-Commutative-Monoid-𝔽 : Monoid-𝔽 l
  finite-monoid-Commutative-Monoid-𝔽 = {!!}

  monoid-Commutative-Monoid-𝔽 : Monoid l
  monoid-Commutative-Monoid-𝔽 = {!!}

  finite-type-Commutative-Monoid-𝔽 : 𝔽 l
  finite-type-Commutative-Monoid-𝔽 = {!!}

  type-Commutative-Monoid-𝔽 : UU l
  type-Commutative-Monoid-𝔽 = {!!}

  is-finite-type-Commutative-Monoid-𝔽 : is-finite type-Commutative-Monoid-𝔽
  is-finite-type-Commutative-Monoid-𝔽 = {!!}

  semigroup-Commutative-Monoid-𝔽 : Semigroup l
  semigroup-Commutative-Monoid-𝔽 = {!!}

  set-Commutative-Monoid-𝔽 : Set l
  set-Commutative-Monoid-𝔽 = {!!}

  is-set-type-Commutative-Monoid-𝔽 : is-set type-Commutative-Monoid-𝔽
  is-set-type-Commutative-Monoid-𝔽 = {!!}
```

### The multiplicative operation of a commutative monoid

```agda
  has-associative-mul-Commutative-Monoid-𝔽 :
    has-associative-mul-Set set-Commutative-Monoid-𝔽
  has-associative-mul-Commutative-Monoid-𝔽 = {!!}

  mul-Commutative-Monoid-𝔽 :
    (x y : type-Commutative-Monoid-𝔽) → type-Commutative-Monoid-𝔽
  mul-Commutative-Monoid-𝔽 = {!!}

  mul-Commutative-Monoid-𝔽' :
    (x y : type-Commutative-Monoid-𝔽) → type-Commutative-Monoid-𝔽
  mul-Commutative-Monoid-𝔽' = {!!}

  ap-mul-Commutative-Monoid-𝔽 :
    {x x' y y' : type-Commutative-Monoid-𝔽} →
    x ＝ x' → y ＝ y' →
    mul-Commutative-Monoid-𝔽 x y ＝ mul-Commutative-Monoid-𝔽 x' y'
  ap-mul-Commutative-Monoid-𝔽 = {!!}

  associative-mul-Commutative-Monoid-𝔽 :
    (x y z : type-Commutative-Monoid-𝔽) →
    ( mul-Commutative-Monoid-𝔽 (mul-Commutative-Monoid-𝔽 x y) z) ＝
    ( mul-Commutative-Monoid-𝔽 x (mul-Commutative-Monoid-𝔽 y z))
  associative-mul-Commutative-Monoid-𝔽 = {!!}

  commutative-mul-Commutative-Monoid-𝔽 :
    (x y : type-Commutative-Monoid-𝔽) →
    mul-Commutative-Monoid-𝔽 x y ＝ mul-Commutative-Monoid-𝔽 y x
  commutative-mul-Commutative-Monoid-𝔽 = {!!}

  commutative-monoid-Commutative-Monoid-𝔽 : Commutative-Monoid l
  pr1 commutative-monoid-Commutative-Monoid-𝔽 = {!!}

  interchange-mul-mul-Commutative-Monoid-𝔽 :
    (x y x' y' : type-Commutative-Monoid-𝔽) →
    ( mul-Commutative-Monoid-𝔽
      ( mul-Commutative-Monoid-𝔽 x y)
      ( mul-Commutative-Monoid-𝔽 x' y')) ＝
    ( mul-Commutative-Monoid-𝔽
      ( mul-Commutative-Monoid-𝔽 x x')
      ( mul-Commutative-Monoid-𝔽 y y'))
  interchange-mul-mul-Commutative-Monoid-𝔽 = {!!}

  right-swap-mul-Commutative-Monoid-𝔽 :
    (x y z : type-Commutative-Monoid-𝔽) →
    mul-Commutative-Monoid-𝔽 (mul-Commutative-Monoid-𝔽 x y) z ＝
    mul-Commutative-Monoid-𝔽 (mul-Commutative-Monoid-𝔽 x z) y
  right-swap-mul-Commutative-Monoid-𝔽 = {!!}

  left-swap-mul-Commutative-Monoid-𝔽 :
    (x y z : type-Commutative-Monoid-𝔽) →
    mul-Commutative-Monoid-𝔽 x (mul-Commutative-Monoid-𝔽 y z) ＝
    mul-Commutative-Monoid-𝔽 y (mul-Commutative-Monoid-𝔽 x z)
  left-swap-mul-Commutative-Monoid-𝔽 = {!!}
```

### The unit element of a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid-𝔽 l)
  where

  has-unit-Commutative-Monoid-𝔽 : is-unital (mul-Commutative-Monoid-𝔽 M)
  has-unit-Commutative-Monoid-𝔽 = {!!}

  unit-Commutative-Monoid-𝔽 : type-Commutative-Monoid-𝔽 M
  unit-Commutative-Monoid-𝔽 = {!!}

  left-unit-law-mul-Commutative-Monoid-𝔽 :
    (x : type-Commutative-Monoid-𝔽 M) →
    mul-Commutative-Monoid-𝔽 M unit-Commutative-Monoid-𝔽 x ＝ x
  left-unit-law-mul-Commutative-Monoid-𝔽 = {!!}

  right-unit-law-mul-Commutative-Monoid-𝔽 :
    (x : type-Commutative-Monoid-𝔽 M) →
    mul-Commutative-Monoid-𝔽 M x unit-Commutative-Monoid-𝔽 ＝ x
  right-unit-law-mul-Commutative-Monoid-𝔽 = {!!}
```

## Properties

### There is a finite number of ways to equip a finite type with a structure of finite commutative monoids

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-commutative-monoid-𝔽 : UU l
  structure-commutative-monoid-𝔽 = {!!}

  compute-structure-commutative-monoid-𝔽 :
    structure-commutative-monoid-𝔽 → Commutative-Monoid-𝔽 l
  pr1 (compute-structure-commutative-monoid-𝔽 (m , c)) = {!!}

  is-finite-structure-commutative-monoid-𝔽 :
    is-finite structure-commutative-monoid-𝔽
  is-finite-structure-commutative-monoid-𝔽 = {!!}
```
