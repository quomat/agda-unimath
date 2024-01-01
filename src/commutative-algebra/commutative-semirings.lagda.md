# Commutative semirings

```agda
module commutative-algebra.commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids

open import ring-theory.semirings
```

</details>

## Idea

A semiring `A` is said to be **commutative** if its multiplicative operation is
commutative, i.e., if `xy = {!!}

## Definition

### Main definition

```agda
is-commutative-Semiring : {l : Level} → Semiring l → UU l
is-commutative-Semiring = {!!}

is-prop-is-commutative-Semiring :
  { l : Level} (A : Semiring l) → is-prop (is-commutative-Semiring A)
is-prop-is-commutative-Semiring = {!!}

Commutative-Semiring :
  ( l : Level) → UU (lsuc l)
Commutative-Semiring = {!!}
```

### Immediate infrastructure for commutative semirings

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  semiring-Commutative-Semiring : Semiring l
  semiring-Commutative-Semiring = {!!}

  additive-commutative-monoid-Commutative-Semiring : Commutative-Monoid l
  additive-commutative-monoid-Commutative-Semiring = {!!}

  multiplicative-monoid-Commutative-Semiring : Monoid l
  multiplicative-monoid-Commutative-Semiring = {!!}

  set-Commutative-Semiring : Set l
  set-Commutative-Semiring = {!!}

  type-Commutative-Semiring : UU l
  type-Commutative-Semiring = {!!}

  is-set-type-Commutative-Semiring : is-set type-Commutative-Semiring
  is-set-type-Commutative-Semiring = {!!}

  zero-Commutative-Semiring : type-Commutative-Semiring
  zero-Commutative-Semiring = {!!}

  is-zero-Commutative-Semiring : type-Commutative-Semiring → UU l
  is-zero-Commutative-Semiring = {!!}

  is-nonzero-Commutative-Semiring : type-Commutative-Semiring → UU l
  is-nonzero-Commutative-Semiring = {!!}

  add-Commutative-Semiring :
    type-Commutative-Semiring → type-Commutative-Semiring →
    type-Commutative-Semiring
  add-Commutative-Semiring = {!!}

  add-Commutative-Semiring' :
    type-Commutative-Semiring → type-Commutative-Semiring →
    type-Commutative-Semiring
  add-Commutative-Semiring' = {!!}

  ap-add-Commutative-Semiring :
    {x x' y y' : type-Commutative-Semiring} →
    (x ＝ x') → (y ＝ y') →
    add-Commutative-Semiring x y ＝ add-Commutative-Semiring x' y'
  ap-add-Commutative-Semiring = {!!}

  associative-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( add-Commutative-Semiring (add-Commutative-Semiring x y) z) ＝
    ( add-Commutative-Semiring x (add-Commutative-Semiring y z))
  associative-add-Commutative-Semiring = {!!}

  left-unit-law-add-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    add-Commutative-Semiring zero-Commutative-Semiring x ＝ x
  left-unit-law-add-Commutative-Semiring = {!!}

  right-unit-law-add-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    add-Commutative-Semiring x zero-Commutative-Semiring ＝ x
  right-unit-law-add-Commutative-Semiring = {!!}

  commutative-add-Commutative-Semiring :
    (x y : type-Commutative-Semiring) →
    add-Commutative-Semiring x y ＝ add-Commutative-Semiring y x
  commutative-add-Commutative-Semiring = {!!}

  interchange-add-add-Commutative-Semiring :
    (x y x' y' : type-Commutative-Semiring) →
    ( add-Commutative-Semiring
      ( add-Commutative-Semiring x y)
      ( add-Commutative-Semiring x' y')) ＝
    ( add-Commutative-Semiring
      ( add-Commutative-Semiring x x')
      ( add-Commutative-Semiring y y'))
  interchange-add-add-Commutative-Semiring = {!!}

  right-swap-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( add-Commutative-Semiring (add-Commutative-Semiring x y) z) ＝
    ( add-Commutative-Semiring (add-Commutative-Semiring x z) y)
  right-swap-add-Commutative-Semiring = {!!}

  left-swap-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( add-Commutative-Semiring x (add-Commutative-Semiring y z)) ＝
    ( add-Commutative-Semiring y (add-Commutative-Semiring x z))
  left-swap-add-Commutative-Semiring = {!!}

  mul-Commutative-Semiring :
    (x y : type-Commutative-Semiring) → type-Commutative-Semiring
  mul-Commutative-Semiring = {!!}

  mul-Commutative-Semiring' :
    (x y : type-Commutative-Semiring) → type-Commutative-Semiring
  mul-Commutative-Semiring' = {!!}

  one-Commutative-Semiring : type-Commutative-Semiring
  one-Commutative-Semiring = {!!}

  left-unit-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring one-Commutative-Semiring x ＝ x
  left-unit-law-mul-Commutative-Semiring = {!!}

  right-unit-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring x one-Commutative-Semiring ＝ x
  right-unit-law-mul-Commutative-Semiring = {!!}

  associative-mul-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring (mul-Commutative-Semiring x y) z ＝
    mul-Commutative-Semiring x (mul-Commutative-Semiring y z)
  associative-mul-Commutative-Semiring = {!!}

  left-distributive-mul-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( mul-Commutative-Semiring x (add-Commutative-Semiring y z)) ＝
    ( add-Commutative-Semiring
      ( mul-Commutative-Semiring x y)
      ( mul-Commutative-Semiring x z))
  left-distributive-mul-add-Commutative-Semiring = {!!}

  right-distributive-mul-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( mul-Commutative-Semiring (add-Commutative-Semiring x y) z) ＝
    ( add-Commutative-Semiring
      ( mul-Commutative-Semiring x z)
      ( mul-Commutative-Semiring y z))
  right-distributive-mul-add-Commutative-Semiring = {!!}

  commutative-mul-Commutative-Semiring :
    (x y : type-Commutative-Semiring) →
    mul-Commutative-Semiring x y ＝ mul-Commutative-Semiring y x
  commutative-mul-Commutative-Semiring = {!!}

  multiplicative-commutative-monoid-Commutative-Semiring :
    Commutative-Monoid l
  multiplicative-commutative-monoid-Commutative-Semiring = {!!}

  left-zero-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring zero-Commutative-Semiring x ＝
    zero-Commutative-Semiring
  left-zero-law-mul-Commutative-Semiring = {!!}

  right-zero-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring x zero-Commutative-Semiring ＝
    zero-Commutative-Semiring
  right-zero-law-mul-Commutative-Semiring = {!!}

  right-swap-mul-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring (mul-Commutative-Semiring x y) z ＝
    mul-Commutative-Semiring (mul-Commutative-Semiring x z) y
  right-swap-mul-Commutative-Semiring = {!!}

  left-swap-mul-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring x (mul-Commutative-Semiring y z) ＝
    mul-Commutative-Semiring y (mul-Commutative-Semiring x z)
  left-swap-mul-Commutative-Semiring = {!!}
```

## Operations

### Scalar multiplication of elements of a commutative ring by natural numbers

```agda
  mul-nat-scalar-Commutative-Semiring :
    ℕ → type-Commutative-Semiring → type-Commutative-Semiring
  mul-nat-scalar-Commutative-Semiring = {!!}

  ap-mul-nat-scalar-Commutative-Semiring :
    {m n : ℕ} {x y : type-Commutative-Semiring} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Commutative-Semiring m x ＝
    mul-nat-scalar-Commutative-Semiring n y
  ap-mul-nat-scalar-Commutative-Semiring = {!!}

  left-zero-law-mul-nat-scalar-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-nat-scalar-Commutative-Semiring 0 x ＝ zero-Commutative-Semiring
  left-zero-law-mul-nat-scalar-Commutative-Semiring = {!!}

  right-zero-law-mul-nat-scalar-Commutative-Semiring :
    (n : ℕ) →
    mul-nat-scalar-Commutative-Semiring n zero-Commutative-Semiring ＝
    zero-Commutative-Semiring
  right-zero-law-mul-nat-scalar-Commutative-Semiring = {!!}

  left-unit-law-mul-nat-scalar-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-nat-scalar-Commutative-Semiring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Commutative-Semiring = {!!}

  left-nat-scalar-law-mul-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring) →
    mul-Commutative-Semiring (mul-nat-scalar-Commutative-Semiring n x) y ＝
    mul-nat-scalar-Commutative-Semiring n (mul-Commutative-Semiring x y)
  left-nat-scalar-law-mul-Commutative-Semiring = {!!}

  right-nat-scalar-law-mul-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring) →
    mul-Commutative-Semiring x (mul-nat-scalar-Commutative-Semiring n y) ＝
    mul-nat-scalar-Commutative-Semiring n (mul-Commutative-Semiring x y)
  right-nat-scalar-law-mul-Commutative-Semiring = {!!}

  left-distributive-mul-nat-scalar-add-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring) →
    mul-nat-scalar-Commutative-Semiring n (add-Commutative-Semiring x y) ＝
    add-Commutative-Semiring
      ( mul-nat-scalar-Commutative-Semiring n x)
      ( mul-nat-scalar-Commutative-Semiring n y)
  left-distributive-mul-nat-scalar-add-Commutative-Semiring = {!!}

  right-distributive-mul-nat-scalar-add-Commutative-Semiring :
    (m n : ℕ) (x : type-Commutative-Semiring) →
    mul-nat-scalar-Commutative-Semiring (m +ℕ n) x ＝
    add-Commutative-Semiring
      ( mul-nat-scalar-Commutative-Semiring m x)
      ( mul-nat-scalar-Commutative-Semiring n x)
  right-distributive-mul-nat-scalar-add-Commutative-Semiring = {!!}
```
