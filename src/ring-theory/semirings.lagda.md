# Semirings

```agda
module ring-theory.semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The concept of semiring vastly generalizes the arithmetical structure on the
natural numbers. A semiring consists of a set equipped with addition and
multiplication, where the addition operation gives the ring the structure of a
commutative monoid, and the multiplication is associative, unital, and
distributive over addition.

## Definitions

### Semirings

```agda
has-mul-Commutative-Monoid :
  {l : Level} → Commutative-Monoid l → UU l
has-mul-Commutative-Monoid = {!!}

zero-laws-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) → has-mul-Commutative-Monoid M → UU l
zero-laws-Commutative-Monoid = {!!}

Semiring : (l : Level) → UU (lsuc l)
Semiring l1 = {!!}

module _
  {l : Level} (R : Semiring l)
  where

  additive-commutative-monoid-Semiring : Commutative-Monoid l
  additive-commutative-monoid-Semiring = {!!}

  additive-monoid-Semiring : Monoid l
  additive-monoid-Semiring = {!!}

  additive-semigroup-Semiring : Semigroup l
  additive-semigroup-Semiring = {!!}

  set-Semiring : Set l
  set-Semiring = {!!}

  type-Semiring : UU l
  type-Semiring = {!!}

  is-set-type-Semiring : is-set type-Semiring
  is-set-type-Semiring = {!!}
```

### Addition in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-associative-add-Semiring : has-associative-mul-Set (set-Semiring R)
  has-associative-add-Semiring = {!!}

  add-Semiring : type-Semiring R → type-Semiring R → type-Semiring R
  add-Semiring = {!!}

  add-Semiring' : type-Semiring R → type-Semiring R → type-Semiring R
  add-Semiring' = {!!}

  ap-add-Semiring :
    {x y x' y' : type-Semiring R} →
    x ＝ x' → y ＝ y' → add-Semiring x y ＝ add-Semiring x' y'
  ap-add-Semiring = {!!}

  associative-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring (add-Semiring x y) z ＝ add-Semiring x (add-Semiring y z)
  associative-add-Semiring = {!!}

  commutative-add-Semiring :
    (x y : type-Semiring R) → add-Semiring x y ＝ add-Semiring y x
  commutative-add-Semiring = {!!}

  interchange-add-add-Semiring :
    (x y x' y' : type-Semiring R) →
    ( add-Semiring (add-Semiring x y) (add-Semiring x' y')) ＝
    ( add-Semiring (add-Semiring x x') (add-Semiring y y'))
  interchange-add-add-Semiring = {!!}

  right-swap-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring (add-Semiring x y) z ＝ add-Semiring (add-Semiring x z) y
  right-swap-add-Semiring = {!!}

  left-swap-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring x (add-Semiring y z) ＝ add-Semiring y (add-Semiring x z)
  left-swap-add-Semiring = {!!}
```

### The zero element of a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-zero-Semiring : is-unital (add-Semiring R)
  has-zero-Semiring = {!!}

  zero-Semiring : type-Semiring R
  zero-Semiring = {!!}

  is-zero-Semiring : type-Semiring R → UU l
  is-zero-Semiring x = {!!}

  is-nonzero-Semiring : type-Semiring R → UU l
  is-nonzero-Semiring x = {!!}

  is-zero-semiring-Prop : type-Semiring R → Prop l
  is-zero-semiring-Prop x = {!!}

  left-unit-law-add-Semiring :
    (x : type-Semiring R) → Id (add-Semiring R zero-Semiring x) x
  left-unit-law-add-Semiring = {!!}

  right-unit-law-add-Semiring :
    (x : type-Semiring R) → Id (add-Semiring R x zero-Semiring) x
  right-unit-law-add-Semiring = {!!}
```

### Multiplication in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-associative-mul-Semiring : has-associative-mul-Set (set-Semiring R)
  has-associative-mul-Semiring = {!!}

  mul-Semiring : type-Semiring R → type-Semiring R → type-Semiring R
  mul-Semiring = {!!}

  mul-Semiring' : type-Semiring R → type-Semiring R → type-Semiring R
  mul-Semiring' x y = {!!}

  ap-mul-Semiring :
    {x x' y y' : type-Semiring R} (p : Id x x') (q : Id y y') →
    Id (mul-Semiring x y) (mul-Semiring x' y')
  ap-mul-Semiring = {!!}

  associative-mul-Semiring :
    (x y z : type-Semiring R) →
    Id (mul-Semiring (mul-Semiring x y) z) (mul-Semiring x (mul-Semiring y z))
  associative-mul-Semiring = {!!}

  multiplicative-semigroup-Semiring : Semigroup l
  pr1 multiplicative-semigroup-Semiring = {!!}

  left-distributive-mul-add-Semiring :
    (x y z : type-Semiring R) →
    mul-Semiring x (add-Semiring R y z) ＝
    add-Semiring R (mul-Semiring x y) (mul-Semiring x z)
  left-distributive-mul-add-Semiring = {!!}

  right-distributive-mul-add-Semiring :
    (x y z : type-Semiring R) →
    mul-Semiring (add-Semiring R x y) z ＝
    add-Semiring R (mul-Semiring x z) (mul-Semiring y z)
  right-distributive-mul-add-Semiring = {!!}

  bidistributive-mul-add-Semiring :
    (u v x y : type-Semiring R) →
    mul-Semiring (add-Semiring R u v) (add-Semiring R x y) ＝
    add-Semiring R
      ( add-Semiring R (mul-Semiring u x) (mul-Semiring u y))
      ( add-Semiring R (mul-Semiring v x) (mul-Semiring v y))
  bidistributive-mul-add-Semiring = {!!}

  left-zero-law-mul-Semiring :
    (x : type-Semiring R) → mul-Semiring (zero-Semiring R) x ＝ zero-Semiring R
  left-zero-law-mul-Semiring = {!!}

  right-zero-law-mul-Semiring :
    (x : type-Semiring R) → mul-Semiring x (zero-Semiring R) ＝ zero-Semiring R
  right-zero-law-mul-Semiring = {!!}
```

### Multiplicative units in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-unital-Semiring : is-unital (mul-Semiring R)
  is-unital-Semiring = {!!}

  multiplicative-monoid-Semiring : Monoid l
  pr1 multiplicative-monoid-Semiring = {!!}

  one-Semiring : type-Semiring R
  one-Semiring = {!!}

  left-unit-law-mul-Semiring :
    (x : type-Semiring R) → Id (mul-Semiring R one-Semiring x) x
  left-unit-law-mul-Semiring = {!!}

  right-unit-law-mul-Semiring :
    (x : type-Semiring R) → Id (mul-Semiring R x one-Semiring) x
  right-unit-law-mul-Semiring = {!!}
```

### Scalar multiplication of semiring elements by natural numbers

```agda
module _
  {l : Level} (R : Semiring l)
  where

  mul-nat-scalar-Semiring : ℕ → type-Semiring R → type-Semiring R
  mul-nat-scalar-Semiring zero-ℕ x = {!!}

  ap-mul-nat-scalar-Semiring :
    {m n : ℕ} {x y : type-Semiring R} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Semiring m x ＝ mul-nat-scalar-Semiring n y
  ap-mul-nat-scalar-Semiring = {!!}

  left-zero-law-mul-nat-scalar-Semiring :
    (x : type-Semiring R) → mul-nat-scalar-Semiring 0 x ＝ zero-Semiring R
  left-zero-law-mul-nat-scalar-Semiring = {!!}

  right-zero-law-mul-nat-scalar-Semiring :
    (n : ℕ) → mul-nat-scalar-Semiring n (zero-Semiring R) ＝ zero-Semiring R
  right-zero-law-mul-nat-scalar-Semiring = {!!}

  left-unit-law-mul-nat-scalar-Semiring :
    (x : type-Semiring R) → mul-nat-scalar-Semiring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Semiring = {!!}

  left-nat-scalar-law-mul-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    mul-Semiring R (mul-nat-scalar-Semiring n x) y ＝
    mul-nat-scalar-Semiring n (mul-Semiring R x y)
  left-nat-scalar-law-mul-Semiring = {!!}
  left-nat-scalar-law-mul-Semiring (succ-ℕ n) x y = {!!}

  right-nat-scalar-law-mul-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    mul-Semiring R x (mul-nat-scalar-Semiring n y) ＝
    mul-nat-scalar-Semiring n (mul-Semiring R x y)
  right-nat-scalar-law-mul-Semiring = {!!}
  right-nat-scalar-law-mul-Semiring (succ-ℕ n) x y = {!!}

  left-distributive-mul-nat-scalar-add-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    mul-nat-scalar-Semiring n (add-Semiring R x y) ＝
    add-Semiring R (mul-nat-scalar-Semiring n x) (mul-nat-scalar-Semiring n y)
  left-distributive-mul-nat-scalar-add-Semiring = {!!}
  left-distributive-mul-nat-scalar-add-Semiring (succ-ℕ n) x y = {!!}

  right-distributive-mul-nat-scalar-add-Semiring :
    (m n : ℕ) (x : type-Semiring R) →
    mul-nat-scalar-Semiring (m +ℕ n) x ＝
    add-Semiring R (mul-nat-scalar-Semiring m x) (mul-nat-scalar-Semiring n x)
  right-distributive-mul-nat-scalar-add-Semiring = {!!}
  right-distributive-mul-nat-scalar-add-Semiring m (succ-ℕ n) x = {!!}
```
