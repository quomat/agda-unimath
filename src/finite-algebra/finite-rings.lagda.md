# Finite rings

```agda
module finite-algebra.finite-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-algebra.finite-abelian-groups
open import finite-algebra.finite-groups
open import finite-algebra.finite-monoids

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import lists.concatenation-lists
open import lists.lists

open import ring-theory.rings
open import ring-theory.semirings

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **finite ring** is a ring where the underlying type is finite.

## Definitions

### Finite Rings

```agda
has-mul-Ab-𝔽 : {l1 : Level} (A : Ab-𝔽 l1) → UU l1
has-mul-Ab-𝔽 = {!!}

Ring-𝔽 : (l1 : Level) → UU (lsuc l1)
Ring-𝔽 = {!!}

compute-ring-𝔽 :
  {l : Level} → (R : Ring l) → is-finite (type-Ring R) → Ring-𝔽 l
compute-ring-𝔽 = {!!}
pr2 (compute-ring-𝔽 R f) = {!!}

module _
  {l : Level} (R : Ring-𝔽 l)
  where

  finite-ab-Ring-𝔽 : Ab-𝔽 l
  finite-ab-Ring-𝔽 = {!!}

  ab-Ring-𝔽 : Ab l
  ab-Ring-𝔽 = {!!}

  ring-Ring-𝔽 : Ring l
  ring-Ring-𝔽 = {!!}

  finite-type-Ring-𝔽 : 𝔽 l
  finite-type-Ring-𝔽 = {!!}

  type-Ring-𝔽 : UU l
  type-Ring-𝔽 = {!!}

  is-finite-type-Ring-𝔽 : is-finite type-Ring-𝔽
  is-finite-type-Ring-𝔽 = {!!}

  finite-group-Ring-𝔽 : Group-𝔽 l
  finite-group-Ring-𝔽 = {!!}

  group-Ring-𝔽 : Group l
  group-Ring-𝔽 = {!!}

  additive-commutative-monoid-Ring-𝔽 : Commutative-Monoid l
  additive-commutative-monoid-Ring-𝔽 = {!!}

  additive-monoid-Ring-𝔽 : Monoid l
  additive-monoid-Ring-𝔽 = {!!}

  additive-semigroup-Ring-𝔽 : Semigroup l
  additive-semigroup-Ring-𝔽 = {!!}

  set-Ring-𝔽 : Set l
  set-Ring-𝔽 = {!!}

  is-set-type-Ring-𝔽 : is-set type-Ring-𝔽
  is-set-type-Ring-𝔽 = {!!}
```

### Addition in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-associative-add-Ring-𝔽 : has-associative-mul-Set (set-Ring-𝔽 R)
  has-associative-add-Ring-𝔽 = {!!}

  add-Ring-𝔽 : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  add-Ring-𝔽 = {!!}

  add-Ring-𝔽' : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  add-Ring-𝔽' = {!!}

  ap-add-Ring-𝔽 :
    {x y x' y' : type-Ring-𝔽 R} →
    Id x x' → Id y y' → Id (add-Ring-𝔽 x y) (add-Ring-𝔽 x' y')
  ap-add-Ring-𝔽 = {!!}

  associative-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    Id (add-Ring-𝔽 (add-Ring-𝔽 x y) z) (add-Ring-𝔽 x (add-Ring-𝔽 y z))
  associative-add-Ring-𝔽 = {!!}

  is-group-additive-semigroup-Ring-𝔽 : is-group (additive-semigroup-Ring-𝔽 R)
  is-group-additive-semigroup-Ring-𝔽 = {!!}

  commutative-add-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) → Id (add-Ring-𝔽 x y) (add-Ring-𝔽 y x)
  commutative-add-Ring-𝔽 = {!!}

  interchange-add-add-Ring-𝔽 :
    (x y x' y' : type-Ring-𝔽 R) →
    ( add-Ring-𝔽 (add-Ring-𝔽 x y) (add-Ring-𝔽 x' y')) ＝
    ( add-Ring-𝔽 (add-Ring-𝔽 x x') (add-Ring-𝔽 y y'))
  interchange-add-add-Ring-𝔽 = {!!}

  right-swap-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    add-Ring-𝔽 (add-Ring-𝔽 x y) z ＝ add-Ring-𝔽 (add-Ring-𝔽 x z) y
  right-swap-add-Ring-𝔽 = {!!}

  left-swap-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    add-Ring-𝔽 x (add-Ring-𝔽 y z) ＝ add-Ring-𝔽 y (add-Ring-𝔽 x z)
  left-swap-add-Ring-𝔽 = {!!}

  is-equiv-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → is-equiv (add-Ring-𝔽 x)
  is-equiv-add-Ring-𝔽 = {!!}

  is-equiv-add-Ring-𝔽' : (x : type-Ring-𝔽 R) → is-equiv (add-Ring-𝔽' x)
  is-equiv-add-Ring-𝔽' = {!!}

  is-binary-equiv-add-Ring-𝔽 : is-binary-equiv add-Ring-𝔽
  is-binary-equiv-add-Ring-𝔽 = {!!}

  is-binary-emb-add-Ring-𝔽 : is-binary-emb add-Ring-𝔽
  is-binary-emb-add-Ring-𝔽 = {!!}

  is-emb-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → is-emb (add-Ring-𝔽 x)
  is-emb-add-Ring-𝔽 = {!!}

  is-emb-add-Ring-𝔽' : (x : type-Ring-𝔽 R) → is-emb (add-Ring-𝔽' x)
  is-emb-add-Ring-𝔽' = {!!}

  is-injective-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → is-injective (add-Ring-𝔽 x)
  is-injective-add-Ring-𝔽 = {!!}

  is-injective-add-Ring-𝔽' : (x : type-Ring-𝔽 R) → is-injective (add-Ring-𝔽' x)
  is-injective-add-Ring-𝔽' = {!!}
```

### The zero element of a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-zero-Ring-𝔽 : is-unital (add-Ring-𝔽 R)
  has-zero-Ring-𝔽 = {!!}

  zero-Ring-𝔽 : type-Ring-𝔽 R
  zero-Ring-𝔽 = {!!}

  is-zero-Ring-𝔽 : type-Ring-𝔽 R → UU l
  is-zero-Ring-𝔽 = {!!}

  is-nonzero-Ring-𝔽 : type-Ring-𝔽 R → UU l
  is-nonzero-Ring-𝔽 = {!!}

  is-zero-finite-ring-Prop : type-Ring-𝔽 R → Prop l
  is-zero-finite-ring-Prop = {!!}

  is-nonzero-finite-ring-Prop : type-Ring-𝔽 R → Prop l
  is-nonzero-finite-ring-Prop = {!!}

  left-unit-law-add-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R zero-Ring-𝔽 x) x
  left-unit-law-add-Ring-𝔽 = {!!}

  right-unit-law-add-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R x zero-Ring-𝔽) x
  right-unit-law-add-Ring-𝔽 = {!!}
```

### Additive inverses in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-negatives-Ring-𝔽 :
    is-group' (additive-semigroup-Ring-𝔽 R) (has-zero-Ring-𝔽 R)
  has-negatives-Ring-𝔽 = {!!}

  neg-Ring-𝔽 : type-Ring-𝔽 R → type-Ring-𝔽 R
  neg-Ring-𝔽 = {!!}

  left-inverse-law-add-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R (neg-Ring-𝔽 x) x) (zero-Ring-𝔽 R)
  left-inverse-law-add-Ring-𝔽 = {!!}

  right-inverse-law-add-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R x (neg-Ring-𝔽 x)) (zero-Ring-𝔽 R)
  right-inverse-law-add-Ring-𝔽 = {!!}

  neg-neg-Ring-𝔽 : (x : type-Ring-𝔽 R) → neg-Ring-𝔽 (neg-Ring-𝔽 x) ＝ x
  neg-neg-Ring-𝔽 = {!!}

  distributive-neg-add-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    neg-Ring-𝔽 (add-Ring-𝔽 R x y) ＝ add-Ring-𝔽 R (neg-Ring-𝔽 x) (neg-Ring-𝔽 y)
  distributive-neg-add-Ring-𝔽 = {!!}
```

### Multiplication in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-associative-mul-Ring-𝔽 : has-associative-mul-Set (set-Ring-𝔽 R)
  has-associative-mul-Ring-𝔽 = {!!}

  mul-Ring-𝔽 : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  mul-Ring-𝔽 = {!!}

  mul-Ring-𝔽' : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  mul-Ring-𝔽' = {!!}

  ap-mul-Ring-𝔽 :
    {x x' y y' : type-Ring-𝔽 R} (p : Id x x') (q : Id y y') →
    Id (mul-Ring-𝔽 x y) (mul-Ring-𝔽 x' y')
  ap-mul-Ring-𝔽 = {!!}

  associative-mul-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    Id (mul-Ring-𝔽 (mul-Ring-𝔽 x y) z) (mul-Ring-𝔽 x (mul-Ring-𝔽 y z))
  associative-mul-Ring-𝔽 = {!!}

  multiplicative-semigroup-Ring-𝔽 : Semigroup l
  multiplicative-semigroup-Ring-𝔽 = {!!}

  left-distributive-mul-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    mul-Ring-𝔽 x (add-Ring-𝔽 R y z) ＝
    add-Ring-𝔽 R (mul-Ring-𝔽 x y) (mul-Ring-𝔽 x z)
  left-distributive-mul-add-Ring-𝔽 = {!!}

  right-distributive-mul-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    mul-Ring-𝔽 (add-Ring-𝔽 R x y) z ＝
    add-Ring-𝔽 R (mul-Ring-𝔽 x z) (mul-Ring-𝔽 y z)
  right-distributive-mul-add-Ring-𝔽 = {!!}
```

### Multiplicative units in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  is-unital-Ring-𝔽 : is-unital (mul-Ring-𝔽 R)
  is-unital-Ring-𝔽 = {!!}

  multiplicative-monoid-Ring-𝔽 : Monoid l
  multiplicative-monoid-Ring-𝔽 = {!!}

  one-Ring-𝔽 : type-Ring-𝔽 R
  one-Ring-𝔽 = {!!}

  left-unit-law-mul-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R one-Ring-𝔽 x) x
  left-unit-law-mul-Ring-𝔽 = {!!}

  right-unit-law-mul-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R x one-Ring-𝔽) x
  right-unit-law-mul-Ring-𝔽 = {!!}
```

### The zero laws for multiplication of a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  left-zero-law-mul-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R (zero-Ring-𝔽 R) x) (zero-Ring-𝔽 R)
  left-zero-law-mul-Ring-𝔽 = {!!}

  right-zero-law-mul-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R x (zero-Ring-𝔽 R)) (zero-Ring-𝔽 R)
  right-zero-law-mul-Ring-𝔽 = {!!}
```

### Rings are semirings

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-mul-Ring-𝔽 :
    has-mul-Commutative-Monoid (additive-commutative-monoid-Ring-𝔽 R)
  has-mul-Ring-𝔽 = {!!}

  zero-laws-mul-Ring-𝔽 :
    zero-laws-Commutative-Monoid
      ( additive-commutative-monoid-Ring-𝔽 R)
      ( has-mul-Ring-𝔽)
  zero-laws-mul-Ring-𝔽 = {!!}

  semiring-Ring-𝔽 : Semiring l
  semiring-Ring-𝔽 = {!!}
```

### Computing multiplication with minus one in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  neg-one-Ring-𝔽 : type-Ring-𝔽 R
  neg-one-Ring-𝔽 = {!!}

  mul-neg-one-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → mul-Ring-𝔽 R neg-one-Ring-𝔽 x ＝ neg-Ring-𝔽 R x
  mul-neg-one-Ring-𝔽 = {!!}

  mul-neg-one-Ring-𝔽' :
    (x : type-Ring-𝔽 R) → mul-Ring-𝔽 R x neg-one-Ring-𝔽 ＝ neg-Ring-𝔽 R x
  mul-neg-one-Ring-𝔽' = {!!}

  is-involution-mul-neg-one-Ring-𝔽 :
    is-involution (mul-Ring-𝔽 R neg-one-Ring-𝔽)
  is-involution-mul-neg-one-Ring-𝔽 = {!!}

  is-involution-mul-neg-one-Ring-𝔽' :
    is-involution (mul-Ring-𝔽' R neg-one-Ring-𝔽)
  is-involution-mul-neg-one-Ring-𝔽' = {!!}
```

### Left and right negative laws for multiplication

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  left-negative-law-mul-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R (neg-Ring-𝔽 R x) y ＝ neg-Ring-𝔽 R (mul-Ring-𝔽 R x y)
  left-negative-law-mul-Ring-𝔽 = {!!}

  right-negative-law-mul-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R x (neg-Ring-𝔽 R y) ＝ neg-Ring-𝔽 R (mul-Ring-𝔽 R x y)
  right-negative-law-mul-Ring-𝔽 = {!!}

  mul-neg-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R (neg-Ring-𝔽 R x) (neg-Ring-𝔽 R y) ＝ mul-Ring-𝔽 R x y
  mul-neg-Ring-𝔽 = {!!}
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  mul-nat-scalar-Ring-𝔽 : ℕ → type-Ring-𝔽 R → type-Ring-𝔽 R
  mul-nat-scalar-Ring-𝔽 = {!!}

  ap-mul-nat-scalar-Ring-𝔽 :
    {m n : ℕ} {x y : type-Ring-𝔽 R} →
    (m ＝ n) → (x ＝ y) → mul-nat-scalar-Ring-𝔽 m x ＝ mul-nat-scalar-Ring-𝔽 n y
  ap-mul-nat-scalar-Ring-𝔽 = {!!}

  left-zero-law-mul-nat-scalar-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → mul-nat-scalar-Ring-𝔽 0 x ＝ zero-Ring-𝔽 R
  left-zero-law-mul-nat-scalar-Ring-𝔽 = {!!}

  right-zero-law-mul-nat-scalar-Ring-𝔽 :
    (n : ℕ) → mul-nat-scalar-Ring-𝔽 n (zero-Ring-𝔽 R) ＝ zero-Ring-𝔽 R
  right-zero-law-mul-nat-scalar-Ring-𝔽 = {!!}

  left-unit-law-mul-nat-scalar-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → mul-nat-scalar-Ring-𝔽 1 x ＝ x
  left-unit-law-mul-nat-scalar-Ring-𝔽 = {!!}

  left-nat-scalar-law-mul-Ring-𝔽 :
    (n : ℕ) (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R (mul-nat-scalar-Ring-𝔽 n x) y ＝
    mul-nat-scalar-Ring-𝔽 n (mul-Ring-𝔽 R x y)
  left-nat-scalar-law-mul-Ring-𝔽 = {!!}

  right-nat-scalar-law-mul-Ring-𝔽 :
    (n : ℕ) (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R x (mul-nat-scalar-Ring-𝔽 n y) ＝
    mul-nat-scalar-Ring-𝔽 n (mul-Ring-𝔽 R x y)
  right-nat-scalar-law-mul-Ring-𝔽 = {!!}

  left-distributive-mul-nat-scalar-add-Ring-𝔽 :
    (n : ℕ) (x y : type-Ring-𝔽 R) →
    mul-nat-scalar-Ring-𝔽 n (add-Ring-𝔽 R x y) ＝
    add-Ring-𝔽 R (mul-nat-scalar-Ring-𝔽 n x) (mul-nat-scalar-Ring-𝔽 n y)
  left-distributive-mul-nat-scalar-add-Ring-𝔽 = {!!}

  right-distributive-mul-nat-scalar-add-Ring-𝔽 :
    (m n : ℕ) (x : type-Ring-𝔽 R) →
    mul-nat-scalar-Ring-𝔽 (m +ℕ n) x ＝
    add-Ring-𝔽 R (mul-nat-scalar-Ring-𝔽 m x) (mul-nat-scalar-Ring-𝔽 n x)
  right-distributive-mul-nat-scalar-add-Ring-𝔽 = {!!}
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  add-list-Ring-𝔽 : list (type-Ring-𝔽 R) → type-Ring-𝔽 R
  add-list-Ring-𝔽 = {!!}

  preserves-concat-add-list-Ring-𝔽 :
    (l1 l2 : list (type-Ring-𝔽 R)) →
    Id
      ( add-list-Ring-𝔽 (concat-list l1 l2))
      ( add-Ring-𝔽 R (add-list-Ring-𝔽 l1) (add-list-Ring-𝔽 l2))
  preserves-concat-add-list-Ring-𝔽 = {!!}
```

## Properties

### There is a finite number of ways to equip a finite type with a structure of ring

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-ring-𝔽 : UU l
  structure-ring-𝔽 = {!!}

  compute-structure-ring-𝔽 :
    structure-ring-𝔽 → Ring-𝔽 l
  compute-structure-ring-𝔽 = {!!}
  pr2 (compute-structure-ring-𝔽 (m , c)) = {!!}

  is-finite-structure-ring-𝔽 :
    is-finite structure-ring-𝔽
  is-finite-structure-ring-𝔽 = {!!}
```
