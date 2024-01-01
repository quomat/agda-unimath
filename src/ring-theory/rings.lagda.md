# Rings

```agda
module ring-theory.rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.negation
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

open import ring-theory.semirings
```

</details>

## Idea

The concept of ring vastly generalizes the arithmetical structure on the
integers. A ring consists of a set equipped with addition and multiplication,
where the addition operation gives the ring the structure of an abelian group,
and the multiplication is associative, unital, and distributive over addition.

## Definitions

### Rings

```agda
has-mul-Ab : {l1 : Level} (A : Ab l1) → UU l1
has-mul-Ab = {!!}

Ring : (l1 : Level) → UU (lsuc l1)
Ring = {!!}

module _
  {l : Level} (R : Ring l)
  where

  ab-Ring : Ab l
  ab-Ring = {!!}

  group-Ring : Group l
  group-Ring = {!!}

  additive-commutative-monoid-Ring : Commutative-Monoid l
  additive-commutative-monoid-Ring = {!!}

  additive-monoid-Ring : Monoid l
  additive-monoid-Ring = {!!}

  additive-semigroup-Ring : Semigroup l
  additive-semigroup-Ring = {!!}

  set-Ring : Set l
  set-Ring = {!!}

  type-Ring : UU l
  type-Ring = {!!}

  is-set-type-Ring : is-set type-Ring
  is-set-type-Ring = {!!}
```

### Addition in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-associative-add-Ring : has-associative-mul-Set (set-Ring R)
  has-associative-add-Ring = {!!}

  add-Ring : type-Ring R → type-Ring R → type-Ring R
  add-Ring = {!!}

  add-Ring' : type-Ring R → type-Ring R → type-Ring R
  add-Ring' = {!!}

  ap-add-Ring :
    {x y x' y' : type-Ring R} →
    Id x x' → Id y y' → Id (add-Ring x y) (add-Ring x' y')
  ap-add-Ring = {!!}

  associative-add-Ring :
    (x y z : type-Ring R) →
    Id (add-Ring (add-Ring x y) z) (add-Ring x (add-Ring y z))
  associative-add-Ring = {!!}

  is-group-additive-semigroup-Ring : is-group (additive-semigroup-Ring R)
  is-group-additive-semigroup-Ring = {!!}

  commutative-add-Ring : (x y : type-Ring R) → Id (add-Ring x y) (add-Ring y x)
  commutative-add-Ring = {!!}

  interchange-add-add-Ring :
    (x y x' y' : type-Ring R) →
    ( add-Ring (add-Ring x y) (add-Ring x' y')) ＝
    ( add-Ring (add-Ring x x') (add-Ring y y'))
  interchange-add-add-Ring = {!!}

  right-swap-add-Ring :
    (x y z : type-Ring R) →
    add-Ring (add-Ring x y) z ＝ add-Ring (add-Ring x z) y
  right-swap-add-Ring = {!!}

  left-swap-add-Ring :
    (x y z : type-Ring R) →
    add-Ring x (add-Ring y z) ＝ add-Ring y (add-Ring x z)
  left-swap-add-Ring = {!!}
```

### Addition in a ring is a binary equivalence

#### Addition on the left is an equivalence

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-subtraction-Ring : type-Ring R → type-Ring R → type-Ring R
  left-subtraction-Ring = {!!}

  ap-left-subtraction-Ring :
    {x x' y y' : type-Ring R} → x ＝ x' → y ＝ y' →
    left-subtraction-Ring x y ＝ left-subtraction-Ring x' y'
  ap-left-subtraction-Ring = {!!}

  is-section-left-subtraction-Ring :
    (x : type-Ring R) → (add-Ring R x ∘ left-subtraction-Ring x) ~ id
  is-section-left-subtraction-Ring = {!!}

  is-retraction-left-subtraction-Ring :
    (x : type-Ring R) → (left-subtraction-Ring x ∘ add-Ring R x) ~ id
  is-retraction-left-subtraction-Ring = {!!}

  is-equiv-add-Ring : (x : type-Ring R) → is-equiv (add-Ring R x)
  is-equiv-add-Ring = {!!}

  equiv-add-Ring : type-Ring R → (type-Ring R ≃ type-Ring R)
  equiv-add-Ring = {!!}
```

#### Addition on the right is an equivalence

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-subtraction-Ring : type-Ring R → type-Ring R → type-Ring R
  right-subtraction-Ring = {!!}

  ap-right-subtraction-Ring :
    {x x' y y' : type-Ring R} → x ＝ x' → y ＝ y' →
    right-subtraction-Ring x y ＝ right-subtraction-Ring x' y'
  ap-right-subtraction-Ring = {!!}

  is-section-right-subtraction-Ring :
    (x : type-Ring R) →
    (add-Ring' R x ∘ (λ y → right-subtraction-Ring y x)) ~ id
  is-section-right-subtraction-Ring = {!!}

  is-retraction-right-subtraction-Ring :
    (x : type-Ring R) →
    ((λ y → right-subtraction-Ring y x) ∘ add-Ring' R x) ~ id
  is-retraction-right-subtraction-Ring = {!!}

  is-equiv-add-Ring' : (x : type-Ring R) → is-equiv (add-Ring' R x)
  is-equiv-add-Ring' = {!!}

  equiv-add-Ring' : type-Ring R → (type-Ring R ≃ type-Ring R)
  equiv-add-Ring' = {!!}
```

#### Addition in a ring is a binary equivalence

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-binary-equiv-add-Ring : is-binary-equiv (add-Ring R)
  is-binary-equiv-add-Ring = {!!}
```

#### Addition in a ring is a binary embedding

```agda
  is-binary-emb-add-Ring : is-binary-emb (add-Ring R)
  is-binary-emb-add-Ring = {!!}

  is-emb-add-Ring : (x : type-Ring R) → is-emb (add-Ring R x)
  is-emb-add-Ring = {!!}

  is-emb-add-Ring' : (x : type-Ring R) → is-emb (add-Ring' R x)
  is-emb-add-Ring' = {!!}
```

#### Addition in a ring is pointwise injective from both sides

```agda
  is-injective-add-Ring : (x : type-Ring R) → is-injective (add-Ring R x)
  is-injective-add-Ring = {!!}

  is-injective-add-Ring' : (x : type-Ring R) → is-injective (add-Ring' R x)
  is-injective-add-Ring' = {!!}
```

### The zero element of a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-zero-Ring : is-unital (add-Ring R)
  has-zero-Ring = {!!}

  zero-Ring : type-Ring R
  zero-Ring = {!!}

  is-zero-Ring : type-Ring R → UU l
  is-zero-Ring = {!!}

  is-nonzero-Ring : type-Ring R → UU l
  is-nonzero-Ring = {!!}

  is-zero-ring-Prop : type-Ring R → Prop l
  is-zero-ring-Prop = {!!}

  is-nonzero-ring-Prop : type-Ring R → Prop l
  is-nonzero-ring-Prop = {!!}

  left-unit-law-add-Ring : (x : type-Ring R) → Id (add-Ring R zero-Ring x) x
  left-unit-law-add-Ring = {!!}

  right-unit-law-add-Ring : (x : type-Ring R) → Id (add-Ring R x zero-Ring) x
  right-unit-law-add-Ring = {!!}
```

### Additive inverses in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-negatives-Ring : is-group' (additive-semigroup-Ring R) (has-zero-Ring R)
  has-negatives-Ring = {!!}

  neg-Ring : type-Ring R → type-Ring R
  neg-Ring = {!!}

  left-inverse-law-add-Ring :
    (x : type-Ring R) → Id (add-Ring R (neg-Ring x) x) (zero-Ring R)
  left-inverse-law-add-Ring = {!!}

  right-inverse-law-add-Ring :
    (x : type-Ring R) → Id (add-Ring R x (neg-Ring x)) (zero-Ring R)
  right-inverse-law-add-Ring = {!!}

  neg-neg-Ring : (x : type-Ring R) → neg-Ring (neg-Ring x) ＝ x
  neg-neg-Ring = {!!}

  distributive-neg-add-Ring :
    (x y : type-Ring R) →
    neg-Ring (add-Ring R x y) ＝ add-Ring R (neg-Ring x) (neg-Ring y)
  distributive-neg-add-Ring = {!!}

  neg-zero-Ring : neg-Ring (zero-Ring R) ＝ (zero-Ring R)
  neg-zero-Ring = {!!}

  add-and-subtract-Ring :
    (x y z : type-Ring R) →
    add-Ring R (add-Ring R x y) (add-Ring R (neg-Ring y) z) ＝ add-Ring R x z
  add-and-subtract-Ring = {!!}

  eq-is-unit-left-div-Ring :
    {x y : type-Ring R} →
    (is-zero-Ring R (add-Ring R (neg-Ring x) y)) → x ＝ y
  eq-is-unit-left-div-Ring = {!!}

  is-unit-left-div-eq-Ring :
    {x y : type-Ring R} →
    x ＝ y → (is-zero-Ring R (add-Ring R (neg-Ring x) y))
  is-unit-left-div-eq-Ring = {!!}
```

### Multiplication in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-associative-mul-Ring : has-associative-mul-Set (set-Ring R)
  has-associative-mul-Ring = {!!}

  mul-Ring : type-Ring R → type-Ring R → type-Ring R
  mul-Ring = {!!}

  mul-Ring' : type-Ring R → type-Ring R → type-Ring R
  mul-Ring' = {!!}

  ap-mul-Ring :
    {x x' y y' : type-Ring R} (p : Id x x') (q : Id y y') →
    Id (mul-Ring x y) (mul-Ring x' y')
  ap-mul-Ring = {!!}

  associative-mul-Ring :
    (x y z : type-Ring R) →
    Id (mul-Ring (mul-Ring x y) z) (mul-Ring x (mul-Ring y z))
  associative-mul-Ring = {!!}

  multiplicative-semigroup-Ring : Semigroup l
  multiplicative-semigroup-Ring = {!!}

  left-distributive-mul-add-Ring :
    (x y z : type-Ring R) →
    mul-Ring x (add-Ring R y z) ＝ add-Ring R (mul-Ring x y) (mul-Ring x z)
  left-distributive-mul-add-Ring = {!!}

  right-distributive-mul-add-Ring :
    (x y z : type-Ring R) →
    mul-Ring (add-Ring R x y) z ＝ add-Ring R (mul-Ring x z) (mul-Ring y z)
  right-distributive-mul-add-Ring = {!!}
```

### Multiplicative units in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-unital-Ring : is-unital (mul-Ring R)
  is-unital-Ring = {!!}

  multiplicative-monoid-Ring : Monoid l
  multiplicative-monoid-Ring = {!!}

  one-Ring : type-Ring R
  one-Ring = {!!}

  left-unit-law-mul-Ring : (x : type-Ring R) → Id (mul-Ring R one-Ring x) x
  left-unit-law-mul-Ring = {!!}

  right-unit-law-mul-Ring : (x : type-Ring R) → Id (mul-Ring R x one-Ring) x
  right-unit-law-mul-Ring = {!!}
```

### The zero laws for multiplication of a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-zero-law-mul-Ring :
    (x : type-Ring R) → Id (mul-Ring R (zero-Ring R) x) (zero-Ring R)
  left-zero-law-mul-Ring = {!!}

  right-zero-law-mul-Ring :
    (x : type-Ring R) → Id (mul-Ring R x (zero-Ring R)) (zero-Ring R)
  right-zero-law-mul-Ring = {!!}
```

### Rings are semirings

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-mul-Ring :
    has-mul-Commutative-Monoid (additive-commutative-monoid-Ring R)
  has-mul-Ring = {!!}

  zero-laws-mul-Ring :
    zero-laws-Commutative-Monoid
      ( additive-commutative-monoid-Ring R)
      ( has-mul-Ring)
  zero-laws-mul-Ring = {!!}

  semiring-Ring : Semiring l
  semiring-Ring = {!!}
```

### Computing multiplication with minus one in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-one-Ring : type-Ring R
  neg-one-Ring = {!!}

  mul-neg-one-Ring :
    (x : type-Ring R) → mul-Ring R neg-one-Ring x ＝ neg-Ring R x
  mul-neg-one-Ring = {!!}

  mul-neg-one-Ring' :
    (x : type-Ring R) → mul-Ring R x neg-one-Ring ＝ neg-Ring R x
  mul-neg-one-Ring' = {!!}

  is-involution-mul-neg-one-Ring :
    is-involution (mul-Ring R neg-one-Ring)
  is-involution-mul-neg-one-Ring = {!!}

  is-involution-mul-neg-one-Ring' :
    is-involution (mul-Ring' R neg-one-Ring)
  is-involution-mul-neg-one-Ring' = {!!}
```

### Left and right negative laws for multiplication

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-negative-law-mul-Ring :
    (x y : type-Ring R) →
    mul-Ring R (neg-Ring R x) y ＝ neg-Ring R (mul-Ring R x y)
  left-negative-law-mul-Ring = {!!}

  right-negative-law-mul-Ring :
    (x y : type-Ring R) →
    mul-Ring R x (neg-Ring R y) ＝ neg-Ring R (mul-Ring R x y)
  right-negative-law-mul-Ring = {!!}

  mul-neg-Ring :
    (x y : type-Ring R) →
    mul-Ring R (neg-Ring R x) (neg-Ring R y) ＝ mul-Ring R x y
  mul-neg-Ring = {!!}
```

### Distributivity of multiplication over subtraction

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-left-subtraction-Ring :
    (x y z : type-Ring R) →
    mul-Ring R x (left-subtraction-Ring R y z) ＝
    left-subtraction-Ring R (mul-Ring R x y) (mul-Ring R x z)
  left-distributive-mul-left-subtraction-Ring = {!!}

  right-distributive-mul-left-subtraction-Ring :
    (x y z : type-Ring R) →
    mul-Ring R (left-subtraction-Ring R x y) z ＝
    left-subtraction-Ring R (mul-Ring R x z) (mul-Ring R y z)
  right-distributive-mul-left-subtraction-Ring = {!!}

  left-distributive-mul-right-subtraction-Ring :
    (x y z : type-Ring R) →
    mul-Ring R x (right-subtraction-Ring R y z) ＝
    right-subtraction-Ring R (mul-Ring R x y) (mul-Ring R x z)
  left-distributive-mul-right-subtraction-Ring = {!!}

  right-distributive-mul-right-subtraction-Ring :
    (x y z : type-Ring R) →
    mul-Ring R (right-subtraction-Ring R x y) z ＝
    right-subtraction-Ring R (mul-Ring R x z) (mul-Ring R y z)
  right-distributive-mul-right-subtraction-Ring = {!!}
```

### Bidistributivity of multiplication over addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  bidistributive-mul-add-Ring :
    (u v x y : type-Ring R) →
    mul-Ring R (add-Ring R u v) (add-Ring R x y) ＝
    add-Ring R
      ( add-Ring R (mul-Ring R u x) (mul-Ring R u y))
      ( add-Ring R (mul-Ring R v x) (mul-Ring R v y))
  bidistributive-mul-add-Ring = {!!}
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {l : Level} (R : Ring l)
  where

  mul-nat-scalar-Ring : ℕ → type-Ring R → type-Ring R
  mul-nat-scalar-Ring = {!!}

  ap-mul-nat-scalar-Ring :
    {m n : ℕ} {x y : type-Ring R} →
    (m ＝ n) → (x ＝ y) → mul-nat-scalar-Ring m x ＝ mul-nat-scalar-Ring n y
  ap-mul-nat-scalar-Ring = {!!}

  left-zero-law-mul-nat-scalar-Ring :
    (x : type-Ring R) → mul-nat-scalar-Ring 0 x ＝ zero-Ring R
  left-zero-law-mul-nat-scalar-Ring = {!!}

  right-zero-law-mul-nat-scalar-Ring :
    (n : ℕ) → mul-nat-scalar-Ring n (zero-Ring R) ＝ zero-Ring R
  right-zero-law-mul-nat-scalar-Ring = {!!}

  left-unit-law-mul-nat-scalar-Ring :
    (x : type-Ring R) → mul-nat-scalar-Ring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Ring = {!!}

  left-nat-scalar-law-mul-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-Ring R (mul-nat-scalar-Ring n x) y ＝
    mul-nat-scalar-Ring n (mul-Ring R x y)
  left-nat-scalar-law-mul-Ring = {!!}

  right-nat-scalar-law-mul-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-Ring R x (mul-nat-scalar-Ring n y) ＝
    mul-nat-scalar-Ring n (mul-Ring R x y)
  right-nat-scalar-law-mul-Ring = {!!}

  left-distributive-mul-nat-scalar-add-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-nat-scalar-Ring n (add-Ring R x y) ＝
    add-Ring R (mul-nat-scalar-Ring n x) (mul-nat-scalar-Ring n y)
  left-distributive-mul-nat-scalar-add-Ring = {!!}

  right-distributive-mul-nat-scalar-add-Ring :
    (m n : ℕ) (x : type-Ring R) →
    mul-nat-scalar-Ring (m +ℕ n) x ＝
    add-Ring R (mul-nat-scalar-Ring m x) (mul-nat-scalar-Ring n x)
  right-distributive-mul-nat-scalar-add-Ring = {!!}
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-list-Ring : list (type-Ring R) → type-Ring R
  add-list-Ring = {!!}

  preserves-concat-add-list-Ring :
    (l1 l2 : list (type-Ring R)) →
    Id
      ( add-list-Ring (concat-list l1 l2))
      ( add-Ring R (add-list-Ring l1) (add-list-Ring l2))
  preserves-concat-add-list-Ring = {!!}
```

### Equip a type with a structure of a ring

```agda
structure-ring :
  {l1 : Level} → UU l1 → UU l1
structure-ring = {!!}

compute-structure-ring :
  {l1 : Level} → (X : UU l1) → structure-ring X → Ring l1
compute-structure-ring = {!!}
pr2 (compute-structure-ring X (p , q)) = {!!}
```
