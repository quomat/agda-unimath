# Euclidean domains

```agda
module commutative-algebra.euclidean-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.integral-domains
open import commutative-algebra.trivial-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
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

open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

A **Euclidean domain** is an
[integral domain](commutative-algebra.integral-domains.md) `R` that has a
**Euclidean valuation**, i.e., a function `v : R → ℕ` such that for every
`x y : R`, if `y` is non-zero then there are `q r : R` with `x = {!!}
`v r < v y`.

## Definition

### The condition of being a Euclidean valuation

```agda
is-euclidean-valuation :
  { l : Level} (R : Integral-Domain l) →
  ( type-Integral-Domain R → ℕ) →
  UU l
is-euclidean-valuation = {!!}
```

### The condition of being a Euclidean domain

```agda
is-euclidean-domain-Integral-Domain :
  { l : Level} (R : Integral-Domain l) → UU l
is-euclidean-domain-Integral-Domain = {!!}
```

### Euclidean domains

```agda
Euclidean-Domain : (l : Level) → UU (lsuc l)
Euclidean-Domain = {!!}

module _
  {l : Level} (R : Euclidean-Domain l)
  where

  integral-domain-Euclidean-Domain : Integral-Domain l
  integral-domain-Euclidean-Domain = {!!}

  is-euclidean-domain-Euclidean-Domain :
    is-euclidean-domain-Integral-Domain integral-domain-Euclidean-Domain
  is-euclidean-domain-Euclidean-Domain = {!!}

  commutative-ring-Euclidean-Domain : Commutative-Ring l
  commutative-ring-Euclidean-Domain = {!!}

  has-cancellation-property-Euclidean-Domain :
    cancellation-property-Commutative-Ring commutative-ring-Euclidean-Domain
  has-cancellation-property-Euclidean-Domain = {!!}

  is-nontrivial-Euclidean-Domain :
    is-nontrivial-Commutative-Ring commutative-ring-Euclidean-Domain
  is-nontrivial-Euclidean-Domain = {!!}

  ab-Euclidean-Domain : Ab l
  ab-Euclidean-Domain = {!!}

  ring-Euclidean-Domain : Ring l
  ring-Euclidean-Domain = {!!}

  set-Euclidean-Domain : Set l
  set-Euclidean-Domain = {!!}

  type-Euclidean-Domain : UU l
  type-Euclidean-Domain = {!!}

  is-set-type-Euclidean-Domain : is-set type-Euclidean-Domain
  is-set-type-Euclidean-Domain = {!!}
```

### Addition in a Euclidean domain

```agda
  has-associative-add-Euclidean-Domain :
    has-associative-mul-Set set-Euclidean-Domain
  has-associative-add-Euclidean-Domain = {!!}

  add-Euclidean-Domain :
    type-Euclidean-Domain → type-Euclidean-Domain → type-Euclidean-Domain
  add-Euclidean-Domain = {!!}

  add-Euclidean-Domain' :
    type-Euclidean-Domain → type-Euclidean-Domain → type-Euclidean-Domain
  add-Euclidean-Domain' = {!!}

  ap-add-Euclidean-Domain :
    {x x' y y' : type-Euclidean-Domain} →
    (x ＝ x') → (y ＝ y') →
    add-Euclidean-Domain x y ＝ add-Euclidean-Domain x' y'
  ap-add-Euclidean-Domain = {!!}

  associative-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( add-Euclidean-Domain (add-Euclidean-Domain x y) z) ＝
    ( add-Euclidean-Domain x (add-Euclidean-Domain y z))
  associative-add-Euclidean-Domain = {!!}

  additive-semigroup-Euclidean-Domain : Semigroup l
  additive-semigroup-Euclidean-Domain = {!!}

  is-group-additive-semigroup-Euclidean-Domain :
    is-group additive-semigroup-Euclidean-Domain
  is-group-additive-semigroup-Euclidean-Domain = {!!}

  commutative-add-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    Id (add-Euclidean-Domain x y) (add-Euclidean-Domain y x)
  commutative-add-Euclidean-Domain = {!!}

  interchange-add-add-Euclidean-Domain :
    (x y x' y' : type-Euclidean-Domain) →
    ( add-Euclidean-Domain
      ( add-Euclidean-Domain x y)
      ( add-Euclidean-Domain x' y')) ＝
    ( add-Euclidean-Domain
      ( add-Euclidean-Domain x x')
      ( add-Euclidean-Domain y y'))
  interchange-add-add-Euclidean-Domain = {!!}

  right-swap-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( add-Euclidean-Domain (add-Euclidean-Domain x y) z) ＝
    ( add-Euclidean-Domain (add-Euclidean-Domain x z) y)
  right-swap-add-Euclidean-Domain = {!!}

  left-swap-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( add-Euclidean-Domain x (add-Euclidean-Domain y z)) ＝
    ( add-Euclidean-Domain y (add-Euclidean-Domain x z))
  left-swap-add-Euclidean-Domain = {!!}

  is-equiv-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) → is-equiv (add-Euclidean-Domain x)
  is-equiv-add-Euclidean-Domain = {!!}

  is-equiv-add-Euclidean-Domain' :
    (x : type-Euclidean-Domain) → is-equiv (add-Euclidean-Domain' x)
  is-equiv-add-Euclidean-Domain' = {!!}

  is-binary-equiv-add-Euclidean-Domain : is-binary-equiv add-Euclidean-Domain
  is-binary-equiv-add-Euclidean-Domain = {!!}

  is-binary-emb-add-Euclidean-Domain : is-binary-emb add-Euclidean-Domain
  is-binary-emb-add-Euclidean-Domain = {!!}

  is-emb-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) → is-emb (add-Euclidean-Domain x)
  is-emb-add-Euclidean-Domain = {!!}

  is-emb-add-Euclidean-Domain' :
    (x : type-Euclidean-Domain) → is-emb (add-Euclidean-Domain' x)
  is-emb-add-Euclidean-Domain' = {!!}

  is-injective-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) → is-injective (add-Euclidean-Domain x)
  is-injective-add-Euclidean-Domain = {!!}

  is-injective-add-Euclidean-Domain' :
    (x : type-Euclidean-Domain) → is-injective (add-Euclidean-Domain' x)
  is-injective-add-Euclidean-Domain' = {!!}
```

### The zero element of a Euclidean domain

```agda
  has-zero-Euclidean-Domain : is-unital add-Euclidean-Domain
  has-zero-Euclidean-Domain = {!!}

  zero-Euclidean-Domain : type-Euclidean-Domain
  zero-Euclidean-Domain = {!!}

  is-zero-Euclidean-Domain : type-Euclidean-Domain → UU l
  is-zero-Euclidean-Domain = {!!}

  is-nonzero-Euclidean-Domain : type-Euclidean-Domain → UU l
  is-nonzero-Euclidean-Domain = {!!}

  is-zero-euclidean-domain-Prop : type-Euclidean-Domain → Prop l
  is-zero-euclidean-domain-Prop = {!!}

  is-nonzero-euclidean-domain-Prop : type-Euclidean-Domain → Prop l
  is-nonzero-euclidean-domain-Prop = {!!}

  left-unit-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain zero-Euclidean-Domain x ＝ x
  left-unit-law-add-Euclidean-Domain = {!!}

  right-unit-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain x zero-Euclidean-Domain ＝ x
  right-unit-law-add-Euclidean-Domain = {!!}
```

### Additive inverses in a Euclidean domain

```agda
  has-negatives-Euclidean-Domain :
    is-group' additive-semigroup-Euclidean-Domain has-zero-Euclidean-Domain
  has-negatives-Euclidean-Domain = {!!}

  neg-Euclidean-Domain : type-Euclidean-Domain → type-Euclidean-Domain
  neg-Euclidean-Domain = {!!}

  left-inverse-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain (neg-Euclidean-Domain x) x ＝ zero-Euclidean-Domain
  left-inverse-law-add-Euclidean-Domain = {!!}

  right-inverse-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain x (neg-Euclidean-Domain x) ＝ zero-Euclidean-Domain
  right-inverse-law-add-Euclidean-Domain = {!!}

  neg-neg-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    neg-Euclidean-Domain (neg-Euclidean-Domain x) ＝ x
  neg-neg-Euclidean-Domain = {!!}

  distributive-neg-add-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    neg-Euclidean-Domain (add-Euclidean-Domain x y) ＝
    add-Euclidean-Domain (neg-Euclidean-Domain x) (neg-Euclidean-Domain y)
  distributive-neg-add-Euclidean-Domain = {!!}
```

### Multiplication in a Euclidean domain

```agda
  has-associative-mul-Euclidean-Domain :
    has-associative-mul-Set set-Euclidean-Domain
  has-associative-mul-Euclidean-Domain = {!!}

  mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) → type-Euclidean-Domain
  mul-Euclidean-Domain = {!!}

  mul-Euclidean-Domain' :
    (x y : type-Euclidean-Domain) → type-Euclidean-Domain
  mul-Euclidean-Domain' = {!!}

  ap-mul-Euclidean-Domain :
    {x x' y y' : type-Euclidean-Domain} (p : Id x x') (q : Id y y') →
    Id (mul-Euclidean-Domain x y) (mul-Euclidean-Domain x' y')
  ap-mul-Euclidean-Domain = {!!}

  associative-mul-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain (mul-Euclidean-Domain x y) z ＝
    mul-Euclidean-Domain x (mul-Euclidean-Domain y z)
  associative-mul-Euclidean-Domain = {!!}

  multiplicative-semigroup-Euclidean-Domain : Semigroup l
  multiplicative-semigroup-Euclidean-Domain = {!!}

  left-distributive-mul-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( mul-Euclidean-Domain x (add-Euclidean-Domain y z)) ＝
    ( add-Euclidean-Domain
      ( mul-Euclidean-Domain x y)
      ( mul-Euclidean-Domain x z))
  left-distributive-mul-add-Euclidean-Domain = {!!}

  right-distributive-mul-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( mul-Euclidean-Domain (add-Euclidean-Domain x y) z) ＝
    ( add-Euclidean-Domain
      ( mul-Euclidean-Domain x z)
      ( mul-Euclidean-Domain y z))
  right-distributive-mul-add-Euclidean-Domain = {!!}

  commutative-mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain x y ＝ mul-Euclidean-Domain y x
  commutative-mul-Euclidean-Domain = {!!}
```

### Multiplicative units in a Euclidean domain

```agda
  is-unital-Euclidean-Domain : is-unital mul-Euclidean-Domain
  is-unital-Euclidean-Domain = {!!}

  multiplicative-monoid-Euclidean-Domain : Monoid l
  multiplicative-monoid-Euclidean-Domain = {!!}

  one-Euclidean-Domain : type-Euclidean-Domain
  one-Euclidean-Domain = {!!}

  left-unit-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain one-Euclidean-Domain x ＝ x
  left-unit-law-mul-Euclidean-Domain = {!!}

  right-unit-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain x one-Euclidean-Domain ＝ x
  right-unit-law-mul-Euclidean-Domain = {!!}

  right-swap-mul-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain (mul-Euclidean-Domain x y) z ＝
    mul-Euclidean-Domain (mul-Euclidean-Domain x z) y
  right-swap-mul-Euclidean-Domain = {!!}

  left-swap-mul-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain x (mul-Euclidean-Domain y z) ＝
    mul-Euclidean-Domain y (mul-Euclidean-Domain x z)
  left-swap-mul-Euclidean-Domain = {!!}

  interchange-mul-mul-Euclidean-Domain :
    (x y z w : type-Euclidean-Domain) →
    mul-Euclidean-Domain
      ( mul-Euclidean-Domain x y)
      ( mul-Euclidean-Domain z w) ＝
    mul-Euclidean-Domain
      ( mul-Euclidean-Domain x z)
      ( mul-Euclidean-Domain y w)
  interchange-mul-mul-Euclidean-Domain = {!!}
```

### The zero laws for multiplication of a Euclidean domain

```agda
  left-zero-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain zero-Euclidean-Domain x ＝
    zero-Euclidean-Domain
  left-zero-law-mul-Euclidean-Domain = {!!}

  right-zero-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain x zero-Euclidean-Domain ＝
    zero-Euclidean-Domain
  right-zero-law-mul-Euclidean-Domain = {!!}
```

### Euclidean domains are commutative semirings

```agda
  multiplicative-commutative-monoid-Euclidean-Domain : Commutative-Monoid l
  multiplicative-commutative-monoid-Euclidean-Domain = {!!}

  semiring-Euclidean-Domain : Semiring l
  semiring-Euclidean-Domain = {!!}

  commutative-semiring-Euclidean-Domain : Commutative-Semiring l
  commutative-semiring-Euclidean-Domain = {!!}
```

### Computing multiplication with minus one in a Euclidean domain

```agda
  neg-one-Euclidean-Domain : type-Euclidean-Domain
  neg-one-Euclidean-Domain = {!!}

  mul-neg-one-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain neg-one-Euclidean-Domain x ＝
    neg-Euclidean-Domain x
  mul-neg-one-Euclidean-Domain = {!!}

  mul-neg-one-Euclidean-Domain' :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain x neg-one-Euclidean-Domain ＝
    neg-Euclidean-Domain x
  mul-neg-one-Euclidean-Domain' = {!!}

  is-involution-mul-neg-one-Euclidean-Domain :
    is-involution (mul-Euclidean-Domain neg-one-Euclidean-Domain)
  is-involution-mul-neg-one-Euclidean-Domain = {!!}

  is-involution-mul-neg-one-Euclidean-Domain' :
    is-involution (mul-Euclidean-Domain' neg-one-Euclidean-Domain)
  is-involution-mul-neg-one-Euclidean-Domain' = {!!}
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain (neg-Euclidean-Domain x) y ＝
    neg-Euclidean-Domain (mul-Euclidean-Domain x y)
  left-negative-law-mul-Euclidean-Domain = {!!}

  right-negative-law-mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain x (neg-Euclidean-Domain y) ＝
    neg-Euclidean-Domain (mul-Euclidean-Domain x y)
  right-negative-law-mul-Euclidean-Domain = {!!}

  mul-neg-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain (neg-Euclidean-Domain x) (neg-Euclidean-Domain y) ＝
    mul-Euclidean-Domain x y
  mul-neg-Euclidean-Domain = {!!}
```

### Scalar multiplication of elements of a Euclidean domain by natural numbers

```agda
  mul-nat-scalar-Euclidean-Domain :
    ℕ → type-Euclidean-Domain → type-Euclidean-Domain
  mul-nat-scalar-Euclidean-Domain = {!!}

  ap-mul-nat-scalar-Euclidean-Domain :
    {m n : ℕ} {x y : type-Euclidean-Domain} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Euclidean-Domain m x ＝
    mul-nat-scalar-Euclidean-Domain n y
  ap-mul-nat-scalar-Euclidean-Domain = {!!}

  left-zero-law-mul-nat-scalar-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-nat-scalar-Euclidean-Domain 0 x ＝ zero-Euclidean-Domain
  left-zero-law-mul-nat-scalar-Euclidean-Domain = {!!}

  right-zero-law-mul-nat-scalar-Euclidean-Domain :
    (n : ℕ) →
    mul-nat-scalar-Euclidean-Domain n zero-Euclidean-Domain ＝
    zero-Euclidean-Domain
  right-zero-law-mul-nat-scalar-Euclidean-Domain = {!!}

  left-unit-law-mul-nat-scalar-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-nat-scalar-Euclidean-Domain 1 x ＝ x
  left-unit-law-mul-nat-scalar-Euclidean-Domain = {!!}

  left-nat-scalar-law-mul-Euclidean-Domain :
    (n : ℕ) (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain (mul-nat-scalar-Euclidean-Domain n x) y ＝
    mul-nat-scalar-Euclidean-Domain n (mul-Euclidean-Domain x y)
  left-nat-scalar-law-mul-Euclidean-Domain = {!!}

  right-nat-scalar-law-mul-Euclidean-Domain :
    (n : ℕ) (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain x (mul-nat-scalar-Euclidean-Domain n y) ＝
    mul-nat-scalar-Euclidean-Domain n (mul-Euclidean-Domain x y)
  right-nat-scalar-law-mul-Euclidean-Domain = {!!}

  left-distributive-mul-nat-scalar-add-Euclidean-Domain :
    (n : ℕ) (x y : type-Euclidean-Domain) →
    mul-nat-scalar-Euclidean-Domain n (add-Euclidean-Domain x y) ＝
    add-Euclidean-Domain
      ( mul-nat-scalar-Euclidean-Domain n x)
      ( mul-nat-scalar-Euclidean-Domain n y)
  left-distributive-mul-nat-scalar-add-Euclidean-Domain = {!!}

  right-distributive-mul-nat-scalar-add-Euclidean-Domain :
    (m n : ℕ) (x : type-Euclidean-Domain) →
    mul-nat-scalar-Euclidean-Domain (m +ℕ n) x ＝
    add-Euclidean-Domain
      ( mul-nat-scalar-Euclidean-Domain m x)
      ( mul-nat-scalar-Euclidean-Domain n x)
  right-distributive-mul-nat-scalar-add-Euclidean-Domain = {!!}
```

### Addition of a list of elements in a Euclidean domain

```agda
  add-list-Euclidean-Domain :
    list type-Euclidean-Domain → type-Euclidean-Domain
  add-list-Euclidean-Domain = {!!}

  preserves-concat-add-list-Euclidean-Domain :
    (l1 l2 : list type-Euclidean-Domain) →
    Id
      ( add-list-Euclidean-Domain (concat-list l1 l2))
      ( add-Euclidean-Domain
        ( add-list-Euclidean-Domain l1)
        ( add-list-Euclidean-Domain l2))
  preserves-concat-add-list-Euclidean-Domain = {!!}
```

### Euclidean division in a Euclidean domain

```agda
  euclidean-valuation-Euclidean-Domain :
    type-Euclidean-Domain → ℕ
  euclidean-valuation-Euclidean-Domain = {!!}

  euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( is-nonzero-Euclidean-Domain y) →
    type-Euclidean-Domain × type-Euclidean-Domain
  euclidean-division-Euclidean-Domain = {!!}

  quotient-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( is-nonzero-Euclidean-Domain y) →
    type-Euclidean-Domain
  quotient-euclidean-division-Euclidean-Domain = {!!}

  remainder-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( is-nonzero-Euclidean-Domain y) →
    type-Euclidean-Domain
  remainder-euclidean-division-Euclidean-Domain = {!!}

  equation-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( p : is-nonzero-Euclidean-Domain y) →
    ( Id
      ( x)
      ( add-Euclidean-Domain
        ( mul-Euclidean-Domain
          ( quotient-euclidean-division-Euclidean-Domain x y p)
          ( y))
        ( remainder-euclidean-division-Euclidean-Domain x y p)))
  equation-euclidean-division-Euclidean-Domain = {!!}

  remainder-condition-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( p : is-nonzero-Integral-Domain integral-domain-Euclidean-Domain y) →
    ( is-zero-Euclidean-Domain
      ( remainder-euclidean-division-Euclidean-Domain x y p)) +
    ( euclidean-valuation-Euclidean-Domain
      ( remainder-euclidean-division-Euclidean-Domain x y p) <-ℕ
    ( euclidean-valuation-Euclidean-Domain y))
  remainder-condition-euclidean-division-Euclidean-Domain = {!!}
```
