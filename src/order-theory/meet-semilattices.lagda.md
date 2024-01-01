# Meet-semilattices

```agda
module order-theory.meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.isomorphisms-semigroups
open import group-theory.semigroups

open import order-theory.greatest-lower-bounds-posets
open import order-theory.lower-bounds-posets
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A **meet-semilattice** is a poset in which every pair of elements has a greatest
binary-lower bound. Alternatively, meet-semilattices can be defined
algebraically as a set `X` equipped with a binary operation `∧ : X → X → X`
satisfying

1. Asociativity: `(x ∧ y) ∧ z ＝ x ∧ (y ∧ z)`,
2. Commutativity: `x ∧ y ＝ y ∧ x`,
3. Idempotency: `x ∧ x ＝ x`.

We will follow the algebraic approach for our principal definition of
meet-semilattices, since it requires only one universe level. This is necessary
in order to consider the [large category](category-theory.large-categories.md)
of meet-semilattices.

## Definitions

### The predicate on semigroups of being a meet-semilattice

```agda
module _
  {l : Level} (X : Semigroup l)
  where

  is-meet-semilattice-prop-Semigroup : Prop l
  is-meet-semilattice-prop-Semigroup = {!!}

  is-meet-semilattice-Semigroup : UU l
  is-meet-semilattice-Semigroup = {!!}

  is-prop-is-meet-semilattice-Semigroup :
    is-prop is-meet-semilattice-Semigroup
  is-prop-is-meet-semilattice-Semigroup = {!!}
```

### The algebraic definition of meet-semilattices

```agda
Meet-Semilattice : (l : Level) → UU (lsuc l)
Meet-Semilattice l = {!!}

module _
  {l : Level} (X : Meet-Semilattice l)
  where

  semigroup-Meet-Semilattice : Semigroup l
  semigroup-Meet-Semilattice = {!!}

  set-Meet-Semilattice : Set l
  set-Meet-Semilattice = {!!}

  type-Meet-Semilattice : UU l
  type-Meet-Semilattice = {!!}

  is-set-type-Meet-Semilattice : is-set type-Meet-Semilattice
  is-set-type-Meet-Semilattice = {!!}

  meet-Meet-Semilattice : (x y : type-Meet-Semilattice) → type-Meet-Semilattice
  meet-Meet-Semilattice = {!!}

  meet-Meet-Semilattice' : (x y : type-Meet-Semilattice) → type-Meet-Semilattice
  meet-Meet-Semilattice' x y = {!!}

  private
    _∧_ = {!!}

  associative-meet-Meet-Semilattice :
    (x y z : type-Meet-Semilattice) → ((x ∧ y) ∧ z) ＝ (x ∧ (y ∧ z))
  associative-meet-Meet-Semilattice = {!!}

  is-meet-semilattice-Meet-Semilattice :
    is-meet-semilattice-Semigroup semigroup-Meet-Semilattice
  is-meet-semilattice-Meet-Semilattice = {!!}

  commutative-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → (x ∧ y) ＝ (y ∧ x)
  commutative-meet-Meet-Semilattice = {!!}

  idempotent-meet-Meet-Semilattice :
    (x : type-Meet-Semilattice) → (x ∧ x) ＝ x
  idempotent-meet-Meet-Semilattice = {!!}

  leq-Meet-Semilattice-Prop :
    (x y : type-Meet-Semilattice) → Prop l
  leq-Meet-Semilattice-Prop = {!!}

  leq-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → UU l
  leq-Meet-Semilattice = {!!}

  is-prop-leq-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → is-prop (leq-Meet-Semilattice x y)
  is-prop-leq-Meet-Semilattice = {!!}

  private
    _≤_ = {!!}

  refl-leq-Meet-Semilattice : is-reflexive leq-Meet-Semilattice
  refl-leq-Meet-Semilattice x = {!!}

  transitive-leq-Meet-Semilattice : is-transitive leq-Meet-Semilattice
  transitive-leq-Meet-Semilattice x y z H K = {!!}

  antisymmetric-leq-Meet-Semilattice : is-antisymmetric leq-Meet-Semilattice
  antisymmetric-leq-Meet-Semilattice x y H K = {!!}

  preorder-Meet-Semilattice : Preorder l l
  pr1 preorder-Meet-Semilattice = {!!}

  poset-Meet-Semilattice : Poset l l
  pr1 poset-Meet-Semilattice = {!!}

  is-binary-lower-bound-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    is-binary-lower-bound-Poset
      ( poset-Meet-Semilattice)
      ( x)
      ( y)
      ( meet-Meet-Semilattice x y)
  is-binary-lower-bound-meet-Meet-Semilattice = {!!}

  is-greatest-binary-lower-bound-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    is-greatest-binary-lower-bound-Poset
      ( poset-Meet-Semilattice)
      ( x)
      ( y)
      ( meet-Meet-Semilattice x y)
  is-greatest-binary-lower-bound-meet-Meet-Semilattice = {!!}

  has-greatest-binary-lower-bound-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    has-greatest-binary-lower-bound-Poset (poset-Meet-Semilattice) x y
  has-greatest-binary-lower-bound-Meet-Semilattice = {!!}
```

### The predicate on posets of being a meet-semilattice

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-meet-semilattice-Poset-Prop : Prop (l1 ⊔ l2)
  is-meet-semilattice-Poset-Prop = {!!}

  is-meet-semilattice-Poset : UU (l1 ⊔ l2)
  is-meet-semilattice-Poset = {!!}

  is-prop-is-meet-semilattice-Poset :
    is-prop is-meet-semilattice-Poset
  is-prop-is-meet-semilattice-Poset = {!!}

  module _
    (H : is-meet-semilattice-Poset)
    where

    meet-is-meet-semilattice-Poset :
      type-Poset P → type-Poset P → type-Poset P
    meet-is-meet-semilattice-Poset = {!!}

    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Poset :
      (x y : type-Poset P) →
      is-greatest-binary-lower-bound-Poset P x y
        ( meet-is-meet-semilattice-Poset x y)
    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Poset = {!!}
```

### The order-theoretic definition of meet semilattices

```agda
Order-Theoretic-Meet-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Order-Theoretic-Meet-Semilattice l1 l2 = {!!}

module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  where

  poset-Order-Theoretic-Meet-Semilattice : Poset l1 l2
  poset-Order-Theoretic-Meet-Semilattice = {!!}

  type-Order-Theoretic-Meet-Semilattice : UU l1
  type-Order-Theoretic-Meet-Semilattice = {!!}

  is-set-type-Order-Theoretic-Meet-Semilattice :
    is-set type-Order-Theoretic-Meet-Semilattice
  is-set-type-Order-Theoretic-Meet-Semilattice = {!!}

  set-Order-Theoretic-Meet-Semilattice : Set l1
  set-Order-Theoretic-Meet-Semilattice = {!!}

  leq-Order-Theoretic-Meet-Semilattice-Prop :
    (x y : type-Order-Theoretic-Meet-Semilattice) → Prop l2
  leq-Order-Theoretic-Meet-Semilattice-Prop = {!!}

  leq-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) → UU l2
  leq-Order-Theoretic-Meet-Semilattice = {!!}

  is-prop-leq-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-prop (leq-Order-Theoretic-Meet-Semilattice x y)
  is-prop-leq-Order-Theoretic-Meet-Semilattice = {!!}

  refl-leq-Order-Theoretic-Meet-Semilattice :
    (x : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice x x
  refl-leq-Order-Theoretic-Meet-Semilattice = {!!}

  antisymmetric-leq-Order-Theoretic-Meet-Semilattice :
    {x y : type-Order-Theoretic-Meet-Semilattice} →
    leq-Order-Theoretic-Meet-Semilattice x y →
    leq-Order-Theoretic-Meet-Semilattice y x →
    x ＝ y
  antisymmetric-leq-Order-Theoretic-Meet-Semilattice = {!!}

  transitive-leq-Order-Theoretic-Meet-Semilattice :
    (x y z : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice y z →
    leq-Order-Theoretic-Meet-Semilattice x y →
    leq-Order-Theoretic-Meet-Semilattice x z
  transitive-leq-Order-Theoretic-Meet-Semilattice = {!!}

  is-meet-semilattice-Order-Theoretic-Meet-Semilattice :
    is-meet-semilattice-Poset poset-Order-Theoretic-Meet-Semilattice
  is-meet-semilattice-Order-Theoretic-Meet-Semilattice = {!!}

  meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    type-Order-Theoretic-Meet-Semilattice
  meet-Order-Theoretic-Meet-Semilattice = {!!}

  private
    _∧_ = {!!}

  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-greatest-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( x)
      ( y)
      ( x ∧ y)
  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice = {!!}

  is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( x)
      ( y)
      ( x ∧ y)
  is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-left-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice (x ∧ y) x
  leq-left-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-right-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice (x ∧ y) y
  leq-right-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-meet-Order-Theoretic-Meet-Semilattice :
    {x y z : type-Order-Theoretic-Meet-Semilattice} →
    leq-Order-Theoretic-Meet-Semilattice z x →
    leq-Order-Theoretic-Meet-Semilattice z y →
    leq-Order-Theoretic-Meet-Semilattice z (x ∧ y)
  leq-meet-Order-Theoretic-Meet-Semilattice = {!!}
```

## Properties

### The meet operation of order theoretic meet-semilattices is associative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (x y z : type-Order-Theoretic-Meet-Semilattice A)
  where

  private
    _∧_ = {!!}

  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ x
  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ y
  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ z
  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ x
  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice' = {!!}

  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ y
  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice' = {!!}

  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ z
  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice' = {!!}

  leq-associative-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ (x ∧ (y ∧ z))
  leq-associative-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-associative-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ ((x ∧ y) ∧ z)
  leq-associative-meet-Order-Theoretic-Meet-Semilattice' = {!!}

  associative-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ＝ (x ∧ (y ∧ z))
  associative-meet-Order-Theoretic-Meet-Semilattice = {!!}
```

### The meet operation of order theoretic meet-semilattices is commutative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (x y : type-Order-Theoretic-Meet-Semilattice A)
  where

  private
    _∧_ = {!!}

  leq-commutative-meet-Order-Theoretic-Meet-Semilattice :
    (x ∧ y) ≤ (y ∧ x)
  leq-commutative-meet-Order-Theoretic-Meet-Semilattice = {!!}

  leq-commutative-meet-Order-Theoretic-Meet-Semilattice' :
    (y ∧ x) ≤ (x ∧ y)
  leq-commutative-meet-Order-Theoretic-Meet-Semilattice' = {!!}

  commutative-meet-Order-Theoretic-Meet-Semilattice :
    (x ∧ y) ＝ (y ∧ x)
  commutative-meet-Order-Theoretic-Meet-Semilattice = {!!}
```

### The meet operation of order theoretic meet-semilattices is idempotent

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (x : type-Order-Theoretic-Meet-Semilattice A)
  where

  private
    _∧_ = {!!}

  idempotent-meet-Order-Theoretic-Meet-Semilattice :
    (x ∧ x) ＝ x
  idempotent-meet-Order-Theoretic-Meet-Semilattice = {!!}
```

### Any order theoretic meet-semilattice is an algebraic meet semilattice

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  where

  semigroup-Order-Theoretic-Meet-Semilattice : Semigroup l1
  pr1 semigroup-Order-Theoretic-Meet-Semilattice = {!!}

  meet-semilattice-Order-Theoretic-Meet-Semilattice :
    Meet-Semilattice l1
  meet-semilattice-Order-Theoretic-Meet-Semilattice = {!!}
```

### Any meet-semilattice `A` is isomorphic to the meet-semilattice obtained from the order theoretic meet-semilattice obtained from `A`

```agda
module _
  {l1 : Level} (A : Meet-Semilattice l1)
  where

  order-theoretic-meet-semilattice-Meet-Semilattice :
    Order-Theoretic-Meet-Semilattice l1 l1
  order-theoretic-meet-semilattice-Meet-Semilattice = {!!}

  compute-meet-order-theoretic-meet-semilattice-Meet-Semilattice :
    (x y : type-Meet-Semilattice A) →
    meet-Meet-Semilattice A x y ＝
    meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Meet-Semilattice)
      ( x)
      ( y)
  compute-meet-order-theoretic-meet-semilattice-Meet-Semilattice = {!!}

  compute-order-theoretic-meet-semilattice-Meet-Semilattice :
    iso-Semigroup
      ( semigroup-Meet-Semilattice A)
      ( semigroup-Meet-Semilattice
        ( meet-semilattice-Order-Theoretic-Meet-Semilattice
          ( order-theoretic-meet-semilattice-Meet-Semilattice)))
  compute-order-theoretic-meet-semilattice-Meet-Semilattice = {!!}
```
