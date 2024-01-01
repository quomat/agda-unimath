# Join-semilattices

```agda
module order-theory.join-semilattices where
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

open import group-theory.semigroups

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.upper-bounds-posets
```

</details>

## Idea

A **join-semilattice** is a poset in which every pair of elements has a least
binary upper bound. Alternatively, join-semilattices can be defined
algebraically as a set `X` equipped with a binary operation `∧ : X → X → X`
satisfying

1. Asociativity: `(x ∧ y) ∧ z ＝ x ∧ (y ∧ z)`,
2. Commutativity: `x ∧ y ＝ y ∧ x`,
3. Idempotency: `x ∧ x ＝ x`.

Note that this definition is identical to the definition of
[meet-semilattices](order-theory.meet-semilattices.md). We will follow the
algebraic approach for our principal definition of join-semilattices, since it
requires only one universe level. This is necessary in order to consider the
[large category](category-theory.large-categories.md) of join-semilattices.

## Definitions

### The predicate on semigroups of being a join-semilattice

```agda
module _
  {l : Level} (X : Semigroup l)
  where

  is-join-semilattice-prop-Semigroup : Prop l
  is-join-semilattice-prop-Semigroup = {!!}

  is-join-semilattice-Semigroup : UU l
  is-join-semilattice-Semigroup = {!!}

  is-prop-is-join-semilattice-Semigroup :
    is-prop is-join-semilattice-Semigroup
  is-prop-is-join-semilattice-Semigroup = {!!}
```

### The algebraic definition of join-semilattices

```agda
Join-Semilattice : (l : Level) → UU (lsuc l)
Join-Semilattice l = {!!}

module _
  {l : Level} (X : Join-Semilattice l)
  where

  semigroup-Join-Semilattice : Semigroup l
  semigroup-Join-Semilattice = {!!}

  set-Join-Semilattice : Set l
  set-Join-Semilattice = {!!}

  type-Join-Semilattice : UU l
  type-Join-Semilattice = {!!}

  is-set-type-Join-Semilattice : is-set type-Join-Semilattice
  is-set-type-Join-Semilattice = {!!}

  join-Join-Semilattice : (x y : type-Join-Semilattice) → type-Join-Semilattice
  join-Join-Semilattice = {!!}

  join-Join-Semilattice' : (x y : type-Join-Semilattice) → type-Join-Semilattice
  join-Join-Semilattice' x y = {!!}

  private
    _∨_ = {!!}

  associative-join-Join-Semilattice :
    (x y z : type-Join-Semilattice) → ((x ∨ y) ∨ z) ＝ (x ∨ (y ∨ z))
  associative-join-Join-Semilattice = {!!}

  is-join-semilattice-Join-Semilattice :
    is-join-semilattice-Semigroup semigroup-Join-Semilattice
  is-join-semilattice-Join-Semilattice = {!!}

  commutative-join-Join-Semilattice :
    (x y : type-Join-Semilattice) → (x ∨ y) ＝ (y ∨ x)
  commutative-join-Join-Semilattice = {!!}

  idempotent-join-Join-Semilattice :
    (x : type-Join-Semilattice) → (x ∨ x) ＝ x
  idempotent-join-Join-Semilattice = {!!}

  leq-Join-Semilattice-Prop :
    (x y : type-Join-Semilattice) → Prop l
  leq-Join-Semilattice-Prop = {!!}

  leq-Join-Semilattice :
    (x y : type-Join-Semilattice) → UU l
  leq-Join-Semilattice = {!!}

  is-prop-leq-Join-Semilattice :
    (x y : type-Join-Semilattice) → is-prop (leq-Join-Semilattice x y)
  is-prop-leq-Join-Semilattice = {!!}

  private
    _≤_ = {!!}

  refl-leq-Join-Semilattice : is-reflexive leq-Join-Semilattice
  refl-leq-Join-Semilattice x = {!!}

  transitive-leq-Join-Semilattice : is-transitive leq-Join-Semilattice
  transitive-leq-Join-Semilattice x y z H K = {!!}

  antisymmetric-leq-Join-Semilattice : is-antisymmetric leq-Join-Semilattice
  antisymmetric-leq-Join-Semilattice x y H K = {!!}

  preorder-Join-Semilattice : Preorder l l
  pr1 preorder-Join-Semilattice = {!!}

  poset-Join-Semilattice : Poset l l
  pr1 poset-Join-Semilattice = {!!}

  is-binary-upper-bound-join-Join-Semilattice :
    (x y : type-Join-Semilattice) →
    is-binary-upper-bound-Poset
      ( poset-Join-Semilattice)
      ( x)
      ( y)
      ( join-Join-Semilattice x y)
  is-binary-upper-bound-join-Join-Semilattice = {!!}

  is-least-binary-upper-bound-join-Join-Semilattice :
    (x y : type-Join-Semilattice) →
    is-least-binary-upper-bound-Poset
      ( poset-Join-Semilattice)
      ( x)
      ( y)
      ( join-Join-Semilattice x y)
  is-least-binary-upper-bound-join-Join-Semilattice = {!!}
```

### The predicate on posets of being a join-semilattice

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-join-semilattice-Poset-Prop : Prop (l1 ⊔ l2)
  is-join-semilattice-Poset-Prop = {!!}

  is-join-semilattice-Poset : UU (l1 ⊔ l2)
  is-join-semilattice-Poset = {!!}

  is-prop-is-join-semilattice-Poset :
    is-prop is-join-semilattice-Poset
  is-prop-is-join-semilattice-Poset = {!!}

  module _
    (H : is-join-semilattice-Poset)
    where

    join-is-join-semilattice-Poset :
      type-Poset P → type-Poset P → type-Poset P
    join-is-join-semilattice-Poset = {!!}

    is-least-binary-upper-bound-join-is-join-semilattice-Poset :
      (x y : type-Poset P) →
      is-least-binary-upper-bound-Poset P x y
        ( join-is-join-semilattice-Poset x y)
    is-least-binary-upper-bound-join-is-join-semilattice-Poset = {!!}
```

### The order-theoretic definition of join semilattices

```agda
Order-Theoretic-Join-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Order-Theoretic-Join-Semilattice l1 l2 = {!!}

module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  where

  poset-Order-Theoretic-Join-Semilattice : Poset l1 l2
  poset-Order-Theoretic-Join-Semilattice = {!!}

  type-Order-Theoretic-Join-Semilattice : UU l1
  type-Order-Theoretic-Join-Semilattice = {!!}

  is-set-type-Order-Theoretic-Join-Semilattice :
    is-set type-Order-Theoretic-Join-Semilattice
  is-set-type-Order-Theoretic-Join-Semilattice = {!!}

  set-Order-Theoretic-Join-Semilattice : Set l1
  set-Order-Theoretic-Join-Semilattice = {!!}

  leq-Order-Theoretic-Join-Semilattice-Prop :
    (x y : type-Order-Theoretic-Join-Semilattice) → Prop l2
  leq-Order-Theoretic-Join-Semilattice-Prop = {!!}

  leq-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) → UU l2
  leq-Order-Theoretic-Join-Semilattice = {!!}

  is-prop-leq-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    is-prop (leq-Order-Theoretic-Join-Semilattice x y)
  is-prop-leq-Order-Theoretic-Join-Semilattice = {!!}

  refl-leq-Order-Theoretic-Join-Semilattice :
    (x : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice x x
  refl-leq-Order-Theoretic-Join-Semilattice = {!!}

  antisymmetric-leq-Order-Theoretic-Join-Semilattice :
    {x y : type-Order-Theoretic-Join-Semilattice} →
    leq-Order-Theoretic-Join-Semilattice x y →
    leq-Order-Theoretic-Join-Semilattice y x →
    x ＝ y
  antisymmetric-leq-Order-Theoretic-Join-Semilattice = {!!}

  transitive-leq-Order-Theoretic-Join-Semilattice :
    (x y z : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice y z →
    leq-Order-Theoretic-Join-Semilattice x y →
    leq-Order-Theoretic-Join-Semilattice x z
  transitive-leq-Order-Theoretic-Join-Semilattice = {!!}

  is-join-semilattice-Order-Theoretic-Join-Semilattice :
    is-join-semilattice-Poset poset-Order-Theoretic-Join-Semilattice
  is-join-semilattice-Order-Theoretic-Join-Semilattice = {!!}

  join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    type-Order-Theoretic-Join-Semilattice
  join-Order-Theoretic-Join-Semilattice = {!!}

  private
    _∨_ = {!!}

  is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    is-least-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( x)
      ( y)
      ( x ∨ y)
  is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice = {!!}

  is-binary-upper-bound-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    is-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( x)
      ( y)
      ( x ∨ y)
  is-binary-upper-bound-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-left-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice x (x ∨ y)
  leq-left-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-right-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice y (x ∨ y)
  leq-right-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-join-Order-Theoretic-Join-Semilattice :
    {x y z : type-Order-Theoretic-Join-Semilattice} →
    leq-Order-Theoretic-Join-Semilattice x z →
    leq-Order-Theoretic-Join-Semilattice y z →
    leq-Order-Theoretic-Join-Semilattice (x ∨ y) z
  leq-join-Order-Theoretic-Join-Semilattice = {!!}
```

## Properties

### The join operation of order theoretic join-semilattices is associative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  (x y z : type-Order-Theoretic-Join-Semilattice A)
  where

  private
    _∨_ = {!!}

  leq-left-triple-join-Order-Theoretic-Join-Semilattice :
    x ≤ ((x ∨ y) ∨ z)
  leq-left-triple-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-center-triple-join-Order-Theoretic-Join-Semilattice :
    y ≤ ((x ∨ y) ∨ z)
  leq-center-triple-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-right-triple-join-Order-Theoretic-Join-Semilattice :
    z ≤ ((x ∨ y) ∨ z)
  leq-right-triple-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-left-triple-join-Order-Theoretic-Join-Semilattice' :
    x ≤ (x ∨ (y ∨ z))
  leq-left-triple-join-Order-Theoretic-Join-Semilattice' = {!!}

  leq-center-triple-join-Order-Theoretic-Join-Semilattice' :
    y ≤ (x ∨ (y ∨ z))
  leq-center-triple-join-Order-Theoretic-Join-Semilattice' = {!!}

  leq-right-triple-join-Order-Theoretic-Join-Semilattice' :
    z ≤ (x ∨ (y ∨ z))
  leq-right-triple-join-Order-Theoretic-Join-Semilattice' = {!!}

  leq-associative-join-Order-Theoretic-Join-Semilattice :
    ((x ∨ y) ∨ z) ≤ (x ∨ (y ∨ z))
  leq-associative-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-associative-join-Order-Theoretic-Join-Semilattice' :
    (x ∨ (y ∨ z)) ≤ ((x ∨ y) ∨ z)
  leq-associative-join-Order-Theoretic-Join-Semilattice' = {!!}

  associative-join-Order-Theoretic-Join-Semilattice :
    ((x ∨ y) ∨ z) ＝ (x ∨ (y ∨ z))
  associative-join-Order-Theoretic-Join-Semilattice = {!!}
```

### The join operation of order theoretic join-semilattices is commutative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  (x y : type-Order-Theoretic-Join-Semilattice A)
  where

  private
    _∨_ = {!!}

  leq-commutative-join-Order-Theoretic-Join-Semilattice :
    (x ∨ y) ≤ (y ∨ x)
  leq-commutative-join-Order-Theoretic-Join-Semilattice = {!!}

  leq-commutative-join-Order-Theoretic-Join-Semilattice' :
    (y ∨ x) ≤ (x ∨ y)
  leq-commutative-join-Order-Theoretic-Join-Semilattice' = {!!}

  commutative-join-Order-Theoretic-Join-Semilattice :
    (x ∨ y) ＝ (y ∨ x)
  commutative-join-Order-Theoretic-Join-Semilattice = {!!}
```

### The join operation of order theoretic join-semilattices is idempotent

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  (x : type-Order-Theoretic-Join-Semilattice A)
  where

  private
    _∨_ = {!!}

  idempotent-join-Order-Theoretic-Join-Semilattice :
    (x ∨ x) ＝ x
  idempotent-join-Order-Theoretic-Join-Semilattice = {!!}
```

### Any order theoretic join-semilattice is an algebraic join semilattice

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  where

  semigroup-Order-Theoretic-Join-Semilattice : Semigroup l1
  pr1 semigroup-Order-Theoretic-Join-Semilattice = {!!}

  join-semilattice-Order-Theoretic-Join-Semilattice :
    Join-Semilattice l1
  join-semilattice-Order-Theoretic-Join-Semilattice = {!!}
```
