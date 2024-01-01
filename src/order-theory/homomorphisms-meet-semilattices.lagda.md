# Homomorphisms of meet-semilattices

```agda
module order-theory.homomorphisms-meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups

open import order-theory.greatest-lower-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

A **homomorphism of meet-semilattice** is a map that preserves meets. It follows
that homomorphisms of meet-semilattices are order preserving.

## Definitions

### Homomorphisms of algebraic meet-semilattices

```agda
module _
  {l1 l2 : Level}
  (A : Meet-Semilattice l1) (B : Meet-Semilattice l2)
  where

  preserves-meet-Prop :
    (type-Meet-Semilattice A → type-Meet-Semilattice B) → Prop (l1 ⊔ l2)
  preserves-meet-Prop = {!!}

  preserves-meet :
    (type-Meet-Semilattice A → type-Meet-Semilattice B) → UU (l1 ⊔ l2)
  preserves-meet = {!!}

  is-prop-preserves-meet :
    (f : type-Meet-Semilattice A → type-Meet-Semilattice B) →
    is-prop (preserves-meet f)
  is-prop-preserves-meet = {!!}

  hom-set-Meet-Semilattice : Set (l1 ⊔ l2)
  hom-set-Meet-Semilattice = {!!}

  hom-Meet-Semilattice : UU (l1 ⊔ l2)
  hom-Meet-Semilattice = {!!}

  is-set-hom-Meet-Semilattice : is-set hom-Meet-Semilattice
  is-set-hom-Meet-Semilattice = {!!}

  module _
    (f : hom-Meet-Semilattice)
    where

    map-hom-Meet-Semilattice :
      type-Meet-Semilattice A → type-Meet-Semilattice B
    map-hom-Meet-Semilattice = {!!}

    preserves-meet-hom-Meet-Semilattice :
      preserves-meet map-hom-Meet-Semilattice
    preserves-meet-hom-Meet-Semilattice = {!!}

    preserves-order-hom-Meet-Semilattice :
      preserves-order-Poset
        ( poset-Meet-Semilattice A)
        ( poset-Meet-Semilattice B)
        ( map-hom-Meet-Semilattice)
    preserves-order-hom-Meet-Semilattice x y H = {!!}

    hom-poset-hom-Meet-Semilattice :
      hom-Poset (poset-Meet-Semilattice A) (poset-Meet-Semilattice B)
    pr1 hom-poset-hom-Meet-Semilattice = {!!}
```

### Homomorphisms of order-theoretic meet-semilattices

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (B : Order-Theoretic-Meet-Semilattice l3 l4)
  where

  preserves-meet-hom-Poset-Prop :
    hom-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      ( poset-Order-Theoretic-Meet-Semilattice B) → Prop (l1 ⊔ l3 ⊔ l4)
  preserves-meet-hom-Poset-Prop (f , H) = {!!}

  preserves-meet-hom-Poset :
    hom-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      ( poset-Order-Theoretic-Meet-Semilattice B) → UU (l1 ⊔ l3 ⊔ l4)
  preserves-meet-hom-Poset f = {!!}

  is-prop-preserves-meet-hom-Prop :
    ( f :
      hom-Poset
        ( poset-Order-Theoretic-Meet-Semilattice A)
        ( poset-Order-Theoretic-Meet-Semilattice B)) →
    is-prop (preserves-meet-hom-Poset f)
  is-prop-preserves-meet-hom-Prop f = {!!}

  hom-set-Order-Theoretic-Meet-Semilattice : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-Order-Theoretic-Meet-Semilattice = {!!}
```
