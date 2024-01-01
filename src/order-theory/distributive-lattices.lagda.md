# Distributive lattices

```agda
module order-theory.distributive-lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.lattices
open import order-theory.meet-semilattices
open import order-theory.posets
```

</details>

## Idea

A **distributive lattice** is a lattice in which meets distribute over joins.

## Definition

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  is-distributive-lattice-Prop : Prop l1
  is-distributive-lattice-Prop = {!!}

  is-distributive-Lattice : UU l1
  is-distributive-Lattice = {!!}

  is-prop-is-distributive-Lattice : is-prop is-distributive-Lattice
  is-prop-is-distributive-Lattice = {!!}

Distributive-Lattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Distributive-Lattice = {!!}

module _
  {l1 l2 : Level} (L : Distributive-Lattice l1 l2)
  where

  lattice-Distributive-Lattice : Lattice l1 l2
  lattice-Distributive-Lattice = {!!}

  poset-Distributive-Lattice : Poset l1 l2
  poset-Distributive-Lattice = {!!}

  type-Distributive-Lattice : UU l1
  type-Distributive-Lattice = {!!}

  leq-Distributive-Lattice-Prop : (x y : type-Distributive-Lattice) → Prop l2
  leq-Distributive-Lattice-Prop = {!!}

  leq-Distributive-Lattice : (x y : type-Distributive-Lattice) → UU l2
  leq-Distributive-Lattice = {!!}

  is-prop-leq-Distributive-Lattice :
    (x y : type-Distributive-Lattice) → is-prop (leq-Distributive-Lattice x y)
  is-prop-leq-Distributive-Lattice = {!!}

  refl-leq-Distributive-Lattice : is-reflexive leq-Distributive-Lattice
  refl-leq-Distributive-Lattice = {!!}

  antisymmetric-leq-Distributive-Lattice :
    is-antisymmetric leq-Distributive-Lattice
  antisymmetric-leq-Distributive-Lattice = {!!}

  transitive-leq-Distributive-Lattice : is-transitive leq-Distributive-Lattice
  transitive-leq-Distributive-Lattice = {!!}

  is-set-type-Distributive-Lattice : is-set type-Distributive-Lattice
  is-set-type-Distributive-Lattice = {!!}

  set-Distributive-Lattice : Set l1
  set-Distributive-Lattice = {!!}

  is-lattice-Distributive-Lattice :
    is-lattice-Poset poset-Distributive-Lattice
  is-lattice-Distributive-Lattice = {!!}

  is-meet-semilattice-Distributive-Lattice :
    is-meet-semilattice-Poset poset-Distributive-Lattice
  is-meet-semilattice-Distributive-Lattice = {!!}

  meet-semilattice-Distributive-Lattice : Meet-Semilattice l1
  meet-semilattice-Distributive-Lattice = {!!}

  meet-Distributive-Lattice :
    (x y : type-Distributive-Lattice) → type-Distributive-Lattice
  meet-Distributive-Lattice = {!!}

  is-join-semilattice-Distributive-Lattice :
    is-join-semilattice-Poset poset-Distributive-Lattice
  is-join-semilattice-Distributive-Lattice = {!!}

  join-semilattice-Distributive-Lattice : Join-Semilattice l1
  join-semilattice-Distributive-Lattice = {!!}

  join-Distributive-Lattice :
    (x y : type-Distributive-Lattice) → type-Distributive-Lattice
  join-Distributive-Lattice = {!!}

  distributive-meet-join-Distributive-Lattice :
    (x y z : type-Distributive-Lattice) →
    meet-Distributive-Lattice x (join-Distributive-Lattice y z) ＝
    join-Distributive-Lattice
      ( meet-Distributive-Lattice x y)
      ( meet-Distributive-Lattice x z)
  distributive-meet-join-Distributive-Lattice = {!!}
```
