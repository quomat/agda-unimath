# Lattices

```agda
module order-theory.lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.meet-semilattices
open import order-theory.posets
```

</details>

## Idea

A **lattice** is a poset in which every pair of elements has a meet (a greatest
lower bound) and a join (a least upper bound).

Note that we don't require that meets distribute over joins. Such lattices are
called [distributive lattices](order-theory.distributive-lattices.md).

## Definitions

### Order theoretic lattices

```agda
is-lattice-Poset-Prop :
  {l1 l2 : Level} (P : Poset l1 l2) → Prop (l1 ⊔ l2)
is-lattice-Poset-Prop = {!!}

is-lattice-Poset : {l1 l2 : Level} → Poset l1 l2 → UU (l1 ⊔ l2)
is-lattice-Poset = {!!}

is-prop-is-lattice-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) → is-prop (is-lattice-Poset P)
is-prop-is-lattice-Poset = {!!}

Lattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Lattice = {!!}

module _
  {l1 l2 : Level} (A : Lattice l1 l2)
  where

  poset-Lattice : Poset l1 l2
  poset-Lattice = {!!}

  type-Lattice : UU l1
  type-Lattice = {!!}

  leq-lattice-Prop : (x y : type-Lattice) → Prop l2
  leq-lattice-Prop = {!!}

  leq-Lattice : (x y : type-Lattice) → UU l2
  leq-Lattice = {!!}

  is-prop-leq-Lattice : (x y : type-Lattice) → is-prop (leq-Lattice x y)
  is-prop-leq-Lattice = {!!}

  refl-leq-Lattice : is-reflexive leq-Lattice
  refl-leq-Lattice = {!!}

  antisymmetric-leq-Lattice : is-antisymmetric leq-Lattice
  antisymmetric-leq-Lattice = {!!}

  transitive-leq-Lattice : is-transitive leq-Lattice
  transitive-leq-Lattice = {!!}

  is-set-type-Lattice : is-set type-Lattice
  is-set-type-Lattice = {!!}

  set-Lattice : Set l1
  set-Lattice = {!!}

  is-lattice-Lattice : is-lattice-Poset poset-Lattice
  is-lattice-Lattice = {!!}

  is-meet-semilattice-Lattice : is-meet-semilattice-Poset poset-Lattice
  is-meet-semilattice-Lattice = {!!}

  meet-semilattice-Lattice : Meet-Semilattice l1
  meet-semilattice-Lattice = {!!}

  meet-Lattice : (x y : type-Lattice) → type-Lattice
  meet-Lattice = {!!}

  is-join-semilattice-Lattice : is-join-semilattice-Poset poset-Lattice
  is-join-semilattice-Lattice = {!!}

  join-semilattice-Lattice : Join-Semilattice l1
  join-semilattice-Lattice = {!!}

  join-Lattice : (x y : type-Lattice) → type-Lattice
  join-Lattice = {!!}
```
