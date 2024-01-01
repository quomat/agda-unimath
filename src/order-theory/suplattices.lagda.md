# Suplattices

```agda
module order-theory.suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
```

</details>

## Idea

An **`l`-suplattice** is a poset which has all least upper bounds of families of
elements indexed by a type of universe level `l`.

## Definitions

### The predicate on posets of being an `l`-suplattice

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-suplattice-Poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-suplattice-Poset-Prop = {!!}

  is-suplattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-suplattice-Poset = {!!}

  is-prop-suplattice-Poset : is-prop is-suplattice-Poset
  is-prop-suplattice-Poset = {!!}

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (H : is-suplattice-Poset l3 P)
  where

  sup-is-suplattice-Poset :
    {I : UU l3} → (I → type-Poset P) → type-Poset P
  sup-is-suplattice-Poset = {!!}

  is-least-upper-bound-sup-is-suplattice-Poset :
    {I : UU l3} (x : I → type-Poset P) →
    is-least-upper-bound-family-of-elements-Poset P x
      ( sup-is-suplattice-Poset x)
  is-least-upper-bound-sup-is-suplattice-Poset = {!!}
```

### `l`-Suplattices

```agda
Suplattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Suplattice = {!!}

module _
  {l1 l2 l3 : Level} (A : Suplattice l1 l2 l3)
  where

  poset-Suplattice : Poset l1 l2
  poset-Suplattice = {!!}

  type-Suplattice : UU l1
  type-Suplattice = {!!}

  leq-Suplattice-Prop : (x y : type-Suplattice) → Prop l2
  leq-Suplattice-Prop = {!!}

  leq-Suplattice : (x y : type-Suplattice) → UU l2
  leq-Suplattice = {!!}

  is-prop-leq-Suplattice :
    (x y : type-Suplattice) → is-prop (leq-Suplattice x y)
  is-prop-leq-Suplattice = {!!}

  refl-leq-Suplattice :
    (x : type-Suplattice) → leq-Suplattice x x
  refl-leq-Suplattice = {!!}

  antisymmetric-leq-Suplattice : is-antisymmetric leq-Suplattice
  antisymmetric-leq-Suplattice = {!!}

  transitive-leq-Suplattice : is-transitive leq-Suplattice
  transitive-leq-Suplattice = {!!}

  is-set-type-Suplattice : is-set type-Suplattice
  is-set-type-Suplattice = {!!}

  set-Suplattice : Set l1
  set-Suplattice = {!!}

  is-suplattice-Suplattice :
    is-suplattice-Poset l3 poset-Suplattice
  is-suplattice-Suplattice = {!!}

  sup-Suplattice :
    {I : UU l3} → (I → type-Suplattice) → type-Suplattice
  sup-Suplattice = {!!}

  is-least-upper-bound-sup-Suplattice :
    {I : UU l3} (x : I → type-Suplattice) →
    is-least-upper-bound-family-of-elements-Poset poset-Suplattice x
      ( sup-Suplattice x)
  is-least-upper-bound-sup-Suplattice = {!!}
```
