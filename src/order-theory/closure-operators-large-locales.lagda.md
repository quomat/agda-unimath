# Closure operators on large locales

```agda
module order-theory.closure-operators-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closure-operators-large-posets
open import order-theory.large-frames
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-meet-subsemilattices
open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-subpreorders
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

A **closure operator** on a [large locale](order-theory.large-locales.md) `L` is
a [closure operator](order-theory.closure-operators-large-posets.md) on the
underlying [large poset](order-theory.large-posets.md) of `L`.

We show that if the closed elements are closed under meets, then the closed
elements form a large locale. Note that the condition that the closed elements
are closed under meets is more general than the condition that the closure
operator is a [nucleus](order-theory.nuclei-large-locales.md).

## Definitions

### Closure operators on large locales

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ)
  where

  closure-operator-Large-Locale : UUω
  closure-operator-Large-Locale = {!!}

  module _
    (j : closure-operator-Large-Locale)
    where

    hom-large-poset-closure-operator-Large-Locale :
      hom-Large-Poset
        ( λ l → l)
        ( large-poset-Large-Locale L)
        ( large-poset-Large-Locale L)
    hom-large-poset-closure-operator-Large-Locale = {!!}

    map-closure-operator-Large-Locale :
      {l1 : Level} → type-Large-Locale L l1 → type-Large-Locale L l1
    map-closure-operator-Large-Locale = {!!}

    preserves-order-closure-operator-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1)
      (y : type-Large-Locale L l2) →
      leq-Large-Locale L x y →
      leq-Large-Locale L
        ( map-closure-operator-Large-Locale x)
        ( map-closure-operator-Large-Locale y)
    preserves-order-closure-operator-Large-Locale = {!!}

    is-inflationary-closure-operator-Large-Locale :
      {l1 : Level} (x : type-Large-Locale L l1) →
      leq-Large-Locale L x
        ( map-closure-operator-Large-Locale x)
    is-inflationary-closure-operator-Large-Locale = {!!}

    is-idempotent-closure-operator-Large-Locale :
      {l1 : Level} (x : type-Large-Locale L l1) →
      map-closure-operator-Large-Locale
        ( map-closure-operator-Large-Locale x) ＝
      map-closure-operator-Large-Locale x
    is-idempotent-closure-operator-Large-Locale = {!!}
```

### The large suplattice of `j`-closed elements of a closure operator

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ) (j : closure-operator-Large-Locale L)
  where

  large-subpreorder-closure-operator-Large-Locale :
    Large-Subpreorder α (large-preorder-Large-Locale L)
  large-subpreorder-closure-operator-Large-Locale {l1} x = {!!}

  is-closed-element-closure-operator-Large-Locale :
    {l1 : Level} → type-Large-Locale L l1 → UU (α l1)
  is-closed-element-closure-operator-Large-Locale = {!!}

  is-prop-is-closed-element-closure-operator-Large-Locale :
    {l1 : Level} (x : type-Large-Locale L l1) →
    is-prop (is-closed-element-closure-operator-Large-Locale x)
  is-prop-is-closed-element-closure-operator-Large-Locale = {!!}

  is-closed-element-leq-closure-operator-Large-Locale :
    {l1 : Level} (x : type-Large-Locale L l1) →
    leq-Large-Locale L (map-closure-operator-Large-Locale L j x) x →
    is-closed-element-closure-operator-Large-Locale x
  is-closed-element-leq-closure-operator-Large-Locale x H = {!!}

  closed-element-closure-operator-Large-Locale :
    (l1 : Level) → UU (α l1)
  closed-element-closure-operator-Large-Locale = {!!}

  is-closed-under-sim-closure-operator-Large-Locale :
    {l1 l2 : Level}
    (x : type-Large-Locale L l1)
    (y : type-Large-Locale L l2) →
    leq-Large-Locale L x y → leq-Large-Locale L y x →
    is-closed-element-closure-operator-Large-Locale x →
    is-closed-element-closure-operator-Large-Locale y
  is-closed-under-sim-closure-operator-Large-Locale x y H K c = {!!}

  large-subposet-closure-operator-Large-Locale :
    Large-Subposet α (large-poset-Large-Locale L)
  large-subpreorder-Large-Subposet
    large-subposet-closure-operator-Large-Locale = {!!}

  large-poset-closure-operator-Large-Locale :
    Large-Poset α β
  large-poset-closure-operator-Large-Locale = {!!}

  leq-prop-closed-element-closure-operator-Large-Locale :
    Large-Relation-Prop α β closed-element-closure-operator-Large-Locale
  leq-prop-closed-element-closure-operator-Large-Locale = {!!}

  leq-closed-element-closure-operator-Large-Locale :
    Large-Relation α β closed-element-closure-operator-Large-Locale
  leq-closed-element-closure-operator-Large-Locale = {!!}

  is-prop-leq-closed-element-closure-operator-Large-Locale :
    is-prop-Large-Relation
      ( closed-element-closure-operator-Large-Locale)
      ( leq-closed-element-closure-operator-Large-Locale)
  is-prop-leq-closed-element-closure-operator-Large-Locale = {!!}

  refl-leq-closed-element-closure-operator-Large-Locale :
    is-reflexive-Large-Relation
      ( closed-element-closure-operator-Large-Locale)
      ( leq-closed-element-closure-operator-Large-Locale)
  refl-leq-closed-element-closure-operator-Large-Locale = {!!}

  antisymmetric-leq-closed-element-closure-operator-Large-Locale :
    is-antisymmetric-Large-Relation
      ( closed-element-closure-operator-Large-Locale)
      ( leq-closed-element-closure-operator-Large-Locale)
  antisymmetric-leq-closed-element-closure-operator-Large-Locale = {!!}

  transitive-leq-closed-element-closure-operator-Large-Locale :
    is-transitive-Large-Relation
      ( closed-element-closure-operator-Large-Locale)
      ( leq-closed-element-closure-operator-Large-Locale)
  transitive-leq-closed-element-closure-operator-Large-Locale = {!!}

  contains-top-large-subposet-closure-operator-Large-Locale :
    is-closed-element-closure-operator-Large-Locale
      ( top-Large-Locale L)
  contains-top-large-subposet-closure-operator-Large-Locale = {!!}

  forward-implication-adjoint-relation-closure-operator-Large-Locale :
    {l1 l2 : Level}
    {x : type-Large-Locale L l1}
    {y : type-Large-Locale L l2} →
    is-closed-element-closure-operator-Large-Locale y →
    leq-Large-Locale L x y →
    leq-Large-Locale L (map-closure-operator-Large-Locale L j x) y
  forward-implication-adjoint-relation-closure-operator-Large-Locale
    {x = x} {y} H K = {!!}

  backward-implication-adjoint-relation-closure-operator-Large-Locale :
    {l1 l2 : Level}
    {x : type-Large-Locale L l1}
    {y : type-Large-Locale L l2} →
    leq-Large-Locale L (map-closure-operator-Large-Locale L j x) y →
    leq-Large-Locale L x y
  backward-implication-adjoint-relation-closure-operator-Large-Locale
    {x = x} {y} H = {!!}

  adjoint-relation-closure-operator-Large-Locale :
    {l1 l2 : Level}
    (x : type-Large-Locale L l1)
    (y : type-Large-Locale L l2) →
    is-closed-element-closure-operator-Large-Locale y →
    leq-Large-Locale L x y ↔
    leq-Large-Locale L (map-closure-operator-Large-Locale L j x) y
  pr1 (adjoint-relation-closure-operator-Large-Locale x y H) = {!!}

  sup-closed-element-closure-operator-Large-Locale :
    {l1 l2 : Level} {I : UU l1}
    (x : I → closed-element-closure-operator-Large-Locale l2) →
    closed-element-closure-operator-Large-Locale (γ ⊔ l1 ⊔ l2)
  pr1 (sup-closed-element-closure-operator-Large-Locale x) = {!!}

  is-least-upper-bound-sup-closed-element-closure-operator-Large-Locale :
    {l1 l2 : Level} {I : UU l1}
    (x : I → closed-element-closure-operator-Large-Locale l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-closure-operator-Large-Locale)
      ( x)
      ( sup-closed-element-closure-operator-Large-Locale x)
  pr1
    ( is-least-upper-bound-sup-closed-element-closure-operator-Large-Locale x y)
    ( H) = {!!}

  is-large-suplattice-large-poset-closure-operator-Large-Locale :
    is-large-suplattice-Large-Poset γ
      ( large-poset-closure-operator-Large-Locale)
  sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-large-poset-closure-operator-Large-Locale x) = {!!}

  large-suplattice-closure-operator-Large-Locale :
    Large-Suplattice α β γ
  large-poset-Large-Suplattice
    large-suplattice-closure-operator-Large-Locale = {!!}
```

### The predicate that the closed elements of a closure operator on a large locale are closed under meets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ) (j : closure-operator-Large-Locale L)
  where

  is-closed-under-meets-closure-operator-Large-Locale : UUω
  is-closed-under-meets-closure-operator-Large-Locale = {!!}
```

## Properties

### If the closed elements are closed under meets, then the closed elements of a closure operator form a large locale

We also assume that `x ∧ j y ＝ j (x ∧ y)` for any closed element `x`. In large
locales with exponentials it seems that we can omit this extra hypothesis.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ) (j : closure-operator-Large-Locale L)
  (H : is-closed-under-meets-closure-operator-Large-Locale L j)
  (K :
    {l1 l2 : Level} (x : type-Large-Locale L l1) (y : type-Large-Locale L l2) →
    is-closed-element-closure-operator-Large-Locale L j x →
    meet-Large-Locale L x (map-closure-operator-Large-Locale L j y) ＝
    map-closure-operator-Large-Locale L j (meet-Large-Locale L x y))
  where

  large-meet-subsemilattice-closure-operator-Large-Locale :
    Large-Meet-Subsemilattice α (large-meet-semilattice-Large-Locale L)
  large-subposet-Large-Meet-Subsemilattice
    large-meet-subsemilattice-closure-operator-Large-Locale = {!!}

  large-meet-semilattice-closure-operator-Large-Locale :
    Large-Meet-Semilattice α β
  large-meet-semilattice-closure-operator-Large-Locale = {!!}

  is-large-meet-semilattice-large-poset-closure-operator-Large-Locale :
    is-large-meet-semilattice-Large-Poset
      ( large-poset-closure-operator-Large-Locale L j)
  is-large-meet-semilattice-large-poset-closure-operator-Large-Locale = {!!}

  meet-closed-element-closure-operator-Large-Locale :
    {l1 l2 : Level} →
    closed-element-closure-operator-Large-Locale L j l1 →
    closed-element-closure-operator-Large-Locale L j l2 →
    closed-element-closure-operator-Large-Locale L j (l1 ⊔ l2)
  meet-closed-element-closure-operator-Large-Locale = {!!}

  distributive-meet-sup-closure-operator-Large-Locale :
    {l1 l2 l3 : Level}
    (x : closed-element-closure-operator-Large-Locale L j l1)
    {I : UU l2} (y : I → closed-element-closure-operator-Large-Locale L j l3) →
    meet-closed-element-closure-operator-Large-Locale x
      ( sup-closed-element-closure-operator-Large-Locale L j y) ＝
    sup-closed-element-closure-operator-Large-Locale L j
      ( λ i →
        meet-closed-element-closure-operator-Large-Locale x (y i))
  distributive-meet-sup-closure-operator-Large-Locale (x , p) y = {!!}

  large-frame-closure-operator-Large-Locale :
    Large-Frame α β γ
  large-poset-Large-Frame
    large-frame-closure-operator-Large-Locale = {!!}

  large-locale-closure-operator-Large-Locale :
    Large-Locale α β γ
  large-locale-closure-operator-Large-Locale = {!!}
```
