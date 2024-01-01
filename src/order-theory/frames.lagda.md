# Frames

```agda
module order-theory.frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.meet-suplattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

A **frame** is a [meet-suplattice](order-theory.meet-suplattices.md) with
arbitrary joins in which meets distribute over suprema. The **distributive law
for meets over suprema** states that in any
[meet-suplattice](order-theory.meet-suplattices.md) `A`, we have

```text
  x ∧ (⋁ᵢ yᵢ) ＝ ⋁ᵢ (x ∧ yᵢ)
```

for every element `x : A` and any family `y : I → A`.

## Definitions

### Statement of (instances of) the infinite distributive law

#### In posets

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2)
  where

  module _
    {I : UU l3} {x : type-Poset P} {y : I → type-Poset P}
    (H : has-least-upper-bound-family-of-elements-Poset P y)
    (K : has-greatest-binary-lower-bound-Poset P x (pr1 H))
    (L : (i : I) → has-greatest-binary-lower-bound-Poset P x (y i))
    (M : has-least-upper-bound-family-of-elements-Poset P (λ i → (pr1 (L i))))
    where

    instance-distributive-law-meet-sup-Poset-Prop : Prop l1
    instance-distributive-law-meet-sup-Poset-Prop = {!!}

    instance-distributive-law-meet-sup-Poset : UU l1
    instance-distributive-law-meet-sup-Poset = {!!}

    is-prop-instance-distributive-law-meet-sup-Poset :
      is-prop instance-distributive-law-meet-sup-Poset
    is-prop-instance-distributive-law-meet-sup-Poset = {!!}

  module _
    ( H : is-meet-semilattice-Poset P)
    ( K : is-suplattice-Poset l3 P)
    where

    distributive-law-meet-sup-Poset-Prop : Prop (l1 ⊔ lsuc l3)
    distributive-law-meet-sup-Poset-Prop = {!!}

    distributive-law-meet-sup-Poset : UU (l1 ⊔ lsuc l3)
    distributive-law-meet-sup-Poset = {!!}

    is-prop-distributive-law-meet-sup-Poset :
      is-prop distributive-law-meet-sup-Poset
    is-prop-distributive-law-meet-sup-Poset = {!!}
```

#### In meet-semilattices

```agda
instance-distributive-law-meet-sup-Meet-Semilattice :
  {l1 l2 : Level} (L : Meet-Semilattice l1) {I : UU l2}
  ( x : type-Meet-Semilattice L)
  { y : I → type-Meet-Semilattice L} →
  ( H :
    has-least-upper-bound-family-of-elements-Poset
      ( poset-Meet-Semilattice L)
      ( y))
  ( K :
    has-least-upper-bound-family-of-elements-Poset
      ( poset-Meet-Semilattice L)
      ( λ i → meet-Meet-Semilattice L x (y i))) →
  UU l1
instance-distributive-law-meet-sup-Meet-Semilattice = {!!}
```

#### Statement of the distributive law in meet-suplattices

```agda
module _
  {l1 l2 : Level} (L : Meet-Suplattice l1 l2)
  where

  private
    _∧_ = {!!}

  distributive-law-Meet-Suplattice-Prop : Prop (l1 ⊔ lsuc l2)
  distributive-law-Meet-Suplattice-Prop = {!!}

  distributive-law-Meet-Suplattice : UU (l1 ⊔ lsuc l2)
  distributive-law-Meet-Suplattice = {!!}

  is-prop-distributive-law-Meet-Suplattice :
    is-prop distributive-law-Meet-Suplattice
  is-prop-distributive-law-Meet-Suplattice = {!!}
```

### The predicate on meet-suplattices to be a frame

```agda
module _
  {l1 l2 : Level} (L : Meet-Suplattice l1 l2)
  where

  is-frame-Meet-Suplattice-Prop : Prop (l1 ⊔ lsuc l2)
  is-frame-Meet-Suplattice-Prop = {!!}

  is-frame-Meet-Suplattice : UU (l1 ⊔ lsuc l2)
  is-frame-Meet-Suplattice = {!!}

  is-prop-is-frame-Meet-Suplattice : is-prop is-frame-Meet-Suplattice
  is-prop-is-frame-Meet-Suplattice = {!!}
```

### Frames

```agda
Frame : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Frame = {!!}

module _
  {l1 l2 : Level} (A : Frame l1 l2)
  where

  meet-suplattice-Frame : Meet-Suplattice l1 l2
  meet-suplattice-Frame = {!!}

  meet-semilattice-Frame : Meet-Semilattice l1
  meet-semilattice-Frame = {!!}

  suplattice-Frame : Suplattice l1 l1 l2
  suplattice-Frame = {!!}

  poset-Frame : Poset l1 l1
  poset-Frame = {!!}

  set-Frame : Set l1
  set-Frame = {!!}

  type-Frame : UU l1
  type-Frame = {!!}

  is-set-type-Frame : is-set type-Frame
  is-set-type-Frame = {!!}

  leq-Frame-Prop : (x y : type-Frame) → Prop l1
  leq-Frame-Prop = {!!}

  leq-Frame : (x y : type-Frame) → UU l1
  leq-Frame = {!!}

  is-prop-leq-Frame : (x y : type-Frame) → is-prop (leq-Frame x y)
  is-prop-leq-Frame = {!!}

  refl-leq-Frame : is-reflexive leq-Frame
  refl-leq-Frame = {!!}

  antisymmetric-leq-Frame : is-antisymmetric leq-Frame
  antisymmetric-leq-Frame = {!!}

  transitive-leq-Frame : is-transitive leq-Frame
  transitive-leq-Frame = {!!}

  meet-Frame : type-Frame → type-Frame → type-Frame
  meet-Frame = {!!}

  is-greatest-binary-lower-bound-meet-Frame :
    (x y : type-Frame) →
    is-greatest-binary-lower-bound-Poset poset-Frame x y (meet-Frame x y)
  is-greatest-binary-lower-bound-meet-Frame = {!!}

  associative-meet-Frame :
    (x y z : type-Frame) →
    meet-Frame (meet-Frame x y) z ＝ meet-Frame x (meet-Frame y z)
  associative-meet-Frame = {!!}

  commutative-meet-Frame :
    (x y : type-Frame) → meet-Frame x y ＝ meet-Frame y x
  commutative-meet-Frame = {!!}

  idempotent-meet-Frame :
    (x : type-Frame) → meet-Frame x x ＝ x
  idempotent-meet-Frame = {!!}

  is-suplattice-Frame :
    is-suplattice-Poset l2 poset-Frame
  is-suplattice-Frame = {!!}

  sup-Frame : {I : UU l2} → (I → type-Frame) → type-Frame
  sup-Frame = {!!}

  is-least-upper-bound-sup-Frame :
    {I : UU l2} (x : I → type-Frame) →
    is-least-upper-bound-family-of-elements-Poset poset-Frame x (sup-Frame x)
  is-least-upper-bound-sup-Frame = {!!}

  distributive-meet-sup-Frame :
    distributive-law-Meet-Suplattice meet-suplattice-Frame
  distributive-meet-sup-Frame = {!!}
```
