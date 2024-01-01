# Order preserving maps on posets

```agda
module order-theory.order-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.order-preserving-maps-preorders
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two posets is siad to be
**order preserving** if `x ≤ y` in `P` implies `f x ≤ f y` in `Q`.

## Definition

### Order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-order-Poset-Prop :
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-order-Poset-Prop = {!!}

  preserves-order-Poset :
    (type-Poset P → type-Poset Q) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-order-Poset = {!!}

  is-prop-preserves-order-Poset :
    (f : type-Poset P → type-Poset Q) → is-prop (preserves-order-Poset f)
  is-prop-preserves-order-Poset = {!!}

  hom-set-Poset : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-Poset = {!!}

  hom-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Poset = {!!}

  map-hom-Poset : hom-Poset → type-Poset P → type-Poset Q
  map-hom-Poset = {!!}

  preserves-order-map-hom-Poset :
    (f : hom-Poset) → preserves-order-Poset (map-hom-Poset f)
  preserves-order-map-hom-Poset = {!!}
```

### Homotopies of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-hom-Poset : (f g : hom-Poset P Q) → UU (l1 ⊔ l3)
  htpy-hom-Poset = {!!}

  refl-htpy-hom-Poset : (f : hom-Poset P Q) → htpy-hom-Poset f f
  refl-htpy-hom-Poset = {!!}

  htpy-eq-hom-Poset :
    (f g : hom-Poset P Q) → Id f g → htpy-hom-Poset f g
  htpy-eq-hom-Poset = {!!}

  is-torsorial-htpy-hom-Poset :
    (f : hom-Poset P Q) → is-torsorial (htpy-hom-Poset f)
  is-torsorial-htpy-hom-Poset = {!!}

  is-equiv-htpy-eq-hom-Poset :
    (f g : hom-Poset P Q) → is-equiv (htpy-eq-hom-Poset f g)
  is-equiv-htpy-eq-hom-Poset = {!!}

  extensionality-hom-Poset :
    (f g : hom-Poset P Q) → Id f g ≃ htpy-hom-Poset f g
  extensionality-hom-Poset = {!!}

  eq-htpy-hom-Poset :
    (f g : hom-Poset P Q) → htpy-hom-Poset f g → Id f g
  eq-htpy-hom-Poset = {!!}

  is-prop-htpy-hom-Poset :
    (f g : hom-Poset P Q) → is-prop (htpy-hom-Poset f g)
  is-prop-htpy-hom-Poset f g = {!!}
```

### The identity order preserving map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preserves-order-id-Poset :
    preserves-order-Poset P P (id {A = type-Poset P})
  preserves-order-id-Poset = {!!}

  id-hom-Poset : hom-Poset P P
  id-hom-Poset = {!!}
```

### Composing order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  preserves-order-comp-Poset :
    (g : hom-Poset Q R) (f : hom-Poset P Q) →
    preserves-order-Poset P R
      ( map-hom-Poset Q R g ∘ map-hom-Poset P Q f)
  preserves-order-comp-Poset = {!!}

  comp-hom-Poset :
    (g : hom-Poset Q R) (f : hom-Poset P Q) → hom-Poset P R
  comp-hom-Poset = {!!}
```

### Unit laws for composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-hom-Poset :
    (f : hom-Poset P Q) →
    Id ( comp-hom-Poset P Q Q (id-hom-Poset Q) f) f
  left-unit-law-comp-hom-Poset = {!!}

  right-unit-law-comp-hom-Poset :
    (f : hom-Poset P Q) →
    Id (comp-hom-Poset P P Q f (id-hom-Poset P)) f
  right-unit-law-comp-hom-Poset = {!!}
```

### Associativity of composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  where

  associative-comp-hom-Poset :
    (h : hom-Poset R S) (g : hom-Poset Q R) (f : hom-Poset P Q) →
    comp-hom-Poset P Q S (comp-hom-Poset Q R S h g) f ＝
    comp-hom-Poset P R S h (comp-hom-Poset P Q R g f)
  associative-comp-hom-Poset = {!!}

  inv-associative-comp-hom-Poset :
    (h : hom-Poset R S) (g : hom-Poset Q R) (f : hom-Poset P Q) →
    comp-hom-Poset P R S h (comp-hom-Poset P Q R g f) ＝
    comp-hom-Poset P Q S (comp-hom-Poset Q R S h g) f
  inv-associative-comp-hom-Poset = {!!}
```
