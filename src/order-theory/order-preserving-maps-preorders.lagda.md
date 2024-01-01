# Order preserving maps on preorders

```agda
module order-theory.order-preserving-maps-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two preorders is said to be
**order preserving** if `x ≤ y` in `P` implies `f x ≤ f y` in `Q`.

## Definition

### Order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  preserves-order-Preorder-Prop :
    (type-Preorder P → type-Preorder Q) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-order-Preorder-Prop f = {!!}

  preserves-order-Preorder :
    (type-Preorder P → type-Preorder Q) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-order-Preorder f = {!!}

  is-prop-preserves-order-Preorder :
    (f : type-Preorder P → type-Preorder Q) →
    is-prop (preserves-order-Preorder f)
  is-prop-preserves-order-Preorder f = {!!}

  hom-Preorder : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Preorder = {!!}

  map-hom-Preorder : hom-Preorder → type-Preorder P → type-Preorder Q
  map-hom-Preorder = {!!}

  preserves-order-map-hom-Preorder :
    (f : hom-Preorder) → preserves-order-Preorder (map-hom-Preorder f)
  preserves-order-map-hom-Preorder = {!!}
```

### Homotopies of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  htpy-hom-Preorder : (f g : hom-Preorder P Q) → UU (l1 ⊔ l3)
  htpy-hom-Preorder f g = {!!}

  refl-htpy-hom-Preorder : (f : hom-Preorder P Q) → htpy-hom-Preorder f f
  refl-htpy-hom-Preorder f = {!!}

  htpy-eq-hom-Preorder :
    (f g : hom-Preorder P Q) → Id f g → htpy-hom-Preorder f g
  htpy-eq-hom-Preorder f .f refl = {!!}

  is-torsorial-htpy-hom-Preorder :
    (f : hom-Preorder P Q) → is-torsorial (htpy-hom-Preorder f)
  is-torsorial-htpy-hom-Preorder f = {!!}

  is-equiv-htpy-eq-hom-Preorder :
    (f g : hom-Preorder P Q) → is-equiv (htpy-eq-hom-Preorder f g)
  is-equiv-htpy-eq-hom-Preorder f = {!!}

  extensionality-hom-Preorder :
    (f g : hom-Preorder P Q) → Id f g ≃ htpy-hom-Preorder f g
  pr1 (extensionality-hom-Preorder f g) = {!!}

  eq-htpy-hom-Preorder :
    (f g : hom-Preorder P Q) → htpy-hom-Preorder f g → Id f g
  eq-htpy-hom-Preorder f g = {!!}
```

### The identity order preserving map

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  preserves-order-id-Preorder :
    preserves-order-Preorder P P (id {A = type-Preorder P})
  preserves-order-id-Preorder x y = {!!}

  id-hom-Preorder : hom-Preorder P P
  pr1 id-hom-Preorder = {!!}
```

### Composing order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4) (R : Preorder l5 l6)
  where

  preserves-order-comp-Preorder :
    (g : hom-Preorder Q R) (f : hom-Preorder P Q) →
    preserves-order-Preorder P R
      ( map-hom-Preorder Q R g ∘ map-hom-Preorder P Q f)
  preserves-order-comp-Preorder g f x y H = {!!}

  comp-hom-Preorder :
    (g : hom-Preorder Q R) (f : hom-Preorder P Q) →
    hom-Preorder P R
  pr1 (comp-hom-Preorder g f) = {!!}
```

### Unit laws for composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  left-unit-law-comp-hom-Preorder :
    (f : hom-Preorder P Q) →
    Id ( comp-hom-Preorder P Q Q (id-hom-Preorder Q) f) f
  left-unit-law-comp-hom-Preorder f = {!!}

  right-unit-law-comp-hom-Preorder :
    (f : hom-Preorder P Q) →
    Id (comp-hom-Preorder P P Q f (id-hom-Preorder P)) f
  right-unit-law-comp-hom-Preorder f = {!!}
```

### Associativity of composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (R : Preorder l5 l6) (S : Preorder l7 l8)
  (h : hom-Preorder R S)
  (g : hom-Preorder Q R)
  (f : hom-Preorder P Q)
  where

  associative-comp-hom-Preorder :
    comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f ＝
    comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f)
  associative-comp-hom-Preorder = {!!}

  inv-associative-comp-hom-Preorder :
    comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f) ＝
    comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f
  inv-associative-comp-hom-Preorder = {!!}
```
