# Fibered dependent type theories

```agda
{-# OPTIONS --guardedness #-}

module type-theories.fibered-dependent-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import type-theories.dependent-type-theories
```

</details>

## Bifibered systems

```agda
open dependent
module fibered where

  record bifibered-system
    {l1 l2 l3 l4 l5 l6 : Level} (l7 l8 : Level) {A : system l1 l2}
    (B : fibered-system l3 l4 A) (C : fibered-system l5 l6 A) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ lsuc l7 ⊔ lsuc l8)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X)
        (Z : fibered-system.type C X) → UU l7
      type = {!!}

  record section-fibered-system
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (f : section-system C) (D : bifibered-system l7 l8 B C) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        bifibered-system.type D Y (section-system.type f X)
      type = {!!}
```

### Homotopies of sections of fibered systems

```agda
  double-tr :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
    (D : (x : A) → B x → C x → UU l4) {x y : A} (p : Id x y)
    {u : B x} {u' : B y} (q : Id (tr B p u) u') {v : C x} {v' : C y}
    (r : Id (tr C p v) v') → D x u v → D y u' v'
  double-tr = {!!}

  tr-bifibered-system-slice :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) {X : system.type A}
    (Y : fibered-system.type B X) {Z Z' : fibered-system.type C X}
    {d : bifibered-system.type D Y Z} {d' : bifibered-system.type D Y Z'}
    (p : Id Z Z') (q : Id (tr (bifibered-system.type D Y) p d) d') →
    Id
      ( tr
        ( bifibered-system l7 l8 (fibered-system.slice B Y))
        ( ap (fibered-system.slice C) p)
        ( bifibered-system.slice D d))
      ( bifibered-system.slice D (tr (bifibered-system.type D Y) p d))
  tr-bifibered-system-slice = {!!}

  Eq-bifibered-system' :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C C' : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) (D' : bifibered-system l7 l8 B C')
    (α : Id C C') (β : Id (tr (bifibered-system l7 l8 B) α D) D')
    (f : section-system C) (f' : section-system C')
    (g : section-fibered-system f D) (g' : section-fibered-system f' D') →
    bifibered-system l7 l8 B (Eq-fibered-system' α f f')
  Eq-bifibered-system' = {!!}

  htpy-section-fibered-system' :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C C' : fibered-system l5 l6 A}
    {D : bifibered-system l7 l8 B C} {D' : bifibered-system l7 l8 B C'}
    {f : section-system C} {f' : section-system C'}
    {α : Id C C'} (β : Id (tr (bifibered-system l7 l8 B) α D) D')
    (H : htpy-section-system' α f f')
    (g : section-fibered-system f D) (h : section-fibered-system f' D') →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
  htpy-section-fibered-system' = {!!}

  htpy-section-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    {D : bifibered-system l7 l8 B C} {f f' : section-system C}
    (H : htpy-section-system f f')
    (g : section-fibered-system f D) (h : section-fibered-system f' D) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
  htpy-section-fibered-system = {!!}
```

### Morphisms of fibered systems

```agda
  constant-bifibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    (B : fibered-system l3 l4 A) {C : system l5 l6}
    (D : fibered-system l7 l8 C) →
    bifibered-system l7 l8 B (constant-fibered-system A C)
  constant-bifibered-system = {!!}

  hom-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2} {A' : system l3 l4}
    (f : hom-system A A') (B : fibered-system l5 l6 A)
    (B' : fibered-system l7 l8 A') → UU (l1 ⊔ l2 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
  hom-fibered-system = {!!}

  id-hom-fibered-system :
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} (B : fibered-system l3 l4 A) →
    hom-fibered-system (id-hom-system A) B B
  id-hom-fibered-system = {!!}

  comp-hom-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Level}
    {A : system l1 l2} {B : system l3 l4} {C : system l5 l6}
    {g : hom-system B C} {f : hom-system A B}
    {D : fibered-system l7 l8 A} {E : fibered-system l9 l10 B}
    {F : fibered-system l11 l12 C}
    (k : hom-fibered-system g E F) (h : hom-fibered-system f D E) →
    hom-fibered-system (comp-hom-system g f) D F
  comp-hom-fibered-system = {!!}

  htpy-hom-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : system l5 l6} {D : fibered-system l7 l8 C}
    {f f' : hom-system A C} (H : htpy-hom-system f f')
    (g : hom-fibered-system f B D) (g' : hom-fibered-system f' B D) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
  htpy-hom-fibered-system = {!!}
```

### Weakening structure on fibered systems

```agda
  record fibered-weakening
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
    (W : weakening A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        hom-fibered-system
          ( weakening.type W X)
          ( B)
          ( fibered-system.slice B Y)
      type = {!!}
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-generic-element-is-identity
          ( substitution-cancels-weakening.slice S!WA X)
          ( generic-element-is-identity.slice δidA X)
          ( fibered-generic-element.slice δB Y)
      slice = {!!}
-}

{-
  slice-fibered-type-theory
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
-}
```

---

## Subtype theories

```agda
{-
  record is-subtype-theory
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
    (B : fibered-type-theory l3 l4 A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type  :
        ( (X : system.type (type-theory.sys A)) →
          is-prop (fibered-system.type (fibered-type-theory.sys B) X)) ×
        ( (X : system.type (type-theory.sys A))
          ( Y : fibered-system.type (fibered-type-theory.sys B) X)
          ( x : system.element (type-theory.sys A) X) →
          is-prop (fibered-system.element (fibered-type-theory.sys B) Y x))
      slice :
        (X : system.type (type-theory.sys A)) →
        is-subtype-theory (slice-fibered-type-theory B X)
-}
```
