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
      element :
        {X : system.type A} {Y : fibered-system.type B X}
        {Z : fibered-system.type C X} {x : system.element A X}
        (W : type Y Z) (y : fibered-system.element B Y x)
        (z : fibered-system.element C Z x) → UU l8
      slice :
        {X : system.type A} {Y : fibered-system.type B X}
        {Z : fibered-system.type C X} → type Y Z →
        bifibered-system l7 l8
          ( fibered-system.slice B Y)
          ( fibered-system.slice C Z)

  total-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) →
    fibered-system (l5 ⊔ l7) (l6 ⊔ l8) (total-system A B)
  fibered-system.type (total-fibered-system {C = C} D) X = {!!}

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
      element :
        {X : system.type A} {Y : fibered-system.type B X} →
        {x : system.element A X} (y : fibered-system.element B Y x) →
        bifibered-system.element D
          ( type Y)
          ( y)
          ( section-system.element f x)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        section-fibered-system
          ( section-system.slice f X)
          ( bifibered-system.slice D (type Y))

  total-section-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    {D : bifibered-system l7 l8 B C} {f : section-system C}
    (g : section-fibered-system f D) →
    section-system (total-fibered-system D)
  section-system.type (total-section-system {f = f} g) (pair X Y) = {!!}
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
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-weakening
          ( fibered-system.slice B Y)
          ( weakening.slice W X)

  record preserves-fibered-weakening
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {C : system l5 l6} {D : fibered-system l7 l8 C}
    {WA : weakening A} {WC : weakening C}
    (WB : fibered-weakening B WA) (WD : fibered-weakening D WC)
    {f : hom-system A C} (Wf : preserves-weakening WA WC f)
    (g : hom-fibered-system f B D) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        htpy-hom-fibered-system
          ( preserves-weakening.type Wf X)
          ( comp-hom-fibered-system
            ( section-fibered-system.slice g Y)
            ( fibered-weakening.type WB Y))
          ( comp-hom-fibered-system
            ( fibered-weakening.type WD
              ( section-fibered-system.type g Y))
            ( g))
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        preserves-fibered-weakening
          ( fibered-weakening.slice WB Y)
          ( fibered-weakening.slice WD (section-fibered-system.type g Y))
          ( preserves-weakening.slice Wf X)
          ( section-fibered-system.slice g Y)
```

### Substitution structures on fibered systems

```agda
  record fibered-substitution
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
    (S : substitution A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        hom-fibered-system
          ( substitution.type S x)
          ( fibered-system.slice B Y)
          ( B)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-substitution
          ( fibered-system.slice B Y)
          ( substitution.slice S X)

  record preserves-fibered-substitution
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : system l5 l6}
    {D : fibered-system l7 l8 C} {SA : substitution A} {SC : substitution C}
    (SB : fibered-substitution B SA) (SD : fibered-substitution D SC)
    {f : hom-system A C} (Sf : preserves-substitution SA SC f)
    (g : hom-fibered-system f B D) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        htpy-hom-fibered-system
          ( preserves-substitution.type Sf x)
          ( comp-hom-fibered-system
            ( g)
            ( fibered-substitution.type SB y))
          ( comp-hom-fibered-system
            ( fibered-substitution.type SD
              ( section-fibered-system.element g y))
            ( section-fibered-system.slice g Y))
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        preserves-fibered-substitution
          ( fibered-substitution.slice SB Y)
          ( fibered-substitution.slice SD
            ( section-fibered-system.type g Y))
          ( preserves-substitution.slice Sf X)
          ( section-fibered-system.slice g Y)
```

### Generic element structures on fibered systems equipped with a weakening structure

We define what it means for a fibered system equipped with fibered weakening
structure over a system equipped with weakening structure and the structure of
generic elements to be equipped with generic elements.

```agda
  record fibered-generic-element
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} (W : fibered-weakening B WA)
    (δ : generic-element WA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-system.element
          ( fibered-system.slice B Y)
          ( section-fibered-system.type (fibered-weakening.type W Y) Y)
          ( generic-element.type δ X)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-generic-element
          ( fibered-weakening.slice W Y)
          ( generic-element.slice δ X)

  record preserves-fibered-generic-element
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {C : system l5 l6} {D : fibered-system l7 l8 C}
    {WA : weakening A} {WC : weakening C}
    {WB : fibered-weakening B WA} {WD : fibered-weakening D WC}
    {δA : generic-element WA} {δC : generic-element WC}
    (δB : fibered-generic-element WB δA) (δD : fibered-generic-element WD δC)
    {f : hom-system A C} {Wf : preserves-weakening WA WC f}
    (δf : preserves-generic-element δA δC Wf)
    {g : hom-fibered-system f B D}
    (Wg : preserves-fibered-weakening WB WD Wf g) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        Id
          ( double-tr
            ( λ Z u v →
              fibered-system.element
              ( fibered-system.slice D
                ( section-fibered-system.type g Y))
              {Z} u v)
            ( section-system.type (preserves-weakening.type Wf X) X)
            ( section-fibered-system.type
              ( preserves-fibered-weakening.type Wg Y) Y)
            ( preserves-generic-element.type δf X)
            ( section-fibered-system.element
              ( section-fibered-system.slice g Y)
              ( fibered-generic-element.type δB Y)))
          ( fibered-generic-element.type δD
            ( section-fibered-system.type g Y))
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        preserves-fibered-generic-element
          ( fibered-generic-element.slice δB Y)
          ( fibered-generic-element.slice δD
            ( section-fibered-system.type g Y))
          ( preserves-generic-element.slice δf X)
          ( preserves-fibered-weakening.slice Wg Y)
```

### Fibered dependent type theories

```agda
  record fibered-weakening-preserves-weakening
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} (WWA : weakening-preserves-weakening WA)
    (W : fibered-weakening B WA) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        preserves-fibered-weakening
          ( W)
          ( fibered-weakening.slice W Y)
          ( weakening-preserves-weakening.type WWA X)
          ( fibered-weakening.type W Y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-weakening-preserves-weakening
          ( weakening-preserves-weakening.slice WWA X)
          ( fibered-weakening.slice W Y)

  record fibered-substitution-preserves-substitution
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {SA : substitution A} (SSA : substitution-preserves-substitution SA)
    (S : fibered-substitution B SA) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        preserves-fibered-substitution
          ( fibered-substitution.slice S Y)
          ( S)
          ( substitution-preserves-substitution.type SSA x)
          ( fibered-substitution.type S y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-substitution-preserves-substitution
          ( substitution-preserves-substitution.slice SSA X)
          ( fibered-substitution.slice S Y)

  record fibered-weakening-preserves-substitution
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {SA : substitution A}
    (WSA : weakening-preserves-substitution SA WA)
    (W : fibered-weakening B WA) (S : fibered-substitution B SA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        preserves-fibered-substitution
          ( S)
          ( fibered-substitution.slice S Y)
          ( weakening-preserves-substitution.type WSA X)
          ( fibered-weakening.type W Y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-weakening-preserves-substitution
          ( weakening-preserves-substitution.slice WSA X)
          ( fibered-weakening.slice W Y)
          ( fibered-substitution.slice S Y)

  record fibered-substitution-preserves-weakening
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {SA : substitution A}
    (SWA : substitution-preserves-weakening WA SA)
    (W : fibered-weakening B WA) (S : fibered-substitution B SA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        preserves-fibered-weakening
          ( fibered-weakening.slice W Y)
          ( W)
          ( substitution-preserves-weakening.type SWA x)
          ( fibered-substitution.type S y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-substitution-preserves-weakening
          ( substitution-preserves-weakening.slice SWA X)
          ( fibered-weakening.slice W Y)
          ( fibered-substitution.slice S Y)

  record fibered-weakening-preserves-generic-element
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {δA : generic-element WA}
    {WWA : weakening-preserves-weakening WA}
    (WδA : weakening-preserves-generic-element WA WWA δA)
    {W : fibered-weakening B WA}
    (WWB : fibered-weakening-preserves-weakening WWA W)
    (δ : fibered-generic-element W δA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        preserves-fibered-generic-element
          ( δ)
          ( fibered-generic-element.slice δ Y)
          ( weakening-preserves-generic-element.type WδA X)
          ( fibered-weakening-preserves-weakening.type WWB Y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-weakening-preserves-generic-element
          ( weakening-preserves-generic-element.slice WδA X)
          ( fibered-weakening-preserves-weakening.slice WWB Y)
          ( fibered-generic-element.slice δ Y)

  record fibered-substitution-preserves-generic-element
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {SA : substitution A} {δA : generic-element WA}
    {SWA : substitution-preserves-weakening WA SA}
    (SδA : substitution-preserves-generic-element WA δA SA SWA)
    {WB : fibered-weakening B WA} {SB : fibered-substitution B SA}
    (SWB : fibered-substitution-preserves-weakening SWA WB SB)
    (δB : fibered-generic-element WB δA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        preserves-fibered-generic-element
          ( fibered-generic-element.slice δB Y)
          ( δB)
          ( substitution-preserves-generic-element.type SδA x)
          ( fibered-substitution-preserves-weakening.type SWB y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-substitution-preserves-generic-element
          ( substitution-preserves-generic-element.slice SδA X)
          ( fibered-substitution-preserves-weakening.slice SWB Y)
          ( fibered-generic-element.slice δB Y)

  record fibered-substitution-cancels-weakening
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {SA : substitution A}
    (S!WA : substitution-cancels-weakening WA SA)
    (WB : fibered-weakening B WA) (SB : fibered-substitution B SA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        htpy-hom-fibered-system
          ( substitution-cancels-weakening.type S!WA x)
          ( comp-hom-fibered-system
            ( fibered-substitution.type SB y)
            ( fibered-weakening.type WB Y))
          ( id-hom-fibered-system B)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-substitution-cancels-weakening
          ( substitution-cancels-weakening.slice S!WA X)
          ( fibered-weakening.slice WB Y)
          ( fibered-substitution.slice SB Y)

  record fibered-generic-element-is-identity
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {SA : substitution A} {δA : generic-element WA}
    (S!WA : substitution-cancels-weakening WA SA)
    (δidA : generic-element-is-identity WA SA δA S!WA)
    {WB : fibered-weakening B WA} {SB : fibered-substitution B SA}
    (δB : fibered-generic-element WB δA)
    (S!WB : fibered-substitution-cancels-weakening S!WA WB SB) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} {Y : fibered-system.type B X}
        {x : system.element A X} (y : fibered-system.element B Y x) →
        Id ( double-tr
              ( λ α β γ → fibered-system.element B {X = α} β γ)
              ( section-system.type
                ( substitution-cancels-weakening.type S!WA x)
                ( X))
              ( section-fibered-system.type
                ( fibered-substitution-cancels-weakening.type S!WB y)
                ( Y))
              ( generic-element-is-identity.type δidA x)
              ( section-fibered-system.element
                ( fibered-substitution.type SB y)
                ( fibered-generic-element.type δB Y)))
            ( y)
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-generic-element-is-identity
          ( substitution-cancels-weakening.slice S!WA X)
          ( generic-element-is-identity.slice δidA X)
          ( fibered-generic-element.slice δB Y)
          ( fibered-substitution-cancels-weakening.slice S!WB Y)

  record fibered-substitution-by-generic-element
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {SA : substitution A} {δA : generic-element WA}
    (Sδ! : substitution-by-generic-element WA SA δA)
    {WB : fibered-weakening B WA} (SB : fibered-substitution B SA)
    (δB : fibered-generic-element WB δA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (Y : fibered-system.type B X) →
        htpy-hom-fibered-system
          ( substitution-by-generic-element.type Sδ! X)
          ( comp-hom-fibered-system
            ( fibered-substitution.type
              ( fibered-substitution.slice SB Y)
              ( fibered-generic-element.type δB Y))
            ( fibered-weakening.type
              ( fibered-weakening.slice WB Y)
              ( section-fibered-system.type
                ( fibered-weakening.type WB Y)
                ( Y))))
          ( id-hom-fibered-system (fibered-system.slice B Y))
      slice :
        {X : system.type A} (Y : fibered-system.type B X) →
        fibered-substitution-by-generic-element
          ( substitution-by-generic-element.slice Sδ! X)
          ( fibered-substitution.slice SB Y)
          ( fibered-generic-element.slice δB Y)
```

---

## Fibered dependent type theories

```agda
  record fibered-type-theory
    {l1 l2 : Level} (l3 l4 : Level) (A : type-theory l1 l2) :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
    where
    coinductive
    field
      sys : fibered-system l3 l4 (type-theory.sys A)
      W : fibered-weakening sys (type-theory.W A)
      S : fibered-substitution sys (type-theory.S A)
      δ : fibered-generic-element W (type-theory.δ A)
      WW : fibered-weakening-preserves-weakening (type-theory.WW A) W
      SS : fibered-substitution-preserves-substitution (type-theory.SS A) S
      WS : fibered-weakening-preserves-substitution (type-theory.WS A) W S
      SW : fibered-substitution-preserves-weakening (type-theory.SW A) W S
      Wδ : fibered-weakening-preserves-generic-element (type-theory.Wδ A) WW δ
      Sδ :
        fibered-substitution-preserves-generic-element (type-theory.Sδ A) SW δ
      S!W : fibered-substitution-cancels-weakening (type-theory.S!W A) W S
      δid : fibered-generic-element-is-identity
              (type-theory.S!W A) (type-theory.δid A) δ S!W
      Sδ! : fibered-substitution-by-generic-element (type-theory.Sδ! A) S δ

{-
  total-type-theory :
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
    (B : fibered-type-theory l3 l4 A) → type-theory (l1 ⊔ l3) (l2 ⊔ l4)
  type-theory.sys (total-type-theory {A = A} B) = {!!}
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
