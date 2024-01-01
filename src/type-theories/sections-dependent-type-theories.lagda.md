# Sections of dependent type theories

```agda
{-# OPTIONS --guardedness #-}

module type-theories.sections-dependent-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import type-theories.dependent-type-theories
open import type-theories.fibered-dependent-type-theories
```

</details>

```agda
open dependent
open fibered

module sections-dtt where

  precomp-fibered-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4}
    (C : fibered-system l5 l6 B) (f : hom-system A B) →
    fibered-system l5 l6 A
  precomp-fibered-system = {!!}

  precomp-section-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4}
    {C : fibered-system l5 l6 B}
    (g : section-system C) (f : hom-system A B) →
    section-system (precomp-fibered-system C f)
  precomp-section-system = {!!}

  transpose-bifibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) →
    bifibered-system l7 l8 C B
  transpose-bifibered-system = {!!}

  postcomp-section-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {C : system l5 l6} {D : fibered-system l7 l8 C}
    {f : hom-system A C} (g : hom-fibered-system f B D)
    (h : section-system B) → section-system (precomp-fibered-system D f)
  postcomp-section-system = {!!}

  record preserves-weakening-section-system
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} (WB : fibered-weakening B WA)
    (f : section-system B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        htpy-section-system
          ( precomp-section-system
            ( section-system.slice f X)
            ( weakening.type WA X))
          ( postcomp-section-system
            ( fibered-weakening.type WB (section-system.type f X))
            ( f))
      slice :
        (X : system.type A) →
        preserves-weakening-section-system
          ( fibered-weakening.slice WB (section-system.type f X))
          ( section-system.slice f X)

  record preserves-substitution-section-system
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {SA : substitution A} (SB : fibered-substitution B SA)
    (f : section-system B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        htpy-section-system
          ( precomp-section-system f (substitution.type SA x))
          ( postcomp-section-system
            ( fibered-substitution.type SB (section-system.element f x))
            ( section-system.slice f X))
      slice :
        (X : system.type A) →
        preserves-substitution-section-system
          ( fibered-substitution.slice SB (section-system.type f X))
          ( section-system.slice f X)

  record preserves-generic-element-section-system
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {δA : generic-element WA}
    {WB : fibered-weakening B WA} (δB : fibered-generic-element WB δA)
    {f : section-system B} (Wf : preserves-weakening-section-system WB f) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        Id
          ( tr
            ( λ t →
              fibered-system.element
                ( fibered-system.slice B (section-system.type f X))
                ( t)
                ( generic-element.type δA X))
            ( section-system.type
              ( preserves-weakening-section-system.type Wf X)
              ( X))
            ( section-system.element
              ( section-system.slice f X)
              ( generic-element.type δA X)))
            ( fibered-generic-element.type δB (section-system.type f X))
      slice :
        (X : system.type A) →
        preserves-generic-element-section-system
          ( fibered-generic-element.slice δB (section-system.type f X))
          ( preserves-weakening-section-system.slice Wf X)

  record section-type-theory
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2}
    (B : fibered-type-theory l3 l4 A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    field
      sys : section-system (fibered-type-theory.sys B)
      W :
        preserves-weakening-section-system
          ( fibered-type-theory.W B)
          ( sys)
      S :
        preserves-substitution-section-system
          ( fibered-type-theory.S B)
          ( sys)
      δ :
        preserves-generic-element-section-system
          ( fibered-type-theory.δ B)
          ( W)
```
