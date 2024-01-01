# Fibers of maps

```agda
module foundation-core.fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given a map `f : A → B` and an element `b : B`, the **fiber** of `f` at `b` is
the preimage of `f` at `b`. In other words, it consists of the elements `a : A`
equipped with an [identification](foundation-core.identity-types.md) `f a ＝ b`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber : UU (l1 ⊔ l2)
  fiber = {!!}

  fiber' : UU (l1 ⊔ l2)
  fiber' = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {b : B}
  where

  inclusion-fiber : fiber f b → A
  inclusion-fiber = {!!}

  compute-value-inclusion-fiber : (y : fiber f b) → f (inclusion-fiber y) ＝ b
  compute-value-inclusion-fiber = {!!}
```

## Properties

### Characterization of the identity types of the fibers of a map

#### The case of `fiber`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber : fiber f b → fiber f b → UU (l1 ⊔ l2)
  Eq-fiber s t = {!!}

  refl-Eq-fiber : (s : fiber f b) → Eq-fiber s s
  pr1 (refl-Eq-fiber s) = {!!}

  Eq-eq-fiber : {s t : fiber f b} → s ＝ t → Eq-fiber s t
  Eq-eq-fiber {s} refl = {!!}

  eq-Eq-fiber-uncurry : {s t : fiber f b} → Eq-fiber s t → s ＝ t
  eq-Eq-fiber-uncurry (refl , refl) = {!!}

  eq-Eq-fiber :
    {s t : fiber f b} (α : pr1 s ＝ pr1 t) → ap f α ∙ pr2 t ＝ pr2 s → s ＝ t
  eq-Eq-fiber = {!!}

  is-section-eq-Eq-fiber :
    {s t : fiber f b} → Eq-eq-fiber {s} {t} ∘ eq-Eq-fiber-uncurry {s} {t} ~ id
  is-section-eq-Eq-fiber = {!!}

  is-retraction-eq-Eq-fiber :
    {s t : fiber f b} → eq-Eq-fiber-uncurry {s} {t} ∘ Eq-eq-fiber {s} {t} ~ id
  is-retraction-eq-Eq-fiber = {!!}

  abstract
    is-equiv-Eq-eq-fiber : {s t : fiber f b} → is-equiv (Eq-eq-fiber {s} {t})
    is-equiv-Eq-eq-fiber = {!!}

  equiv-Eq-eq-fiber : {s t : fiber f b} → (s ＝ t) ≃ Eq-fiber s t
  pr1 equiv-Eq-eq-fiber = {!!}

  abstract
    is-equiv-eq-Eq-fiber :
      {s t : fiber f b} → is-equiv (eq-Eq-fiber-uncurry {s} {t})
    is-equiv-eq-Eq-fiber = {!!}

  equiv-eq-Eq-fiber : {s t : fiber f b} → Eq-fiber s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber = {!!}

  compute-ap-inclusion-fiber-eq-Eq-fiber :
    {s t : fiber f b} (α : pr1 s ＝ pr1 t) (β : ap f α ∙ pr2 t ＝ pr2 s) →
    ap (inclusion-fiber f) (eq-Eq-fiber α β) ＝ α
  compute-ap-inclusion-fiber-eq-Eq-fiber = {!!}
```

#### The case of `fiber'`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber' : fiber' f b → fiber' f b → UU (l1 ⊔ l2)
  Eq-fiber' s t = {!!}

  refl-Eq-fiber' : (s : fiber' f b) → Eq-fiber' s s
  pr1 (refl-Eq-fiber' s) = {!!}

  Eq-eq-fiber' : {s t : fiber' f b} → s ＝ t → Eq-fiber' s t
  Eq-eq-fiber' {s} refl = {!!}

  eq-Eq-fiber-uncurry' : {s t : fiber' f b} → Eq-fiber' s t → s ＝ t
  eq-Eq-fiber-uncurry' {x , p} (refl , refl) = {!!}

  eq-Eq-fiber' :
    {s t : fiber' f b} (α : pr1 s ＝ pr1 t) → pr2 t ＝ pr2 s ∙ ap f α → s ＝ t
  eq-Eq-fiber' = {!!}

  is-section-eq-Eq-fiber' :
    {s t : fiber' f b} →
    Eq-eq-fiber' {s} {t} ∘ eq-Eq-fiber-uncurry' {s} {t} ~ id
  is-section-eq-Eq-fiber' = {!!}

  is-retraction-eq-Eq-fiber' :
    {s t : fiber' f b} →
    eq-Eq-fiber-uncurry' {s} {t} ∘ Eq-eq-fiber' {s} {t} ~ id
  is-retraction-eq-Eq-fiber' = {!!}

  abstract
    is-equiv-Eq-eq-fiber' :
      {s t : fiber' f b} → is-equiv (Eq-eq-fiber' {s} {t})
    is-equiv-Eq-eq-fiber' = {!!}

  equiv-Eq-eq-fiber' : {s t : fiber' f b} → (s ＝ t) ≃ Eq-fiber' s t
  pr1 equiv-Eq-eq-fiber' = {!!}

  abstract
    is-equiv-eq-Eq-fiber' :
      {s t : fiber' f b} → is-equiv (eq-Eq-fiber-uncurry' {s} {t})
    is-equiv-eq-Eq-fiber' = {!!}

  equiv-eq-Eq-fiber' : {s t : fiber' f b} → Eq-fiber' s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber' = {!!}
```

### `fiber f y` and `fiber' f y` are equivalent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  map-equiv-fiber : fiber f y → fiber' f y
  pr1 (map-equiv-fiber (x , refl)) = {!!}

  map-inv-equiv-fiber : fiber' f y → fiber f y
  pr1 (map-inv-equiv-fiber (x , refl)) = {!!}

  is-section-map-inv-equiv-fiber : map-equiv-fiber ∘ map-inv-equiv-fiber ~ id
  is-section-map-inv-equiv-fiber (x , refl) = {!!}

  is-retraction-map-inv-equiv-fiber : map-inv-equiv-fiber ∘ map-equiv-fiber ~ id
  is-retraction-map-inv-equiv-fiber (x , refl) = {!!}

  is-equiv-map-equiv-fiber : is-equiv map-equiv-fiber
  is-equiv-map-equiv-fiber = {!!}

  equiv-fiber : fiber f y ≃ fiber' f y
  pr1 equiv-fiber = {!!}
```

### Computing the fibers of a projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fiber-pr1 : fiber (pr1 {B = B}) a → B a
  map-fiber-pr1 ((x , y) , p) = {!!}

  map-inv-fiber-pr1 : B a → fiber (pr1 {B = B}) a
  pr1 (pr1 (map-inv-fiber-pr1 b)) = {!!}

  is-section-map-inv-fiber-pr1 : (map-inv-fiber-pr1 ∘ map-fiber-pr1) ~ id
  is-section-map-inv-fiber-pr1 ((.a , y) , refl) = {!!}

  is-retraction-map-inv-fiber-pr1 : (map-fiber-pr1 ∘ map-inv-fiber-pr1) ~ id
  is-retraction-map-inv-fiber-pr1 b = {!!}

  abstract
    is-equiv-map-fiber-pr1 : is-equiv map-fiber-pr1
    is-equiv-map-fiber-pr1 = {!!}

  equiv-fiber-pr1 : fiber (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-pr1 = {!!}

  abstract
    is-equiv-map-inv-fiber-pr1 : is-equiv map-inv-fiber-pr1
    is-equiv-map-inv-fiber-pr1 = {!!}

  inv-equiv-fiber-pr1 : B a ≃ fiber (pr1 {B = B}) a
  pr1 inv-equiv-fiber-pr1 = {!!}
```

### The total space of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber : (Σ B (fiber f)) → A
  map-equiv-total-fiber t = {!!}

  triangle-map-equiv-total-fiber : pr1 ~ (f ∘ map-equiv-total-fiber)
  triangle-map-equiv-total-fiber t = {!!}

  map-inv-equiv-total-fiber : A → Σ B (fiber f)
  pr1 (map-inv-equiv-total-fiber x) = {!!}

  is-retraction-map-inv-equiv-total-fiber :
    (map-inv-equiv-total-fiber ∘ map-equiv-total-fiber) ~ id
  is-retraction-map-inv-equiv-total-fiber = {!!}

  is-section-map-inv-equiv-total-fiber :
    (map-equiv-total-fiber ∘ map-inv-equiv-total-fiber) ~ id
  is-section-map-inv-equiv-total-fiber = {!!}

  abstract
    is-equiv-map-equiv-total-fiber : is-equiv map-equiv-total-fiber
    is-equiv-map-equiv-total-fiber = {!!}

    is-equiv-map-inv-equiv-total-fiber : is-equiv map-inv-equiv-total-fiber
    is-equiv-map-inv-equiv-total-fiber = {!!}

  equiv-total-fiber : Σ B (fiber f) ≃ A
  pr1 equiv-total-fiber = {!!}

  inv-equiv-total-fiber : A ≃ Σ B (fiber f)
  pr1 inv-equiv-total-fiber = {!!}
```

### Fibers of compositions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (x : X)
  where

  map-compute-fiber-comp :
    fiber (g ∘ h) x → Σ (fiber g x) (λ t → fiber h (pr1 t))
  map-compute-fiber-comp = {!!}

  inv-map-compute-fiber-comp :
    Σ (fiber g x) (λ t → fiber h (pr1 t)) → fiber (g ∘ h) x
  inv-map-compute-fiber-comp = {!!}

  is-section-inv-map-compute-fiber-comp :
    (map-compute-fiber-comp ∘ inv-map-compute-fiber-comp) ~ id
  is-section-inv-map-compute-fiber-comp = {!!}

  is-retraction-inv-map-compute-fiber-comp :
    (inv-map-compute-fiber-comp ∘ map-compute-fiber-comp) ~ id
  is-retraction-inv-map-compute-fiber-comp = {!!}

  abstract
    is-equiv-map-compute-fiber-comp :
      is-equiv map-compute-fiber-comp
    is-equiv-map-compute-fiber-comp = {!!}

  compute-fiber-comp :
    fiber (g ∘ h) x ≃ Σ (fiber g x) (λ t → fiber h (pr1 t))
  compute-fiber-comp = {!!}

  abstract
    is-equiv-inv-map-compute-fiber-comp :
      is-equiv inv-map-compute-fiber-comp
    is-equiv-inv-map-compute-fiber-comp = {!!}

  inv-compute-fiber-comp :
    Σ (fiber g x) (λ t → fiber h (pr1 t)) ≃ fiber (g ∘ h) x
  inv-compute-fiber-comp = {!!}
```

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
