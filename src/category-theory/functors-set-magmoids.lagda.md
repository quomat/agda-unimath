# Functors between set-magmoids

```agda
module category-theory.functors-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.maps-set-magmoids
open import category-theory.set-magmoids

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor between [set-magmoids](category-theory.set-magmoids.md)** is a
family of maps on the hom-[sets](foundation-core.sets.md) that preserve the
[composition operation](category-theory.composition-operations-on-binary-families-of-sets.md).

These objects serve as our starting point in the study of
[stucture](foundation.structure.md)-preserving maps of
[categories](category-theory.categories.md). Indeed, categories form a
[subtype](foundation-core.subtypes.md) of set-magmoids, although functors of
set-magmoids do not automatically preserve identity-morphisms.

## Definitions

### The predicate of being a functor of set-magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F₀ : obj-Set-Magmoid A → obj-Set-Magmoid B)
  (F₁ :
    {x y : obj-Set-Magmoid A} →
    hom-Set-Magmoid A x y → hom-Set-Magmoid B (F₀ x) (F₀ y))
  where

  preserves-comp-hom-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-Set-Magmoid = {!!}

  is-prop-preserves-comp-hom-Set-Magmoid :
    is-prop preserves-comp-hom-Set-Magmoid
  is-prop-preserves-comp-hom-Set-Magmoid = {!!}

  preserves-comp-hom-prop-Set-Magmoid : Prop (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-prop-Set-Magmoid = {!!}
```

### The predicate on maps of set-magmoids of being a functor

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : map-Set-Magmoid A B)
  where

  preserves-comp-hom-prop-map-Set-Magmoid : Prop (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-prop-map-Set-Magmoid = {!!}

  preserves-comp-hom-map-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-map-Set-Magmoid = {!!}

  is-prop-preserves-comp-hom-map-Set-Magmoid :
    is-prop preserves-comp-hom-map-Set-Magmoid
  is-prop-preserves-comp-hom-map-Set-Magmoid = {!!}
```

### The type of functors between set-magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  where

  functor-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Set-Magmoid = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : functor-Set-Magmoid A B)
  where

  obj-functor-Set-Magmoid : obj-Set-Magmoid A → obj-Set-Magmoid B
  obj-functor-Set-Magmoid = {!!}

  hom-functor-Set-Magmoid :
    {x y : obj-Set-Magmoid A} →
    (f : hom-Set-Magmoid A x y) →
    hom-Set-Magmoid B
      ( obj-functor-Set-Magmoid x)
      ( obj-functor-Set-Magmoid y)
  hom-functor-Set-Magmoid = {!!}

  map-functor-Set-Magmoid : map-Set-Magmoid A B
  map-functor-Set-Magmoid = {!!}

  preserves-comp-functor-Set-Magmoid :
    {x y z : obj-Set-Magmoid A}
    (g : hom-Set-Magmoid A y z)
    (f : hom-Set-Magmoid A x y) →
    ( hom-functor-Set-Magmoid
      ( comp-hom-Set-Magmoid A g f)) ＝
    ( comp-hom-Set-Magmoid B
      ( hom-functor-Set-Magmoid g)
      ( hom-functor-Set-Magmoid f))
  preserves-comp-functor-Set-Magmoid = {!!}
```

### The identity functor on a set-magmoid

```agda
module _
  {l1 l2 : Level} (A : Set-Magmoid l1 l2)
  where

  id-functor-Set-Magmoid : functor-Set-Magmoid A A
  id-functor-Set-Magmoid = {!!}
```

### Composition of functors on set-magmoids

Any two compatible functors can be composed to a new functor.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Set-Magmoid l1 l2)
  (B : Set-Magmoid l3 l4)
  (C : Set-Magmoid l5 l6)
  (G : functor-Set-Magmoid B C)
  (F : functor-Set-Magmoid A B)
  where

  obj-comp-functor-Set-Magmoid : obj-Set-Magmoid A → obj-Set-Magmoid C
  obj-comp-functor-Set-Magmoid = {!!}

  hom-comp-functor-Set-Magmoid :
    {x y : obj-Set-Magmoid A} →
    hom-Set-Magmoid A x y →
    hom-Set-Magmoid C
      ( obj-comp-functor-Set-Magmoid x)
      ( obj-comp-functor-Set-Magmoid y)
  hom-comp-functor-Set-Magmoid = {!!}

  map-comp-functor-Set-Magmoid : map-Set-Magmoid A C
  map-comp-functor-Set-Magmoid = {!!}

  preserves-comp-comp-functor-Set-Magmoid :
    preserves-comp-hom-Set-Magmoid A C
      obj-comp-functor-Set-Magmoid
      hom-comp-functor-Set-Magmoid
  preserves-comp-comp-functor-Set-Magmoid = {!!}

  comp-functor-Set-Magmoid : functor-Set-Magmoid A C
  comp-functor-Set-Magmoid = {!!}
```

## Properties

### Extensionality of functors between set-magmoids

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F G : functor-Set-Magmoid A B)
  where

  equiv-eq-map-eq-functor-Set-Magmoid :
    (F ＝ G) ≃ (map-functor-Set-Magmoid A B F ＝ map-functor-Set-Magmoid A B G)
  equiv-eq-map-eq-functor-Set-Magmoid = {!!}

  eq-map-eq-functor-Set-Magmoid :
    F ＝ G → map-functor-Set-Magmoid A B F ＝ map-functor-Set-Magmoid A B G
  eq-map-eq-functor-Set-Magmoid = {!!}

  eq-eq-map-functor-Set-Magmoid :
    map-functor-Set-Magmoid A B F ＝ map-functor-Set-Magmoid A B G → F ＝ G
  eq-eq-map-functor-Set-Magmoid = {!!}

  is-section-eq-eq-map-functor-Set-Magmoid :
    eq-map-eq-functor-Set-Magmoid ∘ eq-eq-map-functor-Set-Magmoid ~ id
  is-section-eq-eq-map-functor-Set-Magmoid = {!!}

  is-retraction-eq-eq-map-functor-Set-Magmoid :
    eq-eq-map-functor-Set-Magmoid ∘ eq-map-eq-functor-Set-Magmoid ~ id
  is-retraction-eq-eq-map-functor-Set-Magmoid = {!!}
```

### Categorical laws for functor composition

#### Unit laws for functor composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : functor-Set-Magmoid A B)
  where

  left-unit-law-comp-functor-Set-Magmoid :
    comp-functor-Set-Magmoid A B B (id-functor-Set-Magmoid B) F ＝ F
  left-unit-law-comp-functor-Set-Magmoid = {!!}

  right-unit-law-comp-functor-Set-Magmoid :
    comp-functor-Set-Magmoid A A B F (id-functor-Set-Magmoid A) ＝ F
  right-unit-law-comp-functor-Set-Magmoid = {!!}
```

#### Associativity of functor composition

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Set-Magmoid l1 l1')
  (B : Set-Magmoid l2 l2')
  (C : Set-Magmoid l3 l3')
  (D : Set-Magmoid l4 l4')
  (F : functor-Set-Magmoid A B)
  (G : functor-Set-Magmoid B C)
  (H : functor-Set-Magmoid C D)
  where

  associative-comp-functor-Set-Magmoid :
    comp-functor-Set-Magmoid A B D (comp-functor-Set-Magmoid B C D H G) F ＝
    comp-functor-Set-Magmoid A C D H (comp-functor-Set-Magmoid A B C G F)
  associative-comp-functor-Set-Magmoid = {!!}
```

#### Mac Lane pentagon for functor composition

```text
    (I(GH))F ---- I((GH)F)
          /        \
         /          \
  ((IH)G)F          I(H(GF))
          \        /
            \    /
           (IH)(GF)
```

The proof remains to be formalized.

```text
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Set-Magmoid l1 l1')
  (B : Set-Magmoid l2 l2')
  (C : Set-Magmoid l3 l3')
  (D : Set-Magmoid l4 l4')
  (E : Set-Magmoid l4 l4')
  (F : functor-Set-Magmoid A B)
  (G : functor-Set-Magmoid B C)
  (H : functor-Set-Magmoid C D)
  (I : functor-Set-Magmoid D E)
  where

  mac-lane-pentagon-comp-functor-Set-Magmoid :
    coherence-pentagon-identifications
      { x = {!!}
```
