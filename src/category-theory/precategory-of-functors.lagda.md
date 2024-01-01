# The precategory of functors and natural transformations between two precategories

```agda
module category-theory.precategory-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) and
[natural transformations](category-theory.natural-transformations-functors-precategories.md)
between them introduce a new precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory. This is called
the **precategory of functors**.

## Definitions

### The precategory of functors and natural transformations between precategories

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  comp-hom-functor-precategory-Precategory :
    {F G H : functor-Precategory C D} →
    natural-transformation-Precategory C D G H →
    natural-transformation-Precategory C D F G →
    natural-transformation-Precategory C D F H
  comp-hom-functor-precategory-Precategory {F} {G} {H} = {!!}

  associative-comp-hom-functor-precategory-Precategory :
    {F G H I : functor-Precategory C D}
    (h : natural-transformation-Precategory C D H I)
    (g : natural-transformation-Precategory C D G H)
    (f : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I h g)
      ( f) ＝
    comp-natural-transformation-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Precategory C D F G H g f)
  associative-comp-hom-functor-precategory-Precategory {F} {G} {H} {I} h g f = {!!}

  inv-associative-comp-hom-functor-precategory-Precategory :
    {F G H I : functor-Precategory C D}
    (h : natural-transformation-Precategory C D H I)
    (g : natural-transformation-Precategory C D G H)
    (f : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Precategory C D F G H g f) ＝
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I h g)
      ( f)
  inv-associative-comp-hom-functor-precategory-Precategory
    { F} {G} {H} {I} h g f = {!!}

  associative-composition-operation-functor-precategory-Precategory :
    associative-composition-operation-binary-family-Set
      ( natural-transformation-set-Precategory C D)
  pr1 associative-composition-operation-functor-precategory-Precategory
    {F} {G} {H} = {!!}

  id-hom-functor-precategory-Precategory :
    (F : functor-Precategory C D) → natural-transformation-Precategory C D F F
  id-hom-functor-precategory-Precategory = {!!}

  left-unit-law-comp-hom-functor-precategory-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G G
      ( id-natural-transformation-Precategory C D G) α ＝
    α
  left-unit-law-comp-hom-functor-precategory-Precategory {F} {G} = {!!}

  right-unit-law-comp-hom-functor-precategory-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F F G
        α (id-natural-transformation-Precategory C D F) ＝
    α
  right-unit-law-comp-hom-functor-precategory-Precategory {F} {G} = {!!}

  is-unital-composition-operation-functor-precategory-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( natural-transformation-set-Precategory C D)
      ( λ {F} {G} {H} → comp-hom-functor-precategory-Precategory {F} {G} {H})
  pr1 is-unital-composition-operation-functor-precategory-Precategory = {!!}

  functor-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-precategory-Precategory = {!!}
```

## Properties

### Isomorphisms in the functor precategory are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-iso-functor-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-natural-isomorphism-Precategory C D F G f →
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f
  pr1 (is-iso-functor-is-natural-isomorphism-Precategory f is-iso-f) = {!!}

  is-natural-isomorphism-is-iso-functor-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f →
    is-natural-isomorphism-Precategory C D F G f
  pr1 (is-natural-isomorphism-is-iso-functor-Precategory f is-iso-f x) = {!!}

  is-equiv-is-iso-functor-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-equiv (is-iso-functor-is-natural-isomorphism-Precategory f)
  is-equiv-is-iso-functor-is-natural-isomorphism-Precategory f = {!!}

  is-equiv-is-natural-isomorphism-is-iso-functor-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-equiv (is-natural-isomorphism-is-iso-functor-Precategory f)
  is-equiv-is-natural-isomorphism-is-iso-functor-Precategory f = {!!}

  equiv-is-iso-functor-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-natural-isomorphism-Precategory C D F G f ≃
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f
  pr1 (equiv-is-iso-functor-is-natural-isomorphism-Precategory f) = {!!}

  equiv-is-natural-isomorphism-is-iso-functor-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f ≃
    is-natural-isomorphism-Precategory C D F G f
  pr1 (equiv-is-natural-isomorphism-is-iso-functor-Precategory f) = {!!}

  iso-functor-natural-isomorphism-Precategory :
    natural-isomorphism-Precategory C D F G →
    iso-Precategory (functor-precategory-Precategory C D) F G
  iso-functor-natural-isomorphism-Precategory = {!!}

  natural-isomorphism-iso-functor-Precategory :
    iso-Precategory (functor-precategory-Precategory C D) F G →
    natural-isomorphism-Precategory C D F G
  natural-isomorphism-iso-functor-Precategory = {!!}

  is-equiv-iso-functor-natural-isomorphism-Precategory :
    is-equiv iso-functor-natural-isomorphism-Precategory
  is-equiv-iso-functor-natural-isomorphism-Precategory = {!!}

  is-equiv-natural-isomorphism-iso-functor-Precategory :
    is-equiv natural-isomorphism-iso-functor-Precategory
  is-equiv-natural-isomorphism-iso-functor-Precategory = {!!}

  equiv-iso-functor-natural-isomorphism-Precategory :
    natural-isomorphism-Precategory C D F G ≃
    iso-Precategory (functor-precategory-Precategory C D) F G
  equiv-iso-functor-natural-isomorphism-Precategory = {!!}

  equiv-natural-isomorphism-iso-functor-Precategory :
    iso-Precategory (functor-precategory-Precategory C D) F G ≃
    natural-isomorphism-Precategory C D F G
  equiv-natural-isomorphism-iso-functor-Precategory = {!!}
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  compute-iso-functor-natural-isomorphism-eq-Precategory :
    (p : F ＝ G) →
    iso-eq-Precategory (functor-precategory-Precategory C D) F G p ＝
    iso-functor-natural-isomorphism-Precategory C D F G
      ( natural-isomorphism-eq-Precategory C D F G p)
  compute-iso-functor-natural-isomorphism-eq-Precategory refl = {!!}
```
