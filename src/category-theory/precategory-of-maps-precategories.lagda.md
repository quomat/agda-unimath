# The precategory of maps and natural transformations between two precategories

```agda
module category-theory.precategory-of-maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-maps-precategories
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

[Maps](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) and
[natural transformations](category-theory.natural-transformations-maps-precategories.md)
between them introduce a new precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory. This is called
the **precategory of maps**.

## Definitions

### The precategory of maps and natural transformations between precategories

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  comp-hom-map-precategory-Precategory :
    {F G H : map-Precategory C D} →
    natural-transformation-map-Precategory C D G H →
    natural-transformation-map-Precategory C D F G →
    natural-transformation-map-Precategory C D F H
  comp-hom-map-precategory-Precategory = {!!}

  associative-comp-hom-map-precategory-Precategory :
    {F G H I : map-Precategory C D}
    (h : natural-transformation-map-Precategory C D H I)
    (g : natural-transformation-map-Precategory C D G H)
    (f : natural-transformation-map-Precategory C D F G) →
    comp-natural-transformation-map-Precategory C D F G I
      ( comp-natural-transformation-map-Precategory C D G H I h g)
      ( f) ＝
    comp-natural-transformation-map-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Precategory C D F G H g f)
  associative-comp-hom-map-precategory-Precategory = {!!}

  inv-associative-comp-hom-map-precategory-Precategory :
    {F G H I : map-Precategory C D}
    (h : natural-transformation-map-Precategory C D H I)
    (g : natural-transformation-map-Precategory C D G H)
    (f : natural-transformation-map-Precategory C D F G) →
    comp-natural-transformation-map-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Precategory C D F G H g f) ＝
    comp-natural-transformation-map-Precategory C D F G I
      ( comp-natural-transformation-map-Precategory C D G H I h g)
      ( f)
  inv-associative-comp-hom-map-precategory-Precategory = {!!}

  associative-composition-operation-map-precategory-Precategory :
    associative-composition-operation-binary-family-Set
      ( natural-transformation-map-set-Precategory C D)
  pr1 associative-composition-operation-map-precategory-Precategory
    {F} {G} {H} = {!!}

  id-hom-map-precategory-Precategory :
    (F : map-Precategory C D) → natural-transformation-map-Precategory C D F F
  id-hom-map-precategory-Precategory = {!!}

  left-unit-law-comp-hom-map-precategory-Precategory :
    {F G : map-Precategory C D}
    (α : natural-transformation-map-Precategory C D F G) →
    ( comp-natural-transformation-map-Precategory C D F G G
      ( id-natural-transformation-map-Precategory C D G) α) ＝
    ( α)
  left-unit-law-comp-hom-map-precategory-Precategory = {!!}

  right-unit-law-comp-hom-map-precategory-Precategory :
    {F G : map-Precategory C D}
    (α : natural-transformation-map-Precategory C D F G) →
    ( comp-natural-transformation-map-Precategory C D F F G
        α (id-natural-transformation-map-Precategory C D F)) ＝
    ( α)
  right-unit-law-comp-hom-map-precategory-Precategory = {!!}

  is-unital-composition-operation-map-precategory-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( natural-transformation-map-set-Precategory C D)
      ( comp-hom-map-precategory-Precategory)
  is-unital-composition-operation-map-precategory-Precategory = {!!}

  map-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  map-precategory-Precategory = {!!}
```

## Properties

### Isomorphisms in the map precategory are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-iso-map-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-natural-isomorphism-map-Precategory C D F G f →
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f
  is-iso-map-is-natural-isomorphism-map-Precategory = {!!}

  is-natural-isomorphism-map-is-iso-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f →
    is-natural-isomorphism-map-Precategory C D F G f
  is-natural-isomorphism-map-is-iso-map-Precategory = {!!}

  is-equiv-is-iso-map-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-equiv (is-iso-map-is-natural-isomorphism-map-Precategory f)
  is-equiv-is-iso-map-is-natural-isomorphism-map-Precategory = {!!}

  is-equiv-is-natural-isomorphism-map-is-iso-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-equiv (is-natural-isomorphism-map-is-iso-map-Precategory f)
  is-equiv-is-natural-isomorphism-map-is-iso-map-Precategory = {!!}

  equiv-is-iso-map-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-natural-isomorphism-map-Precategory C D F G f ≃
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f
  equiv-is-iso-map-is-natural-isomorphism-map-Precategory = {!!}

  equiv-is-natural-isomorphism-map-is-iso-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f ≃
    is-natural-isomorphism-map-Precategory C D F G f
  equiv-is-natural-isomorphism-map-is-iso-map-Precategory = {!!}

  iso-map-natural-isomorphism-map-Precategory :
    natural-isomorphism-map-Precategory C D F G →
    iso-Precategory (map-precategory-Precategory C D) F G
  iso-map-natural-isomorphism-map-Precategory = {!!}

  natural-isomorphism-map-iso-map-Precategory :
    iso-Precategory (map-precategory-Precategory C D) F G →
    natural-isomorphism-map-Precategory C D F G
  natural-isomorphism-map-iso-map-Precategory = {!!}

  is-equiv-iso-map-natural-isomorphism-map-Precategory :
    is-equiv iso-map-natural-isomorphism-map-Precategory
  is-equiv-iso-map-natural-isomorphism-map-Precategory = {!!}

  is-equiv-natural-isomorphism-map-iso-map-Precategory :
    is-equiv natural-isomorphism-map-iso-map-Precategory
  is-equiv-natural-isomorphism-map-iso-map-Precategory = {!!}

  equiv-iso-map-natural-isomorphism-map-Precategory :
    natural-isomorphism-map-Precategory C D F G ≃
    iso-Precategory (map-precategory-Precategory C D) F G
  equiv-iso-map-natural-isomorphism-map-Precategory = {!!}

  equiv-natural-isomorphism-map-iso-map-Precategory :
    iso-Precategory (map-precategory-Precategory C D) F G ≃
    natural-isomorphism-map-Precategory C D F G
  equiv-natural-isomorphism-map-iso-map-Precategory = {!!}
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  compute-iso-map-natural-isomorphism-map-eq-Precategory :
    (p : F ＝ G) →
    iso-eq-Precategory (map-precategory-Precategory C D) F G p ＝
    iso-map-natural-isomorphism-map-Precategory C D F G
      ( natural-isomorphism-map-eq-Precategory C D F G p)
  compute-iso-map-natural-isomorphism-map-eq-Precategory = {!!}
```
