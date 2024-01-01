# Natural isomorphisms between functors between precategories

```agda
module category-theory.natural-isomorphisms-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **natural isomorphism** `γ` from
[functor](category-theory.functors-precategories.md) `F : C → D` to `G : C → D`
is a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
from `F` to `G` such that the morphism `γ F : hom (F x) (G x)` is an
[isomorphism](category-theory.isomorphisms-in-precategories.md), for every
object `x` in `C`.

## Definition

### Families of isomorphisms between functors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  iso-family-functor-Precategory : UU (l1 ⊔ l4)
  iso-family-functor-Precategory = {!!}
```

### The predicate of being an isomorphism in a precategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-natural-isomorphism-Precategory :
    natural-transformation-Precategory C D F G → UU (l1 ⊔ l4)
  is-natural-isomorphism-Precategory = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  (f : natural-transformation-Precategory C D F G)
  where

  hom-inv-family-is-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D F G f →
    hom-family-functor-Precategory C D G F
  hom-inv-family-is-natural-isomorphism-Precategory = {!!}

  is-section-hom-inv-family-is-natural-isomorphism-Precategory :
    (is-iso-f : is-natural-isomorphism-Precategory C D F G f) →
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-family-natural-transformation-Precategory C D F G f x)
      ( hom-inv-is-iso-Precategory D (is-iso-f x)) ＝
    id-hom-Precategory D
  is-section-hom-inv-family-is-natural-isomorphism-Precategory = {!!}

  is-retraction-hom-inv-family-is-natural-isomorphism-Precategory :
    (is-iso-f : is-natural-isomorphism-Precategory C D F G f) →
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-inv-is-iso-Precategory D (is-iso-f x))
      ( hom-family-natural-transformation-Precategory C D F G f x) ＝
    id-hom-Precategory D
  is-retraction-hom-inv-family-is-natural-isomorphism-Precategory = {!!}

  iso-family-is-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D F G f →
    iso-family-functor-Precategory C D F G
  iso-family-is-natural-isomorphism-Precategory = {!!}

  inv-iso-family-is-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D F G f →
    iso-family-functor-Precategory C D G F
  inv-iso-family-is-natural-isomorphism-Precategory = {!!}
```

### Natural isomorphisms in a precategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  natural-isomorphism-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-Precategory = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  (f : natural-isomorphism-Precategory C D F G)
  where

  natural-transformation-natural-isomorphism-Precategory :
    natural-transformation-Precategory C D F G
  natural-transformation-natural-isomorphism-Precategory = {!!}

  hom-family-natural-isomorphism-Precategory :
    hom-family-functor-Precategory C D F G
  hom-family-natural-isomorphism-Precategory = {!!}

  coherence-square-natural-isomorphism-Precategory :
    is-natural-transformation-Precategory C D F G
      ( hom-family-natural-transformation-Precategory C D F G
        ( natural-transformation-natural-isomorphism-Precategory))
  coherence-square-natural-isomorphism-Precategory = {!!}

  is-natural-isomorphism-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D F G
      ( natural-transformation-natural-isomorphism-Precategory)
  is-natural-isomorphism-natural-isomorphism-Precategory = {!!}

  hom-inv-family-natural-isomorphism-Precategory :
    hom-family-functor-Precategory C D G F
  hom-inv-family-natural-isomorphism-Precategory = {!!}

  is-section-hom-inv-family-natural-isomorphism-Precategory :
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-family-natural-isomorphism-Precategory x)
      ( hom-inv-family-natural-isomorphism-Precategory x) ＝
    id-hom-Precategory D
  is-section-hom-inv-family-natural-isomorphism-Precategory = {!!}

  is-retraction-hom-inv-family-natural-isomorphism-Precategory :
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-inv-family-natural-isomorphism-Precategory x)
      ( hom-family-natural-isomorphism-Precategory x) ＝
    id-hom-Precategory D
  is-retraction-hom-inv-family-natural-isomorphism-Precategory = {!!}

  iso-family-natural-isomorphism-Precategory :
    iso-family-functor-Precategory C D F G
  iso-family-natural-isomorphism-Precategory = {!!}

  inv-iso-family-natural-isomorphism-Precategory :
    iso-family-functor-Precategory C D G F
  inv-iso-family-natural-isomorphism-Precategory = {!!}
```

## Examples

### The identity natural isomorphism

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  id-natural-isomorphism-Precategory :
    (F : functor-Precategory C D) → natural-isomorphism-Precategory C D F F
  id-natural-isomorphism-Precategory F = {!!}
```

### Equalities induce natural isomorphisms

An equality between functors `F` and `G` gives rise to a natural isomorphism
between them. This is because, by the J-rule, it is enough to construct a
natural isomorphism given `refl : F ＝ F`, from `F` to itself. We take the
identity natural transformation as such an isomorphism.

```agda
natural-isomorphism-eq-Precategory :
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D) →
  F ＝ G → natural-isomorphism-Precategory C D F G
natural-isomorphism-eq-Precategory C D F .F refl = {!!}
```

## Propositions

### Being a natural isomorphism is a proposition

That a natural transformation is a natural isomorphism is a proposition. This
follows from the fact that being an isomorphism is a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-prop-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-prop (is-natural-isomorphism-Precategory C D F G f)
  is-prop-is-natural-isomorphism-Precategory = {!!}

  is-natural-isomorphism-prop-hom-Precategory :
    (f : natural-transformation-Precategory C D F G) → Prop (l1 ⊔ l4)
  is-natural-isomorphism-prop-hom-Precategory = {!!}
```

### Equality of natural isomorphisms is equality of their underlying natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  extensionality-natural-isomorphism-Precategory :
    (f g : natural-isomorphism-Precategory C D F G) →
    (f ＝ g) ≃
    ( hom-family-natural-isomorphism-Precategory C D F G f ~
      hom-family-natural-isomorphism-Precategory C D F G g)
  extensionality-natural-isomorphism-Precategory = {!!}

  eq-eq-natural-transformation-natural-isomorphism-Precategory :
    (f g : natural-isomorphism-Precategory C D F G) →
    ( natural-transformation-natural-isomorphism-Precategory C D F G f ＝
      natural-transformation-natural-isomorphism-Precategory C D F G g) →
    f ＝ g
  eq-eq-natural-transformation-natural-isomorphism-Precategory f g = {!!}

  eq-htpy-hom-family-natural-isomorphism-Precategory :
        (f g : natural-isomorphism-Precategory C D F G) →
    ( hom-family-natural-isomorphism-Precategory C D F G f ~
      hom-family-natural-isomorphism-Precategory C D F G g) →
    f ＝ g
  eq-htpy-hom-family-natural-isomorphism-Precategory = {!!}
```

### The type of natural isomorphisms form a set

The type of natural isomorphisms between functors `F` and `G` is a
[subtype](foundation-core.subtypes.md) of the [set](foundation-core.sets.md)
`natural-transformation F G` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-set-natural-isomorphism-Precategory :
    is-set (natural-isomorphism-Precategory C D F G)
  is-set-natural-isomorphism-Precategory = {!!}

  natural-isomorphism-set-Precategory : Set (l1 ⊔ l2 ⊔ l4)
  pr1 natural-isomorphism-set-Precategory = {!!}
```

### Inverses of natural isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  (f : natural-transformation-Precategory C D F G)
  where

  natural-transformation-inv-is-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D F G f →
    natural-transformation-Precategory C D G F
  natural-transformation-inv-is-natural-isomorphism-Precategory = {!!}

  is-section-natural-transformation-inv-is-natural-isomorphism-Precategory :
    (is-iso-f : is-natural-isomorphism-Precategory C D F G f) →
    comp-natural-transformation-Precategory C D G F G
      ( f)
      ( natural-transformation-inv-is-natural-isomorphism-Precategory
        ( is-iso-f)) ＝
    id-natural-transformation-Precategory C D G
  is-section-natural-transformation-inv-is-natural-isomorphism-Precategory
    is-iso-f = {!!}

  is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategory :
    (is-iso-f : is-natural-isomorphism-Precategory C D F G f) →
    comp-natural-transformation-Precategory C D F G F
      ( natural-transformation-inv-is-natural-isomorphism-Precategory is-iso-f)
      ( f) ＝
    id-natural-transformation-Precategory C D F
  is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategory
    is-iso-f = {!!}

  is-natural-isomorphism-inv-is-natural-isomorphism-Precategory :
    (is-iso-f : is-natural-isomorphism-Precategory C D F G f) →
    is-natural-isomorphism-Precategory C D G F
      ( natural-transformation-inv-is-natural-isomorphism-Precategory is-iso-f)
  is-natural-isomorphism-inv-is-natural-isomorphism-Precategory is-iso-f = {!!}
```

### Inverses of natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  (f : natural-isomorphism-Precategory C D F G)
  where

  natural-transformation-inv-natural-isomorphism-Precategory :
    natural-transformation-Precategory C D G F
  natural-transformation-inv-natural-isomorphism-Precategory = {!!}

  is-section-natural-transformation-inv-natural-isomorphism-Precategory :
    ( comp-natural-transformation-Precategory C D G F G
      ( natural-transformation-natural-isomorphism-Precategory C D F G f)
      ( natural-transformation-inv-natural-isomorphism-Precategory)) ＝
    ( id-natural-transformation-Precategory C D G)
  is-section-natural-transformation-inv-natural-isomorphism-Precategory = {!!}

  is-retraction-natural-transformation-inv-natural-isomorphism-Precategory :
    ( comp-natural-transformation-Precategory C D F G F
      ( natural-transformation-inv-natural-isomorphism-Precategory)
      ( natural-transformation-natural-isomorphism-Precategory C D F G f)) ＝
    ( id-natural-transformation-Precategory C D F)
  is-retraction-natural-transformation-inv-natural-isomorphism-Precategory = {!!}

  is-natural-isomorphism-inv-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D G F
      ( natural-transformation-inv-natural-isomorphism-Precategory)
  is-natural-isomorphism-inv-natural-isomorphism-Precategory = {!!}

  inv-natural-isomorphism-Precategory :
    natural-isomorphism-Precategory C D G F
  pr1 inv-natural-isomorphism-Precategory = {!!}
```

### Natural isomorphisms are closed under composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H : functor-Precategory C D)
  (g : natural-transformation-Precategory C D G H)
  (f : natural-transformation-Precategory C D F G)
  where

  is-natural-isomorphism-comp-is-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D G H g →
    is-natural-isomorphism-Precategory C D F G f →
    is-natural-isomorphism-Precategory C D F H
      ( comp-natural-transformation-Precategory C D F G H g f)
  is-natural-isomorphism-comp-is-natural-isomorphism-Precategory
    is-iso-g is-iso-f x = {!!}
```

### The composition operation on natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H : functor-Precategory C D)
  (g : natural-isomorphism-Precategory C D G H)
  (f : natural-isomorphism-Precategory C D F G)
  where

  hom-comp-natural-isomorphism-Precategory :
    natural-transformation-Precategory C D F H
  hom-comp-natural-isomorphism-Precategory = {!!}

  is-natural-isomorphism-comp-natural-isomorphism-Precategory :
    is-natural-isomorphism-Precategory C D F H
      ( hom-comp-natural-isomorphism-Precategory)
  is-natural-isomorphism-comp-natural-isomorphism-Precategory = {!!}

  comp-natural-isomorphism-Precategory : natural-isomorphism-Precategory C D F H
  pr1 comp-natural-isomorphism-Precategory = {!!}

  natural-transformation-inv-comp-natural-isomorphism-Precategory :
    natural-transformation-Precategory C D H F
  natural-transformation-inv-comp-natural-isomorphism-Precategory = {!!}

  is-section-inv-comp-natural-isomorphism-Precategory :
    ( comp-natural-transformation-Precategory C D H F H
      ( hom-comp-natural-isomorphism-Precategory)
      ( natural-transformation-inv-comp-natural-isomorphism-Precategory)) ＝
    ( id-natural-transformation-Precategory C D H)
  is-section-inv-comp-natural-isomorphism-Precategory = {!!}

  is-retraction-inv-comp-natural-isomorphism-Precategory :
    ( comp-natural-transformation-Precategory C D F H F
      ( natural-transformation-inv-comp-natural-isomorphism-Precategory)
      ( hom-comp-natural-isomorphism-Precategory)) ＝
    ( id-natural-transformation-Precategory C D F)
  is-retraction-inv-comp-natural-isomorphism-Precategory = {!!}
```

### Groupoid laws of natural isomorphisms in precategories

#### Composition of natural isomorphisms satisfies the unit laws

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  (f : natural-isomorphism-Precategory C D F G)
  where

  left-unit-law-comp-natural-isomorphism-Precategory :
    comp-natural-isomorphism-Precategory C D F G G
      ( id-natural-isomorphism-Precategory C D G)
      ( f) ＝
    f
  left-unit-law-comp-natural-isomorphism-Precategory = {!!}

  right-unit-law-comp-natural-isomorphism-Precategory :
    comp-natural-isomorphism-Precategory C D F F G f
      ( id-natural-isomorphism-Precategory C D F) ＝
    f
  right-unit-law-comp-natural-isomorphism-Precategory = {!!}
```

#### Composition of natural isomorphisms is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H I : functor-Precategory C D)
  (f : natural-isomorphism-Precategory C D F G)
  (g : natural-isomorphism-Precategory C D G H)
  (h : natural-isomorphism-Precategory C D H I)
  where

  associative-comp-natural-isomorphism-Precategory :
    ( comp-natural-isomorphism-Precategory C D F G I
      ( comp-natural-isomorphism-Precategory C D G H I h g)
      ( f)) ＝
    ( comp-natural-isomorphism-Precategory C D F H I h
      ( comp-natural-isomorphism-Precategory C D F G H g f))
  associative-comp-natural-isomorphism-Precategory = {!!}
```

#### Composition of natural isomorphisms satisfies inverse laws

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  (f : natural-isomorphism-Precategory C D F G)
  where

  left-inverse-law-comp-natural-isomorphism-Precategory :
    ( comp-natural-isomorphism-Precategory C D F G F
      ( inv-natural-isomorphism-Precategory C D F G f)
      ( f)) ＝
    ( id-natural-isomorphism-Precategory C D F)
  left-inverse-law-comp-natural-isomorphism-Precategory = {!!}

  right-inverse-law-comp-natural-isomorphism-Precategory :
    ( comp-natural-isomorphism-Precategory C D G F G
      ( f)
      ( inv-natural-isomorphism-Precategory C D F G f)) ＝
    ( id-natural-isomorphism-Precategory C D G)
  right-inverse-law-comp-natural-isomorphism-Precategory = {!!}
```

### When the type of natural transformations is a proposition, the type of natural isomorphisms is a proposition

The type of natural isomorphisms between functors `F` and `G` is a subtype of
`natural-transformation F G`, so when this type is a proposition, then the type
of natural isomorphisms from `F` to `G` form a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-prop-natural-isomorphism-Precategory :
    is-prop (natural-transformation-Precategory C D F G) →
    is-prop (natural-isomorphism-Precategory C D F G)
  is-prop-natural-isomorphism-Precategory = {!!}

  natural-isomorphism-prop-Precategory :
    is-prop (natural-transformation-Precategory C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-prop-Precategory = {!!}
```

### Functoriality of `natural-isomorphism-eq`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H : functor-Precategory C D)
  where

  preserves-concat-natural-isomorphism-eq-Precategory :
    (p : F ＝ G) (q : G ＝ H) →
    natural-isomorphism-eq-Precategory C D F H (p ∙ q) ＝
    comp-natural-isomorphism-Precategory C D F G H
      ( natural-isomorphism-eq-Precategory C D G H q)
      ( natural-isomorphism-eq-Precategory C D F G p)
  preserves-concat-natural-isomorphism-eq-Precategory refl q = {!!}
```
