# Dependent products of precategories

```agda
module category-theory.dependent-products-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a family of [precategories](category-theory.precategories.md) `Pᵢ` indexed
by `i : I`, the dependent product `Π(i : I), Pᵢ` is a precategory consisting of
dependent functions taking `i : I` to an object of `Pᵢ`. Every component of the
structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Precategory l2 l3)
  where

  obj-Π-Precategory : UU (l1 ⊔ l2)
  obj-Π-Precategory = {!!}

  hom-set-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → Set (l1 ⊔ l3)
  hom-set-Π-Precategory = {!!}

  hom-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → UU (l1 ⊔ l3)
  hom-Π-Precategory = {!!}

  comp-hom-Π-Precategory :
    {x y z : obj-Π-Precategory} →
    hom-Π-Precategory y z →
    hom-Π-Precategory x y →
    hom-Π-Precategory x z
  comp-hom-Π-Precategory = {!!}

  associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : hom-Π-Precategory z w)
    (g : hom-Π-Precategory y z)
    (f : hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f) ＝
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f))
  associative-comp-hom-Π-Precategory = {!!}

  inv-associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : hom-Π-Precategory z w)
    (g : hom-Π-Precategory y z)
    (f : hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f)) ＝
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f)
  inv-associative-comp-hom-Π-Precategory = {!!}

  associative-composition-operation-Π-Precategory :
    associative-composition-operation-binary-family-Set hom-set-Π-Precategory
  associative-composition-operation-Π-Precategory = {!!}

  id-hom-Π-Precategory : {x : obj-Π-Precategory} → hom-Π-Precategory x x
  id-hom-Π-Precategory = {!!}

  left-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory}
    (f : hom-Π-Precategory x y) →
    comp-hom-Π-Precategory id-hom-Π-Precategory f ＝ f
  left-unit-law-comp-hom-Π-Precategory = {!!}

  right-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory} (f : hom-Π-Precategory x y) →
    comp-hom-Π-Precategory f id-hom-Π-Precategory ＝ f
  right-unit-law-comp-hom-Π-Precategory = {!!}

  is-unital-Π-Precategory :
    is-unital-composition-operation-binary-family-Set
      hom-set-Π-Precategory
      comp-hom-Π-Precategory
  is-unital-Π-Precategory = {!!}

  Π-Precategory : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  Π-Precategory = {!!}
```

## Properties

### Isomorphisms in the dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Precategory l2 l3)
  {x y : obj-Π-Precategory I C}
  where

  is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-iso-Precategory (Π-Precategory I C) f →
    (i : I) → is-iso-Precategory (C i) (f i)
  is-fiberwise-iso-is-iso-Π-Precategory = {!!}

  fiberwise-iso-iso-Π-Precategory :
    iso-Precategory (Π-Precategory I C) x y →
    (i : I) → iso-Precategory (C i) (x i) (y i)
  fiberwise-iso-iso-Π-Precategory = {!!}

  is-iso-is-fiberwise-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    ((i : I) → is-iso-Precategory (C i) (f i)) →
    is-iso-Precategory (Π-Precategory I C) f
  is-iso-is-fiberwise-iso-Π-Precategory = {!!}

  iso-fiberwise-iso-Π-Precategory :
    ((i : I) → iso-Precategory (C i) (x i) (y i)) →
    iso-Precategory (Π-Precategory I C) x y
  iso-fiberwise-iso-Π-Precategory = {!!}

  is-equiv-is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Π-Precategory f)
  is-equiv-is-fiberwise-iso-is-iso-Π-Precategory = {!!}

  equiv-is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    ( is-iso-Precategory (Π-Precategory I C) f) ≃
    ( (i : I) → is-iso-Precategory (C i) (f i))
  equiv-is-fiberwise-iso-is-iso-Π-Precategory = {!!}

  is-equiv-is-iso-is-fiberwise-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Π-Precategory f)
  is-equiv-is-iso-is-fiberwise-iso-Π-Precategory = {!!}

  equiv-is-iso-is-fiberwise-iso-Π-Precategory :
    ( f : hom-Π-Precategory I C x y) →
    ( (i : I) → is-iso-Precategory (C i) (f i)) ≃
    ( is-iso-Precategory (Π-Precategory I C) f)
  equiv-is-iso-is-fiberwise-iso-Π-Precategory = {!!}

  is-equiv-fiberwise-iso-iso-Π-Precategory :
    is-equiv fiberwise-iso-iso-Π-Precategory
  is-equiv-fiberwise-iso-iso-Π-Precategory = {!!}

  equiv-fiberwise-iso-iso-Π-Precategory :
    ( iso-Precategory (Π-Precategory I C) x y) ≃
    ( (i : I) → iso-Precategory (C i) (x i) (y i))
  equiv-fiberwise-iso-iso-Π-Precategory = {!!}

  is-equiv-iso-fiberwise-iso-Π-Precategory :
    is-equiv iso-fiberwise-iso-Π-Precategory
  is-equiv-iso-fiberwise-iso-Π-Precategory = {!!}

  equiv-iso-fiberwise-iso-Π-Precategory :
    ( (i : I) → iso-Precategory (C i) (x i) (y i)) ≃
    ( iso-Precategory (Π-Precategory I C) x y)
  equiv-iso-fiberwise-iso-Π-Precategory = {!!}
```
