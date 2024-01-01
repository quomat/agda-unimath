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
  hom-set-Π-Precategory x y = {!!}

  hom-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → UU (l1 ⊔ l3)
  hom-Π-Precategory x y = {!!}

  comp-hom-Π-Precategory :
    {x y z : obj-Π-Precategory} →
    hom-Π-Precategory y z →
    hom-Π-Precategory x y →
    hom-Π-Precategory x z
  comp-hom-Π-Precategory f g i = {!!}

  associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : hom-Π-Precategory z w)
    (g : hom-Π-Precategory y z)
    (f : hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f) ＝
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f))
  associative-comp-hom-Π-Precategory h g f = {!!}

  inv-associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : hom-Π-Precategory z w)
    (g : hom-Π-Precategory y z)
    (f : hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f)) ＝
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f)
  inv-associative-comp-hom-Π-Precategory h g f = {!!}

  associative-composition-operation-Π-Precategory :
    associative-composition-operation-binary-family-Set hom-set-Π-Precategory
  pr1 associative-composition-operation-Π-Precategory = {!!}

  id-hom-Π-Precategory : {x : obj-Π-Precategory} → hom-Π-Precategory x x
  id-hom-Π-Precategory i = {!!}

  left-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory}
    (f : hom-Π-Precategory x y) →
    comp-hom-Π-Precategory id-hom-Π-Precategory f ＝ f
  left-unit-law-comp-hom-Π-Precategory f = {!!}

  right-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory} (f : hom-Π-Precategory x y) →
    comp-hom-Π-Precategory f id-hom-Π-Precategory ＝ f
  right-unit-law-comp-hom-Π-Precategory f = {!!}

  is-unital-Π-Precategory :
    is-unital-composition-operation-binary-family-Set
      hom-set-Π-Precategory
      comp-hom-Π-Precategory
  pr1 is-unital-Π-Precategory x = {!!}

  Π-Precategory : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  pr1 Π-Precategory = {!!}
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
  pr1 (is-fiberwise-iso-is-iso-Π-Precategory f is-iso-f i) = {!!}

  fiberwise-iso-iso-Π-Precategory :
    iso-Precategory (Π-Precategory I C) x y →
    (i : I) → iso-Precategory (C i) (x i) (y i)
  pr1 (fiberwise-iso-iso-Π-Precategory e i) = {!!}

  is-iso-is-fiberwise-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    ((i : I) → is-iso-Precategory (C i) (f i)) →
    is-iso-Precategory (Π-Precategory I C) f
  pr1 (is-iso-is-fiberwise-iso-Π-Precategory f is-fiberwise-iso-f) i = {!!}

  iso-fiberwise-iso-Π-Precategory :
    ((i : I) → iso-Precategory (C i) (x i) (y i)) →
    iso-Precategory (Π-Precategory I C) x y
  pr1 (iso-fiberwise-iso-Π-Precategory e) i = {!!}

  is-equiv-is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Π-Precategory f)
  is-equiv-is-fiberwise-iso-is-iso-Π-Precategory f = {!!}

  equiv-is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    ( is-iso-Precategory (Π-Precategory I C) f) ≃
    ( (i : I) → is-iso-Precategory (C i) (f i))
  pr1 (equiv-is-fiberwise-iso-is-iso-Π-Precategory f) = {!!}

  is-equiv-is-iso-is-fiberwise-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Π-Precategory f)
  is-equiv-is-iso-is-fiberwise-iso-Π-Precategory f = {!!}

  equiv-is-iso-is-fiberwise-iso-Π-Precategory :
    ( f : hom-Π-Precategory I C x y) →
    ( (i : I) → is-iso-Precategory (C i) (f i)) ≃
    ( is-iso-Precategory (Π-Precategory I C) f)
  pr1 (equiv-is-iso-is-fiberwise-iso-Π-Precategory f) = {!!}

  is-equiv-fiberwise-iso-iso-Π-Precategory :
    is-equiv fiberwise-iso-iso-Π-Precategory
  is-equiv-fiberwise-iso-iso-Π-Precategory = {!!}

  equiv-fiberwise-iso-iso-Π-Precategory :
    ( iso-Precategory (Π-Precategory I C) x y) ≃
    ( (i : I) → iso-Precategory (C i) (x i) (y i))
  pr1 equiv-fiberwise-iso-iso-Π-Precategory = {!!}

  is-equiv-iso-fiberwise-iso-Π-Precategory :
    is-equiv iso-fiberwise-iso-Π-Precategory
  is-equiv-iso-fiberwise-iso-Π-Precategory = {!!}

  equiv-iso-fiberwise-iso-Π-Precategory :
    ( (i : I) → iso-Precategory (C i) (x i) (y i)) ≃
    ( iso-Precategory (Π-Precategory I C) x y)
  pr1 equiv-iso-fiberwise-iso-Π-Precategory = {!!}
```
