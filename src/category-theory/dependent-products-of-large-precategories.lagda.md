# Dependent products of large precategories

```agda
module category-theory.dependent-products-of-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories

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

Given a family of [large precategories](category-theory.large-precategories.md)
`Pᵢ` indexed by `i : I`, the dependent product `Π(i : I), Pᵢ` is a large
precategory consisting of dependent functions taking `i : I` to an object of
`Pᵢ`. Every component of the structure is given pointwise.

## Definition

```agda
module _
  {l1 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : I → Large-Precategory α β)
  where

  obj-Π-Large-Precategory : (l2 : Level) → UU (l1 ⊔ α l2)
  obj-Π-Large-Precategory = {!!}

  hom-set-Π-Large-Precategory :
    {l2 l3 : Level} →
    obj-Π-Large-Precategory l2 → obj-Π-Large-Precategory l3 → Set (l1 ⊔ β l2 l3)
  hom-set-Π-Large-Precategory = {!!}

  hom-Π-Large-Precategory :
    {l2 l3 : Level} →
    obj-Π-Large-Precategory l2 → obj-Π-Large-Precategory l3 → UU (l1 ⊔ β l2 l3)
  hom-Π-Large-Precategory = {!!}

  comp-hom-Π-Large-Precategory :
    {l2 l3 l4 : Level}
    {x : obj-Π-Large-Precategory l2}
    {y : obj-Π-Large-Precategory l3}
    {z : obj-Π-Large-Precategory l4} →
    hom-Π-Large-Precategory y z →
    hom-Π-Large-Precategory x y →
    hom-Π-Large-Precategory x z
  comp-hom-Π-Large-Precategory = {!!}

  associative-comp-hom-Π-Large-Precategory :
    {l2 l3 l4 l5 : Level}
    {x : obj-Π-Large-Precategory l2}
    {y : obj-Π-Large-Precategory l3}
    {z : obj-Π-Large-Precategory l4}
    {w : obj-Π-Large-Precategory l5} →
    (h : hom-Π-Large-Precategory z w)
    (g : hom-Π-Large-Precategory y z)
    (f : hom-Π-Large-Precategory x y) →
    ( comp-hom-Π-Large-Precategory (comp-hom-Π-Large-Precategory h g) f) ＝
    ( comp-hom-Π-Large-Precategory h (comp-hom-Π-Large-Precategory g f))
  associative-comp-hom-Π-Large-Precategory = {!!}

  inv-associative-comp-hom-Π-Large-Precategory :
    {l2 l3 l4 l5 : Level}
    {x : obj-Π-Large-Precategory l2}
    {y : obj-Π-Large-Precategory l3}
    {z : obj-Π-Large-Precategory l4}
    {w : obj-Π-Large-Precategory l5} →
    (h : hom-Π-Large-Precategory z w)
    (g : hom-Π-Large-Precategory y z)
    (f : hom-Π-Large-Precategory x y) →
    ( comp-hom-Π-Large-Precategory h (comp-hom-Π-Large-Precategory g f)) ＝
    ( comp-hom-Π-Large-Precategory (comp-hom-Π-Large-Precategory h g) f)
  inv-associative-comp-hom-Π-Large-Precategory = {!!}

  id-hom-Π-Large-Precategory :
    {l2 : Level} {x : obj-Π-Large-Precategory l2} → hom-Π-Large-Precategory x x
  id-hom-Π-Large-Precategory = {!!}

  left-unit-law-comp-hom-Π-Large-Precategory :
    {l2 l3 : Level}
    {x : obj-Π-Large-Precategory l2}
    {y : obj-Π-Large-Precategory l3}
    (f : hom-Π-Large-Precategory x y) →
    comp-hom-Π-Large-Precategory id-hom-Π-Large-Precategory f ＝ f
  left-unit-law-comp-hom-Π-Large-Precategory = {!!}

  right-unit-law-comp-hom-Π-Large-Precategory :
    {l2 l3 : Level}
    {x : obj-Π-Large-Precategory l2}
    {y : obj-Π-Large-Precategory l3}
    (f : hom-Π-Large-Precategory x y) →
    comp-hom-Π-Large-Precategory f id-hom-Π-Large-Precategory ＝ f
  right-unit-law-comp-hom-Π-Large-Precategory = {!!}

  Π-Large-Precategory :
    Large-Precategory (λ l2 → l1 ⊔ α l2) (λ l2 l3 → l1 ⊔ β l2 l3)
  Π-Large-Precategory = {!!}
```

## Properties

### Isomorphisms in the large dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : I → Large-Precategory α β)
  {x : obj-Π-Large-Precategory I C l2}
  {y : obj-Π-Large-Precategory I C l3}
  where

  is-fiberwise-iso-is-iso-Π-Large-Precategory :
    (f : hom-Π-Large-Precategory I C x y) →
    is-iso-Large-Precategory (Π-Large-Precategory I C) f →
    (i : I) → is-iso-Large-Precategory (C i) (f i)
  is-fiberwise-iso-is-iso-Π-Large-Precategory = {!!}

  fiberwise-iso-iso-Π-Large-Precategory :
    iso-Large-Precategory (Π-Large-Precategory I C) x y →
    (i : I) → iso-Large-Precategory (C i) (x i) (y i)
  fiberwise-iso-iso-Π-Large-Precategory = {!!}

  is-iso-is-fiberwise-iso-Π-Large-Precategory :
    (f : hom-Π-Large-Precategory I C x y) →
    ((i : I) → is-iso-Large-Precategory (C i) (f i)) →
    is-iso-Large-Precategory (Π-Large-Precategory I C) f
  is-iso-is-fiberwise-iso-Π-Large-Precategory = {!!}

  iso-fiberwise-iso-Π-Large-Precategory :
    ((i : I) → iso-Large-Precategory (C i) (x i) (y i)) →
    iso-Large-Precategory (Π-Large-Precategory I C) x y
  iso-fiberwise-iso-Π-Large-Precategory = {!!}

  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory :
    (f : hom-Π-Large-Precategory I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Π-Large-Precategory f)
  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory = {!!}

  equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory :
    (f : hom-Π-Large-Precategory I C x y) →
    ( is-iso-Large-Precategory (Π-Large-Precategory I C) f) ≃
    ( (i : I) → is-iso-Large-Precategory (C i) (f i))
  equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory = {!!}

  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory :
    (f : hom-Π-Large-Precategory I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Π-Large-Precategory f)
  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory = {!!}

  equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory :
    ( f : hom-Π-Large-Precategory I C x y) →
    ( (i : I) → is-iso-Large-Precategory (C i) (f i)) ≃
    ( is-iso-Large-Precategory (Π-Large-Precategory I C) f)
  equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory = {!!}

  is-equiv-fiberwise-iso-iso-Π-Large-Precategory :
    is-equiv fiberwise-iso-iso-Π-Large-Precategory
  is-equiv-fiberwise-iso-iso-Π-Large-Precategory = {!!}

  equiv-fiberwise-iso-iso-Π-Large-Precategory :
    ( iso-Large-Precategory (Π-Large-Precategory I C) x y) ≃
    ( (i : I) → iso-Large-Precategory (C i) (x i) (y i))
  equiv-fiberwise-iso-iso-Π-Large-Precategory = {!!}

  is-equiv-iso-fiberwise-iso-Π-Large-Precategory :
    is-equiv iso-fiberwise-iso-Π-Large-Precategory
  is-equiv-iso-fiberwise-iso-Π-Large-Precategory = {!!}

  equiv-iso-fiberwise-iso-Π-Large-Precategory :
    ( (i : I) → iso-Large-Precategory (C i) (x i) (y i)) ≃
    ( iso-Large-Precategory (Π-Large-Precategory I C) x y)
  equiv-iso-fiberwise-iso-Π-Large-Precategory = {!!}
```
