# Anafunctors between precategories

```agda
module category-theory.anafunctors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

An **anafunctor** is a [functor](category-theory.functors-precategories.md) that
is only defined up to
[isomorphism](category-theory.isomorphisms-in-precategories.md).

## Definition

```agda
anafunctor-Precategory :
  {l1 l2 l3 l4 : Level} (l : Level) →
  Precategory l1 l2 → Precategory l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
anafunctor-Precategory = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : anafunctor-Precategory l5 C D)
  where

  object-anafunctor-Precategory : obj-Precategory C → obj-Precategory D → UU l5
  object-anafunctor-Precategory = {!!}

  hom-anafunctor-Precategory :
    (X Y : obj-Precategory C)
    (U : obj-Precategory D) (u : object-anafunctor-Precategory X U)
    (V : obj-Precategory D) (v : object-anafunctor-Precategory Y V) →
    hom-Precategory C X Y → hom-Precategory D U V
  hom-anafunctor-Precategory = {!!}
```

## Properties

### Any functor between precategories induces an anafunctor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  anafunctor-functor-Precategory :
    functor-Precategory C D → anafunctor-Precategory l4 C D
  anafunctor-functor-Precategory = {!!}
```
