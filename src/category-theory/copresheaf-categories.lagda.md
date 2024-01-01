# Copresheaf categories

```agda
module category-theory.copresheaf-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.category-of-functors-from-small-to-large-categories
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.functors-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors-from-small-to-large-precategories

open import foundation.category-of-sets
open import foundation.commuting-squares-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, we can form its
**copresheaf [category](category-theory.large-categories.md)** as the
[large category of functors](category-theory.functors-from-small-to-large-precategories.md)
from `C`, into the [large category of sets](foundation.category-of-sets.md)

```text
  C → Set.
```

To this large category, there is an associated
[small category](category-theory.categories.md) of small copresheaves, taking
values in small [sets](foundation-core.sets.md).

## Definitions

### The large category of copresheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  copresheaf-large-precategory-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  copresheaf-large-precategory-Precategory = {!!}

  is-large-category-copresheaf-large-category-Precategory :
    is-large-category-Large-Precategory copresheaf-large-precategory-Precategory
  is-large-category-copresheaf-large-category-Precategory = {!!}

  copresheaf-large-category-Precategory :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  copresheaf-large-category-Precategory = {!!}

  copresheaf-Precategory :
    (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  copresheaf-Precategory = {!!}

  module _
    {l : Level} (P : copresheaf-Precategory l)
    where

    element-set-copresheaf-Precategory : obj-Precategory C → Set l
    element-set-copresheaf-Precategory = {!!}

    element-copresheaf-Precategory : obj-Precategory C → UU l
    element-copresheaf-Precategory = {!!}

    action-copresheaf-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      element-copresheaf-Precategory X → element-copresheaf-Precategory Y
    action-copresheaf-Precategory = {!!}

    preserves-id-action-copresheaf-Precategory :
      {X : obj-Precategory C} →
      action-copresheaf-Precategory {X} {X} (id-hom-Precategory C) ~ id
    preserves-id-action-copresheaf-Precategory = {!!}

    preserves-comp-action-copresheaf-Precategory :
      {X Y Z : obj-Precategory C}
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      action-copresheaf-Precategory (comp-hom-Precategory C g f) ~
      action-copresheaf-Precategory g ∘ action-copresheaf-Precategory f
    preserves-comp-action-copresheaf-Precategory = {!!}

  hom-set-copresheaf-Precategory :
    {l3 l4 : Level}
    (P : copresheaf-Precategory l3)
    (Q : copresheaf-Precategory l4) → Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-copresheaf-Precategory = {!!}

  hom-copresheaf-Precategory :
    {l3 l4 : Level}
    (X : copresheaf-Precategory l3) (Y : copresheaf-Precategory l4) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-copresheaf-Precategory = {!!}

  module _
    {l3 l4 : Level}
    (P : copresheaf-Precategory l3) (Q : copresheaf-Precategory l4)
    (h : hom-copresheaf-Precategory P Q)
    where

    map-hom-copresheaf-Precategory :
      (X : obj-Precategory C) →
      element-copresheaf-Precategory P X → element-copresheaf-Precategory Q X
    map-hom-copresheaf-Precategory = {!!}

    naturality-hom-copresheaf-Precategory :
      {X Y : obj-Precategory C} (f : hom-Precategory C X Y) →
      coherence-square-maps
        ( action-copresheaf-Precategory P f)
        ( map-hom-copresheaf-Precategory X)
        ( map-hom-copresheaf-Precategory Y)
        ( action-copresheaf-Precategory Q f)
    naturality-hom-copresheaf-Precategory = {!!}

  comp-hom-copresheaf-Precategory :
    {l3 l4 l5 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (Z : copresheaf-Precategory l5) →
    hom-copresheaf-Precategory Y Z →
    hom-copresheaf-Precategory X Y →
    hom-copresheaf-Precategory X Z
  comp-hom-copresheaf-Precategory = {!!}

  id-hom-copresheaf-Precategory :
    {l3 : Level} (X : copresheaf-Precategory l3) →
    hom-copresheaf-Precategory X X
  id-hom-copresheaf-Precategory = {!!}

  associative-comp-hom-copresheaf-Precategory :
    {l3 l4 l5 l6 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (Z : copresheaf-Precategory l5)
    (W : copresheaf-Precategory l6)
    (h : hom-copresheaf-Precategory Z W)
    (g : hom-copresheaf-Precategory Y Z)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X Y W
      ( comp-hom-copresheaf-Precategory Y Z W h g)
      ( f) ＝
    comp-hom-copresheaf-Precategory X Z W
      ( h)
      ( comp-hom-copresheaf-Precategory X Y Z g f)
  associative-comp-hom-copresheaf-Precategory = {!!}

  inv-associative-comp-hom-copresheaf-Precategory :
    {l3 l4 l5 l6 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (Z : copresheaf-Precategory l5)
    (W : copresheaf-Precategory l6)
    (h : hom-copresheaf-Precategory Z W)
    (g : hom-copresheaf-Precategory Y Z)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X Z W
      ( h)
      ( comp-hom-copresheaf-Precategory X Y Z g f) ＝
    comp-hom-copresheaf-Precategory X Y W
      ( comp-hom-copresheaf-Precategory Y Z W h g)
      ( f)
  inv-associative-comp-hom-copresheaf-Precategory = {!!}

  left-unit-law-comp-hom-copresheaf-Precategory :
    {l3 l4 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X Y Y
      ( id-hom-copresheaf-Precategory Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-copresheaf-Precategory = {!!}

  right-unit-law-comp-hom-copresheaf-Precategory :
    {l3 l4 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X X Y
      ( f)
      ( id-hom-copresheaf-Precategory X) ＝
    f
  right-unit-law-comp-hom-copresheaf-Precategory = {!!}
```

### The category of small copresheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  copresheaf-category-Precategory :
    Category (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  copresheaf-category-Precategory = {!!}

  copresheaf-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  copresheaf-precategory-Precategory = {!!}
```

## See also

- [The Yoneda lemma](category-theory.yoneda-lemma-precategories.md)

## External links

- [Presheaf precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategories)
  at 1lab
- [category of presheaves](https://ncatlab.org/nlab/show/category+of+presheaves)
  at $n$Lab
- [copresheaf](https://ncatlab.org/nlab/show/copresheaf) at $n$Lab
