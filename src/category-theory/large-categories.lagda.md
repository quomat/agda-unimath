# Large categories

```agda
module category-theory.large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **large category** in Homotopy Type Theory is a
[large precategory](category-theory.large-precategories.md) for which the
[identities](foundation-core.identity-types.md) between the objects are the
[isomorphisms](category-theory.isomorphisms-in-large-categories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A large precategory is a large category if this function is
an equivalence. Note that being a large category is a
[proposition](foundation-core.propositions.md) since `is-equiv` is a
proposition.

## Definition

### The predicate on large precategories of being a large category

```agda
is-large-category-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precategory α β) → UUω
is-large-category-Large-Precategory C = {!!}
```

### The large type of large categories

```agda
record
  Large-Category (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Category

  field
    large-precategory-Large-Category :
      Large-Precategory α β

    is-large-category-Large-Category :
      is-large-category-Large-Precategory large-precategory-Large-Category

open Large-Category public
```

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  where

  obj-Large-Category : (l : Level) → UU (α l)
  obj-Large-Category = {!!}

  hom-set-Large-Category :
    {l1 l2 : Level} →
    obj-Large-Category l1 →
    obj-Large-Category l2 →
    Set (β l1 l2)
  hom-set-Large-Category = {!!}

  hom-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category l1)
    (Y : obj-Large-Category l2) →
    UU (β l1 l2)
  hom-Large-Category X Y = {!!}

  is-set-hom-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category l1)
    (Y : obj-Large-Category l2) →
    is-set (hom-Large-Category X Y)
  is-set-hom-Large-Category X Y = {!!}

  comp-hom-Large-Category :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3} →
    hom-Large-Category Y Z →
    hom-Large-Category X Y →
    hom-Large-Category X Z
  comp-hom-Large-Category = {!!}

  id-hom-Large-Category :
    {l1 : Level} {X : obj-Large-Category l1} →
    hom-Large-Category X X
  id-hom-Large-Category = {!!}

  associative-comp-hom-Large-Category :
    {l1 l2 l3 l4 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3}
    {W : obj-Large-Category l4} →
    (h : hom-Large-Category Z W)
    (g : hom-Large-Category Y Z)
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category (comp-hom-Large-Category h g) f) ＝
    ( comp-hom-Large-Category h (comp-hom-Large-Category g f))
  associative-comp-hom-Large-Category = {!!}

  inv-associative-comp-hom-Large-Category :
    {l1 l2 l3 l4 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3}
    {W : obj-Large-Category l4} →
    (h : hom-Large-Category Z W)
    (g : hom-Large-Category Y Z)
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category h (comp-hom-Large-Category g f)) ＝
    ( comp-hom-Large-Category (comp-hom-Large-Category h g) f)
  inv-associative-comp-hom-Large-Category = {!!}

  left-unit-law-comp-hom-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category id-hom-Large-Category f) ＝ f
  left-unit-law-comp-hom-Large-Category = {!!}

  right-unit-law-comp-hom-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category f id-hom-Large-Category) ＝ f
  right-unit-law-comp-hom-Large-Category = {!!}

  ap-comp-hom-Large-Category :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3}
    {g g' : hom-Large-Category Y Z} (p : g ＝ g')
    {f f' : hom-Large-Category X Y} (q : f ＝ f') →
    comp-hom-Large-Category g f ＝ comp-hom-Large-Category g' f'
  ap-comp-hom-Large-Category p q = {!!}

  comp-hom-Large-Category' :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3} →
    hom-Large-Category X Y →
    hom-Large-Category Y Z →
    hom-Large-Category X Z
  comp-hom-Large-Category' f g = {!!}
```

### Categories obtained from large categories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  (is-large-category-C : is-large-category-Large-Precategory C)
  where

  is-category-is-large-category-Large-Precategory :
    (l : Level) → is-category-Precategory (precategory-Large-Precategory C l)
  is-category-is-large-category-Large-Precategory l X Y = {!!}

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  where

  precategory-Large-Category : (l : Level) → Precategory (α l) (β l l)
  precategory-Large-Category = {!!}

  is-category-Large-Category :
    (l : Level) → is-category-Precategory (precategory-Large-Category l)
  is-category-Large-Category = {!!}

  category-Large-Category : (l : Level) → Category (α l) (β l l)
  pr1 (category-Large-Category l) = {!!}
```

### Equalities induce morphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  {l1 : Level} (X Y : obj-Large-Category C l1)
  where

  hom-eq-Large-Category : X ＝ Y → hom-Large-Category C X Y
  hom-eq-Large-Category = {!!}

  hom-inv-eq-Large-Category : X ＝ Y → hom-Large-Category C Y X
  hom-inv-eq-Large-Category = {!!}

  compute-hom-eq-Large-Category :
    hom-eq-Category (category-Large-Category C l1) X Y ~ hom-eq-Large-Category
  compute-hom-eq-Large-Category = {!!}
```

### Pre- and postcomposing by a morphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  {l1 l2 l3 : Level}
  where

  precomp-hom-Large-Category :
    {X : obj-Large-Category C l1}
    {Y : obj-Large-Category C l2}
    (f : hom-Large-Category C X Y) →
    (Z : obj-Large-Category C l3) →
    hom-Large-Category C Y Z → hom-Large-Category C X Z
  precomp-hom-Large-Category f Z g = {!!}

  postcomp-hom-Large-Category :
    (X : obj-Large-Category C l1)
    {Y : obj-Large-Category C l2}
    {Z : obj-Large-Category C l3}
    (f : hom-Large-Category C Y Z) →
    hom-Large-Category C X Y → hom-Large-Category C X Z
  postcomp-hom-Large-Category X f g = {!!}
```
