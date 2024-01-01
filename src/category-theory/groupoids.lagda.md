# Groupoids

```agda
module category-theory.groupoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.pregroupoids

open import foundation.1-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.iterated-dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **groupoid** is a [category](category-theory.categories.md) in which every
morphism is an [isomorphism](category-theory.isomorphisms-in-categories.md).

## Definition

```agda
is-groupoid-prop-Category :
  {l1 l2 : Level} (C : Category l1 l2) → Prop (l1 ⊔ l2)
is-groupoid-prop-Category C = {!!}

is-groupoid-Category :
  {l1 l2 : Level} (C : Category l1 l2) → UU (l1 ⊔ l2)
is-groupoid-Category C = {!!}

Groupoid : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Groupoid l1 l2 = {!!}

module _
  {l1 l2 : Level} (G : Groupoid l1 l2)
  where

  category-Groupoid : Category l1 l2
  category-Groupoid = {!!}

  precategory-Groupoid : Precategory l1 l2
  precategory-Groupoid = {!!}

  obj-Groupoid : UU l1
  obj-Groupoid = {!!}

  hom-set-Groupoid : obj-Groupoid → obj-Groupoid → Set l2
  hom-set-Groupoid = {!!}

  hom-Groupoid : obj-Groupoid → obj-Groupoid → UU l2
  hom-Groupoid = {!!}

  id-hom-Groupoid :
    {x : obj-Groupoid} → hom-Groupoid x x
  id-hom-Groupoid = {!!}

  comp-hom-Groupoid :
    {x y z : obj-Groupoid} →
    hom-Groupoid y z → hom-Groupoid x y → hom-Groupoid x z
  comp-hom-Groupoid = {!!}

  associative-comp-hom-Groupoid :
    {x y z w : obj-Groupoid}
    (h : hom-Groupoid z w) (g : hom-Groupoid y z) (f : hom-Groupoid x y) →
    comp-hom-Groupoid (comp-hom-Groupoid h g) f ＝
    comp-hom-Groupoid h (comp-hom-Groupoid g f)
  associative-comp-hom-Groupoid = {!!}

  inv-associative-comp-hom-Groupoid :
    {x y z w : obj-Groupoid}
    (h : hom-Groupoid z w) (g : hom-Groupoid y z) (f : hom-Groupoid x y) →
    comp-hom-Groupoid h (comp-hom-Groupoid g f) ＝
    comp-hom-Groupoid (comp-hom-Groupoid h g) f
  inv-associative-comp-hom-Groupoid = {!!}

  left-unit-law-comp-hom-Groupoid :
    {x y : obj-Groupoid} (f : hom-Groupoid x y) →
    ( comp-hom-Groupoid id-hom-Groupoid f) ＝ f
  left-unit-law-comp-hom-Groupoid = {!!}

  right-unit-law-comp-hom-Groupoid :
    {x y : obj-Groupoid} (f : hom-Groupoid x y) →
    ( comp-hom-Groupoid f id-hom-Groupoid) ＝ f
  right-unit-law-comp-hom-Groupoid = {!!}

  iso-Groupoid : (x y : obj-Groupoid) → UU l2
  iso-Groupoid = {!!}

  is-groupoid-Groupoid : is-groupoid-Category category-Groupoid
  is-groupoid-Groupoid = {!!}
```

## Property

### The type of groupoids with respect to universe levels `l1` and `l2` is equivalent to the type of 1-types in `l1`

#### The groupoid associated to a 1-type

```agda
module _
  {l : Level} (X : 1-Type l)
  where

  obj-groupoid-1-Type : UU l
  obj-groupoid-1-Type = {!!}

  precategory-Groupoid-1-Type : Precategory l l
  pr1 precategory-Groupoid-1-Type = {!!}

  is-category-groupoid-1-Type :
    is-category-Precategory precategory-Groupoid-1-Type
  is-category-groupoid-1-Type x = {!!}

  is-groupoid-groupoid-1-Type :
    is-pregroupoid-Precategory precategory-Groupoid-1-Type
  pr1 (is-groupoid-groupoid-1-Type x y p) = {!!}

  groupoid-1-Type : Groupoid l l
  pr1 (pr1 groupoid-1-Type) = {!!}
```

#### The 1-type associated to a groupoid

```agda
module _
  {l1 l2 : Level} (G : Groupoid l1 l2)
  where

  1-type-Groupoid : 1-Type l1
  1-type-Groupoid = {!!}
```

#### The groupoid obtained from the 1-type induced by a groupoid `G` is `G` itself

```agda
module _
  {l1 l2 : Level} (G : Groupoid l1 l2)
  where

  functor-equiv-groupoid-1-type-Groupoid :
    functor-Category
      ( category-Groupoid (groupoid-1-Type (1-type-Groupoid G)))
      ( category-Groupoid G)
  pr1 functor-equiv-groupoid-1-type-Groupoid = {!!}
```

#### The 1-type obtained from the groupoid induced by a 1-type `X` is `X` itself

```agda
module _
  {l : Level} (X : 1-Type l)
  where

  equiv-1-type-groupoid-1-Type :
    type-equiv-1-Type (1-type-Groupoid (groupoid-1-Type X)) X
  equiv-1-type-groupoid-1-Type = {!!}
```

## External links

- [univalent groupoid](https://ncatlab.org/nlab/show/univalent+groupoid) at
  $n$Lab
