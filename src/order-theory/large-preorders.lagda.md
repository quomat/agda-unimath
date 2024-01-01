# Large preorders

```agda
module order-theory.large-preorders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **large preorder** consists of types indexed by a universe levels, and an
ordering relation comparing objects of arbitrary universe levels. This level of
generality therefore accommodates the inclusion relation on subtypes of
different universe levels. Many [preorders](order-theory.preorders.md) in
agda-unimath naturally arise as large preorders.

## Definitions

### Large preorders

```agda
record
  Large-Preorder (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Preorder
  field
    type-Large-Preorder : (l : Level) → UU (α l)
    leq-prop-Large-Preorder : Large-Relation-Prop α β type-Large-Preorder
    refl-leq-Large-Preorder :
      is-reflexive-Large-Relation-Prop
        ( type-Large-Preorder)
        ( leq-prop-Large-Preorder)
    transitive-leq-Large-Preorder :
      is-transitive-Large-Relation-Prop
        ( type-Large-Preorder)
        ( leq-prop-Large-Preorder)

open Large-Preorder public

module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Preorder α β)
  where

  leq-Large-Preorder : Large-Relation α β (type-Large-Preorder X)
  leq-Large-Preorder = {!!}

  is-prop-leq-Large-Preorder :
    is-prop-Large-Relation (type-Large-Preorder X) (leq-Large-Preorder)
  is-prop-leq-Large-Preorder = {!!}

  leq-eq-Large-Preorder :
    {l1 : Level}
    {x y : type-Large-Preorder X l1} →
    (x ＝ y) → leq-Large-Preorder x y
  leq-eq-Large-Preorder {x = x} refl = {!!}
```

### The predicate on large precategories to be a large preorder

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  is-large-preorder-Large-Precategory : UUω
  is-large-preorder-Large-Precategory = {!!}

  large-preorder-Large-Precategory :
    is-large-preorder-Large-Precategory → Large-Preorder α β
  type-Large-Preorder
    ( large-preorder-Large-Precategory H) = {!!}
  pr1 (leq-prop-Large-Preorder (large-preorder-Large-Precategory H) X Y) = {!!}
  pr2 (leq-prop-Large-Preorder (large-preorder-Large-Precategory H) X Y) = {!!}
  refl-leq-Large-Preorder
    ( large-preorder-Large-Precategory H)
    ( X) = {!!}
  transitive-leq-Large-Preorder
    ( large-preorder-Large-Precategory H)
    ( X)
    ( Y)
    ( Z) = {!!}
```

## Properties

### Small preorders from large preorders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  preorder-Large-Preorder : (l : Level) → Preorder (α l) (β l l)
  pr1 (preorder-Large-Preorder l) = {!!}
```

### Large preorders are large precategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  large-precategory-Large-Preorder : Large-Precategory α β
  obj-Large-Precategory large-precategory-Large-Preorder = {!!}
```
