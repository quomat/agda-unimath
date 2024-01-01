# Isomorphisms in subprecategories

```agda
module category-theory.isomorphisms-in-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.subprecategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Definitions

### Isomorphisms in subprecategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  (f : hom-Subprecategory C P x y)
  where

  is-iso-prop-Subprecategory : Prop (l2 ⊔ l4)
  is-iso-prop-Subprecategory = {!!}

  is-iso-Subprecategory : UU (l2 ⊔ l4)
  is-iso-Subprecategory = {!!}

  is-prop-is-iso-Subprecategory : is-prop is-iso-Subprecategory
  is-prop-is-iso-Subprecategory = {!!}
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (x y : obj-Subprecategory C P)
  where

  iso-set-Subprecategory : Set (l2 ⊔ l4)
  iso-set-Subprecategory = {!!}

  iso-Subprecategory : UU (l2 ⊔ l4)
  iso-Subprecategory = {!!}

  is-set-iso-Subprecategory : is-set iso-Subprecategory
  is-set-iso-Subprecategory = {!!}
```

#### The predicate on an isomorphism proof of being contained in a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  (f : hom-Subprecategory C P x y)
  (is-iso-f : is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f))
  where

  is-in-is-iso-prop-Subprecategory : Prop l4
  is-in-is-iso-prop-Subprecategory = {!!}

  is-in-is-iso-Subprecategory : UU l4
  is-in-is-iso-Subprecategory = {!!}

  is-prop-is-in-is-iso-Subprecategory : is-prop is-in-is-iso-Subprecategory
  is-prop-is-in-is-iso-Subprecategory = {!!}

  is-iso-is-in-is-iso-Subprecategory :
    is-in-is-iso-Subprecategory → is-iso-Subprecategory C P f
  pr1 (pr1 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) = {!!}
```

#### The predicate on an isomorphism between objects in the subprecategory of being contained in the subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  (f :
    iso-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y))
  where

  is-in-iso-obj-subprecategory-prop-Subprecategory : Prop l4
  is-in-iso-obj-subprecategory-prop-Subprecategory = {!!}

  is-in-iso-obj-subprecategory-Subprecategory : UU l4
  is-in-iso-obj-subprecategory-Subprecategory = {!!}

  is-prop-is-in-iso-obj-subprecategory-Subprecategory :
    is-prop is-in-iso-obj-subprecategory-Subprecategory
  is-prop-is-in-iso-obj-subprecategory-Subprecategory = {!!}

  is-iso-is-in-iso-obj-subprecategory-Subprecategory :
    ((f₀ , f₁) : is-in-iso-obj-subprecategory-Subprecategory) →
    is-iso-Subprecategory C P (hom-iso-Precategory C f , f₀)
  is-iso-is-in-iso-obj-subprecategory-Subprecategory (f₀ , f₁) = {!!}

  iso-is-in-iso-obj-subprecategory-Subprecategory :
    is-in-iso-obj-subprecategory-Subprecategory → iso-Subprecategory C P x y
  pr1 (pr1 (iso-is-in-iso-obj-subprecategory-Subprecategory is-in-iso-f)) = {!!}
```

#### The predicate on an isomorphism between any objects of being contained in the subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  is-in-iso-prop-Subprecategory : Prop (l3 ⊔ l4)
  is-in-iso-prop-Subprecategory = {!!}

  is-in-iso-Subprecategory : UU (l3 ⊔ l4)
  is-in-iso-Subprecategory = {!!}

  is-prop-is-in-iso-Subprecategory : is-prop is-in-iso-Subprecategory
  is-prop-is-in-iso-Subprecategory = {!!}

  iso-is-in-iso-Subprecategory :
    (is-in-iso-f : is-in-iso-Subprecategory) →
    iso-Subprecategory C P (x , pr1 is-in-iso-f) (y , pr1 (pr2 is-in-iso-f))
  iso-is-in-iso-Subprecategory is-in-iso-f = {!!}

  is-iso-is-in-iso-Subprecategory :
    ( is-in-iso-f : is-in-iso-Subprecategory) →
    is-iso-Subprecategory C P
      ( pr1 f , pr2 (pr1 (iso-is-in-iso-Subprecategory is-in-iso-f)))
  is-iso-is-in-iso-Subprecategory is-in-iso-f = {!!}
```

### If a subprecategory contains an object, it contains its identity ismorphism

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (x : obj-Subprecategory C P)
  where

  is-iso-id-hom-Subprecategory :
    is-iso-Subprecategory C P (id-hom-Subprecategory C P {x})
  is-iso-id-hom-Subprecategory = {!!}

  is-in-is-iso-id-obj-subprecategory-Subprecategory :
    is-in-is-iso-Subprecategory C P {x}
      (id-hom-Subprecategory C P) (is-iso-id-hom-Precategory C)
  is-in-is-iso-id-obj-subprecategory-Subprecategory = {!!}

  is-in-iso-id-obj-subprecategory-Subprecategory :
    is-in-iso-obj-subprecategory-Subprecategory C P (id-iso-Precategory C)
  pr1 is-in-iso-id-obj-subprecategory-Subprecategory = {!!}

  is-in-iso-id-Subprecategory :
    is-in-iso-Subprecategory C P (id-iso-Precategory C)
  pr1 is-in-iso-id-Subprecategory = {!!}
```

## Properties

### Isomorphisms in a subprecategory are isomorphisms in the base category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  where

  is-iso-base-is-iso-Subprecategory :
    {f : hom-Subprecategory C P x y} →
    is-iso-Subprecategory C P f →
    is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f)
  pr1 (is-iso-base-is-iso-Subprecategory is-iso-f) = {!!}
```
