# Large function categories

```agda
module category-theory.large-function-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-large-categories
open import category-theory.isomorphisms-in-large-categories
open import category-theory.large-categories

open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a type `I` and a [large category](category-theory.large-categories.md)
`C`, the **large function category** `Cᴵ` consists of `I`-indexed families of
objects of `C` and `I`-indexed familis of morphisms between them.

## Definition

### Large function categories

```agda
module _
  {l1 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : Large-Category α β)
  where

  Large-Function-Category :
    Large-Category (λ l2 → l1 ⊔ α l2) (λ l2 l3 → l1 ⊔ β l2 l3)
  Large-Function-Category = {!!}

  obj-Large-Function-Category : (l2 : Level) → UU (l1 ⊔ α l2)
  obj-Large-Function-Category = {!!}

  hom-set-Large-Function-Category :
    {l2 l3 : Level} →
    obj-Large-Function-Category l2 → obj-Large-Function-Category l3 →
    Set (l1 ⊔ β l2 l3)
  hom-set-Large-Function-Category = {!!}

  hom-Large-Function-Category :
    {l2 l3 : Level} →
    obj-Large-Function-Category l2 → obj-Large-Function-Category l3 →
    UU (l1 ⊔ β l2 l3)
  hom-Large-Function-Category = {!!}

  comp-hom-Large-Function-Category :
    {l2 l3 l4 : Level}
    {x : obj-Large-Function-Category l2}
    {y : obj-Large-Function-Category l3}
    {z : obj-Large-Function-Category l4} →
    hom-Large-Function-Category y z →
    hom-Large-Function-Category x y →
    hom-Large-Function-Category x z
  comp-hom-Large-Function-Category = {!!}

  associative-comp-hom-Large-Function-Category :
    {l2 l3 l4 l5 : Level}
    {x : obj-Large-Function-Category l2}
    {y : obj-Large-Function-Category l3}
    {z : obj-Large-Function-Category l4}
    {w : obj-Large-Function-Category l5} →
    (h : hom-Large-Function-Category z w)
    (g : hom-Large-Function-Category y z)
    (f : hom-Large-Function-Category x y) →
    comp-hom-Large-Function-Category (comp-hom-Large-Function-Category h g) f ＝
    comp-hom-Large-Function-Category h (comp-hom-Large-Function-Category g f)
  associative-comp-hom-Large-Function-Category = {!!}

  inv-associative-comp-hom-Large-Function-Category :
    {l2 l3 l4 l5 : Level}
    {x : obj-Large-Function-Category l2}
    {y : obj-Large-Function-Category l3}
    {z : obj-Large-Function-Category l4}
    {w : obj-Large-Function-Category l5} →
    (h : hom-Large-Function-Category z w)
    (g : hom-Large-Function-Category y z)
    (f : hom-Large-Function-Category x y) →
    comp-hom-Large-Function-Category h (comp-hom-Large-Function-Category g f) ＝
    comp-hom-Large-Function-Category (comp-hom-Large-Function-Category h g) f
  inv-associative-comp-hom-Large-Function-Category = {!!}

  id-hom-Large-Function-Category :
    {l2 : Level} {x : obj-Large-Function-Category l2} →
    hom-Large-Function-Category x x
  id-hom-Large-Function-Category = {!!}

  left-unit-law-comp-hom-Large-Function-Category :
    {l2 l3 : Level}
    {x : obj-Large-Function-Category l2}
    {y : obj-Large-Function-Category l3}
    (f : hom-Large-Function-Category x y) →
    comp-hom-Large-Function-Category id-hom-Large-Function-Category f ＝ f
  left-unit-law-comp-hom-Large-Function-Category = {!!}

  right-unit-law-comp-hom-Large-Function-Category :
    {l2 l3 : Level}
    {x : obj-Large-Function-Category l2}
    {y : obj-Large-Function-Category l3}
    (f : hom-Large-Function-Category x y) →
    comp-hom-Large-Function-Category f id-hom-Large-Function-Category ＝ f
  right-unit-law-comp-hom-Large-Function-Category = {!!}
```

## Properties

### Isomorphisms in the dependent product category are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : Large-Category α β)
  {x : obj-Large-Function-Category I C l2}
  {y : obj-Large-Function-Category I C l3}
  where

  is-fiberwise-iso-is-iso-Large-Function-Category :
    (f : hom-Large-Function-Category I C x y) →
    is-iso-Large-Category (Large-Function-Category I C) f →
    (i : I) → is-iso-Large-Category C (f i)
  is-fiberwise-iso-is-iso-Large-Function-Category = {!!}

  fiberwise-iso-iso-Large-Function-Category :
    iso-Large-Category (Large-Function-Category I C) x y →
    (i : I) → iso-Large-Category C (x i) (y i)
  fiberwise-iso-iso-Large-Function-Category = {!!}

  is-iso-is-fiberwise-iso-Large-Function-Category :
    (f : hom-Large-Function-Category I C x y) →
    ((i : I) → is-iso-Large-Category C (f i)) →
    is-iso-Large-Category (Large-Function-Category I C) f
  is-iso-is-fiberwise-iso-Large-Function-Category = {!!}

  iso-fiberwise-iso-Large-Function-Category :
    ((i : I) → iso-Large-Category C (x i) (y i)) →
    iso-Large-Category (Large-Function-Category I C) x y
  iso-fiberwise-iso-Large-Function-Category = {!!}

  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Category :
    (f : hom-Large-Function-Category I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Large-Function-Category f)
  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Category = {!!}

  equiv-is-fiberwise-iso-is-iso-Large-Function-Category :
    (f : hom-Large-Function-Category I C x y) →
    ( is-iso-Large-Category (Large-Function-Category I C) f) ≃
    ( (i : I) → is-iso-Large-Category C (f i))
  equiv-is-fiberwise-iso-is-iso-Large-Function-Category = {!!}

  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Category :
    (f : hom-Large-Function-Category I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Large-Function-Category f)
  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Category = {!!}

  equiv-is-iso-is-fiberwise-iso-Large-Function-Category :
    ( f : hom-Large-Function-Category I C x y) →
    ( (i : I) → is-iso-Large-Category C (f i)) ≃
    ( is-iso-Large-Category (Large-Function-Category I C) f)
  equiv-is-iso-is-fiberwise-iso-Large-Function-Category = {!!}

  is-equiv-fiberwise-iso-iso-Large-Function-Category :
    is-equiv fiberwise-iso-iso-Large-Function-Category
  is-equiv-fiberwise-iso-iso-Large-Function-Category = {!!}

  equiv-fiberwise-iso-iso-Large-Function-Category :
    ( iso-Large-Category (Large-Function-Category I C) x y) ≃
    ( (i : I) → iso-Large-Category C (x i) (y i))
  equiv-fiberwise-iso-iso-Large-Function-Category = {!!}

  is-equiv-iso-fiberwise-iso-Large-Function-Category :
    is-equiv iso-fiberwise-iso-Large-Function-Category
  is-equiv-iso-fiberwise-iso-Large-Function-Category = {!!}

  equiv-iso-fiberwise-iso-Large-Function-Category :
    ( (i : I) → iso-Large-Category C (x i) (y i)) ≃
    ( iso-Large-Category (Large-Function-Category I C) x y)
  equiv-iso-fiberwise-iso-Large-Function-Category = {!!}
```
