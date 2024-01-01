# Pregroupoids

```agda
module category-theory.pregroupoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **pregroupoid** is a [precategory](category-theory.precategories.md) in which
every morphism is an
[isomorphism](category-theory.isomorphisms-in-precategories.md).

## Definitions

### The predicate on precategories of being pregroupoids

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pregroupoid-Precategory : UU (l1 ⊔ l2)
  is-pregroupoid-Precategory = {!!}

  is-prop-is-pregroupoid-Precategory : is-prop is-pregroupoid-Precategory
  is-prop-is-pregroupoid-Precategory = {!!}

  is-pregroupoid-prop-Precategory : Prop (l1 ⊔ l2)
  is-pregroupoid-prop-Precategory = {!!}
```

### The type of pregroupoids

```agda
Pregroupoid :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pregroupoid = {!!}

module _
  {l1 l2 : Level} (G : Pregroupoid l1 l2)
  where

  precategory-Pregroupoid : Precategory l1 l2
  precategory-Pregroupoid = {!!}

  is-pregroupoid-Pregroupoid :
    is-pregroupoid-Precategory precategory-Pregroupoid
  is-pregroupoid-Pregroupoid = {!!}

  obj-Pregroupoid : UU l1
  obj-Pregroupoid = {!!}

  hom-set-Pregroupoid : obj-Pregroupoid → obj-Pregroupoid → Set l2
  hom-set-Pregroupoid = {!!}

  hom-Pregroupoid : obj-Pregroupoid → obj-Pregroupoid → UU l2
  hom-Pregroupoid = {!!}

  id-hom-Pregroupoid :
    {x : obj-Pregroupoid} → hom-Pregroupoid x x
  id-hom-Pregroupoid = {!!}

  comp-hom-Pregroupoid :
    {x y z : obj-Pregroupoid} → hom-Pregroupoid y z →
    hom-Pregroupoid x y → hom-Pregroupoid x z
  comp-hom-Pregroupoid = {!!}

  associative-comp-hom-Pregroupoid :
    {x y z w : obj-Pregroupoid} (h : hom-Pregroupoid z w)
    (g : hom-Pregroupoid y z) (f : hom-Pregroupoid x y) →
    comp-hom-Pregroupoid (comp-hom-Pregroupoid h g) f ＝
    comp-hom-Pregroupoid h (comp-hom-Pregroupoid g f)
  associative-comp-hom-Pregroupoid = {!!}

  inv-associative-comp-hom-Pregroupoid :
    {x y z w : obj-Pregroupoid} (h : hom-Pregroupoid z w)
    (g : hom-Pregroupoid y z) (f : hom-Pregroupoid x y) →
    comp-hom-Pregroupoid h (comp-hom-Pregroupoid g f) ＝
    comp-hom-Pregroupoid (comp-hom-Pregroupoid h g) f
  inv-associative-comp-hom-Pregroupoid = {!!}

  left-unit-law-comp-hom-Pregroupoid :
    {x y : obj-Pregroupoid} (f : hom-Pregroupoid x y) →
    ( comp-hom-Pregroupoid id-hom-Pregroupoid f) ＝ f
  left-unit-law-comp-hom-Pregroupoid = {!!}

  right-unit-law-comp-hom-Pregroupoid :
    {x y : obj-Pregroupoid} (f : hom-Pregroupoid x y) →
    ( comp-hom-Pregroupoid f id-hom-Pregroupoid) ＝ f
  right-unit-law-comp-hom-Pregroupoid = {!!}

  iso-Pregroupoid : (x y : obj-Pregroupoid) → UU l2
  iso-Pregroupoid = {!!}
```

## Properties

### The type of isomorphisms in a pregroupoid is equivalent to the type of morphisms

```agda
module _
  {l1 l2 : Level} (G : Pregroupoid l1 l2)
  where

  inv-compute-iso-Pregroupoid :
    {x y : obj-Pregroupoid G} → iso-Pregroupoid G x y ≃ hom-Pregroupoid G x y
  inv-compute-iso-Pregroupoid = {!!}

  compute-iso-Pregroupoid :
    {x y : obj-Pregroupoid G} → hom-Pregroupoid G x y ≃ iso-Pregroupoid G x y
  compute-iso-Pregroupoid = {!!}
```

## See also

- [Cores of precategories](category-theory.cores-precategories.md)

## External links

- [Groupoids](https://1lab.dev/Cat.Groupoid.html) at 1lab
- [pregroupoid](https://ncatlab.org/nlab/show/pregroupoid) at $n$Lab
