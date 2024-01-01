# Conservative functors between precategories

```agda
module category-theory.conservative-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) is **conservative** if every
morphism that is mapped to an
[isomorphism](category-theory.isomorphisms-in-precategories.md) in `D` is an
isomorphism in `C`.

## Definitions

### The predicate of being conservative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-conservative-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-conservative-functor-Precategory = {!!}

  is-prop-is-conservative-functor-Precategory :
    is-prop is-conservative-functor-Precategory
  is-prop-is-conservative-functor-Precategory = {!!}

  is-conservative-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-conservative-prop-functor-Precategory = {!!}
```

### The type of conservative functors

```agda
conservative-functor-Precategory :
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
conservative-functor-Precategory = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : conservative-functor-Precategory C D)
  where

  functor-conservative-functor-Precategory :
    functor-Precategory C D
  functor-conservative-functor-Precategory = {!!}

  is-conservative-conservative-functor-Precategory :
    is-conservative-functor-Precategory C D
      ( functor-conservative-functor-Precategory)
  is-conservative-conservative-functor-Precategory = {!!}

  obj-conservative-functor-Precategory :
    obj-Precategory C → obj-Precategory D
  obj-conservative-functor-Precategory = {!!}

  hom-conservative-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-conservative-functor-Precategory x)
      ( obj-conservative-functor-Precategory y)
  hom-conservative-functor-Precategory = {!!}
```

## See also

- [Essentially injective functors](category-theory.essentially-injective-functors-precategories.md)

- [Pseudomonic functors](category-theory.pseudomonic-functors-precategories.md)
  are conservative.
- [Fully faithful functors](category-theory.fully-faithful-functors-precategories.md)
  are conservative.

## External links

- [Conservative Functors](https://1lab.dev/Cat.Functor.Conservative.html) at
  1lab
- [conservative functor](https://ncatlab.org/nlab/show/conservative+functor) at
  $n$Lab
- [Conservative functor](https://en.wikipedia.org/wiki/Conservative_functor) at
  Wikipedia
