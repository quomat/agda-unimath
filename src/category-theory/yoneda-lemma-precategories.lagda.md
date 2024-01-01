# The Yoneda lemma for precategories

```agda
module category-theory.yoneda-lemma-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.copresheaf-categories
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.precategories
open import category-theory.representable-functors-precategories

open import foundation.action-on-identifications-functions
open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, an object `c`, and
a [functor](category-theory.functors-precategories.md) `F` from `C` to the
[category of sets](foundation.category-of-sets.md)

```text
  F : C → Set,
```

there is an [equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-functors-precategories.md)
from the functor
[represented](category-theory.representable-functors-precategories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

```text
  Nat(Hom(c , -) , F) ≃ F c
```

More precisely, the **Yoneda lemma** asserts that the map from the type of
natural transformations to the type `F c` defined by evaluating the component of
the natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Theorem

### The yoneda lemma into the large category of sets

```agda
module _
  {l1 l2 l3 : Level} (C : Precategory l1 l2) (c : obj-Precategory C)
  (F : copresheaf-Precategory C l3)
  where

  map-yoneda-Precategory :
    hom-copresheaf-Precategory C (representable-functor-Precategory C c) F →
    element-copresheaf-Precategory C F c
  map-yoneda-Precategory σ = {!!}
```

The inverse to the Yoneda map:

```agda
  hom-family-extension-yoneda-Precategory :
    (u : element-copresheaf-Precategory C F c) →
    hom-family-functor-Small-Large-Precategory
      C Set-Large-Precategory (representable-functor-Precategory C c) F
  hom-family-extension-yoneda-Precategory u x f = {!!}

  naturality-extension-yoneda-Precategory :
    (u : element-copresheaf-Precategory C F c) →
    is-natural-transformation-Small-Large-Precategory
      C Set-Large-Precategory (representable-functor-Precategory C c) F
      ( hom-family-extension-yoneda-Precategory u)
  naturality-extension-yoneda-Precategory u g = {!!}

  extension-yoneda-Precategory :
    element-copresheaf-Precategory C F c →
    hom-copresheaf-Precategory C (representable-functor-Precategory C c) F
  pr1 (extension-yoneda-Precategory u) = {!!}
```

The inverse is an inverse:

```agda
  is-section-extension-yoneda-Precategory :
    ( map-yoneda-Precategory ∘
      extension-yoneda-Precategory) ~
    id
  is-section-extension-yoneda-Precategory = {!!}

  is-retraction-extension-yoneda-Precategory :
    ( extension-yoneda-Precategory ∘
      map-yoneda-Precategory) ~
    id
  is-retraction-extension-yoneda-Precategory σ = {!!}

  lemma-yoneda-Precategory : is-equiv map-yoneda-Precategory
  lemma-yoneda-Precategory = {!!}

  equiv-lemma-yoneda-Precategory :
    hom-copresheaf-Precategory C (representable-functor-Precategory C c) F ≃
    element-copresheaf-Precategory C F c
  pr1 equiv-lemma-yoneda-Precategory = {!!}
```

## Corollaries

### The Yoneda lemma for representable functors

An important special-case of the Yoneda lemma is when `F` is itself a
representable functor `F = {!!}

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (c d : obj-Precategory C)
  where

  equiv-lemma-yoneda-representable-Precategory :
    hom-copresheaf-Precategory C
      ( representable-functor-Precategory C c)
      ( representable-functor-Precategory C d) ≃
    hom-Precategory C d c
  equiv-lemma-yoneda-representable-Precategory = {!!}
```

## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

## External links

- [The Yoneda embedding](https://1lab.dev/Cat.Functor.Hom.html#the-yoneda-embedding)
  at 1lab
- [Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma) at $n$Lab
- [The Yoneda lemma](https://www.math3ma.com/blog/the-yoneda-lemma) at Math3ma
- [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) at Wikipedia
- [Yoneda lemma](https://www.wikidata.org/wiki/Q320577) at Wikidata
