# Cores of precategories

```agda
module category-theory.cores-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.pregroupoids
open import category-theory.replete-subprecategories
open import category-theory.subprecategories
open import category-theory.wide-subprecategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **core of a [precategory](category-theory.precategories.md)** `C` is the
maximal subpregroupoid of it. It consists of all objects and
[isomorphisms](category-theory.isomorphisms-in-precategories.md) in `C`.

## Definitions

### The core wide subprecategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  core-wide-subprecategory-Precategory : Wide-Subprecategory l2 C
  core-wide-subprecategory-Precategory = {!!}
```

### The core subprecategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  core-subprecategory-Precategory : Subprecategory lzero l2 C
  core-subprecategory-Precategory = {!!}

  is-wide-core-Precategory :
    is-wide-Subprecategory C core-subprecategory-Precategory
  is-wide-core-Precategory = {!!}
```

### The core precategory

```agda
core-precategory-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → Precategory l1 l2
core-precategory-Precategory = {!!}
```

### The core pregroupoid

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pregroupoid-core-Precategory :
    is-pregroupoid-Precategory (core-precategory-Precategory C)
  is-pregroupoid-core-Precategory = {!!}

  core-pregroupoid-Precategory : Pregroupoid l1 l2
  core-pregroupoid-Precategory = {!!}
```

## Properties

### Computing isomorphisms in the core

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {x y : obj-Precategory C}
  where

  compute-iso-core-Precategory :
    iso-Precategory C x y ≃ iso-Precategory (core-precategory-Precategory C) x y
  compute-iso-core-Precategory = {!!}

  inv-compute-iso-core-Precategory :
    iso-Precategory (core-precategory-Precategory C) x y ≃ iso-Precategory C x y
  inv-compute-iso-core-Precategory = {!!}
```

### The core is replete

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-replete-core-Precategory :
    is-replete-Subprecategory C (core-subprecategory-Precategory C)
  is-replete-core-Precategory = {!!}
```

### The base precategory is a category if and only if the core is

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-torsorial-iso-core-is-category-Precategory :
    is-category-Precategory C →
    (x : obj-Precategory C) →
    is-torsorial (iso-Precategory (core-precategory-Precategory C) x)
  is-torsorial-iso-core-is-category-Precategory = {!!}

  is-category-core-is-category-Precategory :
    is-category-Precategory C →
    is-category-Precategory (core-precategory-Precategory C)
  is-category-core-is-category-Precategory = {!!}

  is-torsorial-iso-is-category-core-Precategory :
    is-category-Precategory (core-precategory-Precategory C) →
    (x : obj-Precategory C) →
    is-torsorial (iso-Precategory C x)
  is-torsorial-iso-is-category-core-Precategory = {!!}

  is-category-is-category-core-Precategory :
    is-category-Precategory (core-precategory-Precategory C) →
    is-category-Precategory C
  is-category-is-category-core-Precategory = {!!}
```

### The construction of the core is idempotent

```text
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-idempotent-core-Precategory :
    ( core-precategory-Precategory (core-precategory-Precategory C)) ＝
    ( core-precategory-Precategory C)
  is-idempotent-core-Precategory = {!!}
```

## See also

- [Cores of monoids](group-theory.cores-monoids.md)
- [Restrictions of functors to cores of precategories](category-theory.restrictions-functors-cores-precategories.md)

## External links

- [The core of a category](https://1lab.dev/Cat.Instances.Core.html) at 1lab
- [core groupoid](https://ncatlab.org/nlab/show/core+groupoid) at $n$Lab
