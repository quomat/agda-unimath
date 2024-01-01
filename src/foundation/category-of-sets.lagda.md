# The category of sets

```agda
module foundation.category-of-sets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.isomorphisms-of-sets
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
```

</details>

## Idea

The **category of [sets](foundation-core.sets.md)** consists of sets and
functions. There is a [category](category-theory.categories.md) of sets for each
universe level, and there is a
[large category](category-theory.large-categories.md) of sets.

## Definitions

### The large precategory of sets

```agda
Set-Large-Precategory : Large-Precategory lsuc (_⊔_)
Set-Large-Precategory = {!!}
hom-set-Large-Precategory Set-Large-Precategory = {!!}
comp-hom-Large-Precategory Set-Large-Precategory g f = {!!}
id-hom-Large-Precategory Set-Large-Precategory = {!!}
associative-comp-hom-Large-Precategory Set-Large-Precategory h g f = {!!}
inv-associative-comp-hom-Large-Precategory Set-Large-Precategory h g f = {!!}
left-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = {!!}
right-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = {!!}
```

### The large category of sets

```agda
id-iso-Set :
  {l : Level} {X : obj-Large-Precategory Set-Large-Precategory l} →
  iso-Large-Precategory Set-Large-Precategory X X
id-iso-Set = {!!}

iso-eq-Set :
  {l : Level} (X Y : obj-Large-Precategory Set-Large-Precategory l) →
  X ＝ Y → iso-Large-Precategory Set-Large-Precategory X Y
iso-eq-Set = {!!}

is-large-category-Set-Large-Precategory :
  is-large-category-Large-Precategory Set-Large-Precategory
is-large-category-Set-Large-Precategory = {!!}

Set-Large-Category : Large-Category lsuc (_⊔_)
Set-Large-Category = {!!}
is-large-category-Large-Category Set-Large-Category = {!!}
```

### The precategory of small sets

```agda
Set-Precategory : (l : Level) → Precategory (lsuc l) l
Set-Precategory = {!!}
```

### The category of small sets

The precategory of sets and functions in a given universe is a category.

```agda
Set-Category : (l : Level) → Category (lsuc l) l
Set-Category = {!!}

is-category-Set-Precategory :
  (l : Level) → is-category-Precategory (Set-Precategory l)
is-category-Set-Precategory = {!!}
```

## Comments

Since sets are equivalent to their set-truncations, the category of sets forms a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
homotopy precategory of types.

## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

## External links

- [Set](https://ncatlab.org/nlab/show/Set) at $n$Lab
- [Category of sets](https://en.wikipedia.org/wiki/Category_of_sets) at
  Wikipedia
