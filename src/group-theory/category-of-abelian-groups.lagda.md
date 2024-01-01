# The category of abelian groups

```agda
module group-theory.category-of-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.full-large-subcategories
open import category-theory.functors-large-categories
open import category-theory.functors-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.category-of-groups
```

</details>

## Idea

The **category of abelian groups** is the
[full large subcategory](category-theory.full-large-subcategories.md) of the
[category of groups](group-theory.category-of-groups.md) consisting of
[groups](group-theory.groups.md) of which the group operation is
[commutative](group-theory.abelian-groups.md).

## Definitions

### The large category of abelian groups

```agda
Ab-Large-Category : Large-Category lsuc _⊔_
Ab-Large-Category = {!!}
```

### The large precategory of abelian groups

```agda
Ab-Large-Precategory : Large-Precategory lsuc _⊔_
Ab-Large-Precategory = {!!}
```

### The category of abelian groups of a given universe level

```agda
Ab-Category : (l : Level) → Category (lsuc l) l
Ab-Category = {!!}
```

### The precategory of abelian groups of a given universe level

```agda
Ab-Precategory : (l : Level) → Precategory (lsuc l) l
Ab-Precategory = {!!}
```

### The forgetful functor from abelian groups to groups

```agda
forgetful-functor-Ab :
  functor-Large-Category (λ l → l) Ab-Large-Category Group-Large-Category
forgetful-functor-Ab = {!!}
```
