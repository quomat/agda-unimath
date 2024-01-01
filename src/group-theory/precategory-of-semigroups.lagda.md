# The precategory of semigroups

```agda
module group-theory.precategory-of-semigroups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

Semigroups and semigroup homomorphisms form a precategory.

## Definition

### The precategory of semigroups

```agda
instance
  Semigroup-Large-Precategory : Large-Precategory lsuc (_⊔_)
  obj-Large-Precategory Semigroup-Large-Precategory = {!!}
```
