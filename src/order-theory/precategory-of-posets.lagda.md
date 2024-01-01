# The precategory of posets

```agda
module order-theory.precategory-of-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

The **(large) precategory of posets** consists of
[posets](order-theory.posets.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md).

## Definitions

### The large precategory of posets

```agda
parametric-Poset-Large-Precategory :
  (α β : Level → Level) →
  Large-Precategory
    ( λ l → lsuc (α l) ⊔ lsuc (β l))
    ( λ l1 l2 → α l1 ⊔ β l1 ⊔ α l2 ⊔ β l2)
parametric-Poset-Large-Precategory α β = {!!}

Poset-Large-Precategory : Large-Precategory lsuc (_⊔_)
Poset-Large-Precategory = {!!}
```

### The precategory or posets of universe level `l`

```agda
Poset-Precategory : (l : Level) → Precategory (lsuc l) l
Poset-Precategory = {!!}
```
