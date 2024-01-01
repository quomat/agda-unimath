# The precategory of group actions

```agda
module group-theory.precategory-of-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
```

</details>

## Idea

The [large precategory](category-theory.large-precategories.md) of
[group actions](group-theory.group-actions.md) consists of group actions and
[morphisms of group actions](group-theory.homomorphisms-group-actions.md)
between them.

## Definitions

### The large precategory of `G`-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  action-Group-Large-Precategory :
    Large-Precategory (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  action-Group-Large-Precategory = {!!}
```

### The small precategory of `G`-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  action-Group-Precategory :
    (l2 : Level) → Precategory (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  action-Group-Precategory = {!!}
```
