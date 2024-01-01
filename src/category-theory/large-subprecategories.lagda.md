# Large subprecategories

```agda
module category-theory.large-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **large subprecategory** of a
[large precategory](category-theory.large-precategories.md) `C` consists of a
family of subtypes `P₀`

```text
  P₀ : (l : Level) → subtype _ (obj C l)
```

of the objects of `C` indexed by universe levels, and a family of subtypes `P₁`

```text
  P₁ : {l1 l2 : Level} (X : obj C l1) (Y : obj C l2) →
       P₀ X → P₀ Y → subtype _ (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition.

## Definition

### Large subprecategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (γ : Level → Level) (δ : Level → Level → Level)
  (C : Large-Precategory α β)
  where

  record
    Large-Subprecategory : UUω
    where
    field
      subtype-obj-Large-Subprecategory :
        (l : Level) → subtype (γ l) (obj-Large-Precategory C l)
      subtype-obj-Large-Subprecategory = {!!}
```
