# The precategory of finite species

```agda
module species.precategory-of-finite-species where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import species.morphisms-finite-species
open import species.species-of-finite-types
```

</details>

## Idea

The **precategory of finite species** consists of finite species and
homomorphisms of finite species.

## Definition

```agda
species-𝔽-Large-Precategory :
  (l1 : Level) →
  Large-Precategory (λ l → lsuc l1 ⊔ lsuc l) (λ l2 l3 → lsuc l1 ⊔ l2 ⊔ l3)
species-𝔽-Large-Precategory = {!!}
```
