# The precategory of concrete groups

```agda
module group-theory.precategory-of-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
```

</details>

## Definitions

### The large precategory of concrete groups

```agda
Concrete-Group-Large-Precategory : Large-Precategory lsuc (_⊔_)
Concrete-Group-Large-Precategory = {!!}
hom-set-Large-Precategory
  Concrete-Group-Large-Precategory = {!!}
comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} {Z = K} = {!!}
id-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} = {!!}
associative-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} {Z = K} {W = L} h g f = {!!}
inv-associative-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} {Z = K} {W = L} h g f = {!!}
left-unit-law-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} f = {!!}
right-unit-law-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} f = {!!}
```
