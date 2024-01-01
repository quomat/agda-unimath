# Discrete categories

```agda
module category-theory.discrete-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

### Discrete precategories

Any set induces a discrete category whose objects are elements of the set and
which contains no-nonidentity morphisms.

```agda
module _
  {l : Level} (X : Set l)
  where

  discrete-precategory-Set : Precategory l l
  pr1 discrete-precategory-Set = {!!}
```
