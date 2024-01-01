# The precategory of monoids

```agda
module group-theory.precategory-of-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
```

</details>

## Idea

The **precategory of monoids** consists of monoids and homomorphisms of monoids.

## Definitions

### The large precategory of monoids

```agda
Monoid-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Monoid-Large-Precategory = {!!}
hom-set-Large-Precategory
  Monoid-Large-Precategory = {!!}
comp-hom-Large-Precategory
  Monoid-Large-Precategory {X = K} {L} {M} = {!!}
id-hom-Large-Precategory
  Monoid-Large-Precategory {X = M} = {!!}
associative-comp-hom-Large-Precategory
  Monoid-Large-Precategory {X = K} {L} {M} {N} = {!!}
inv-associative-comp-hom-Large-Precategory
  Monoid-Large-Precategory {X = K} {L} {M} {N} = {!!}
left-unit-law-comp-hom-Large-Precategory
  Monoid-Large-Precategory {X = M} {N} = {!!}
right-unit-law-comp-hom-Large-Precategory
  Monoid-Large-Precategory {X = M} {N} = {!!}
```

### The precategory of small monoids

```agda
Monoid-Precategory : (l : Level) → Precategory (lsuc l) l
Monoid-Precategory = {!!}
```
