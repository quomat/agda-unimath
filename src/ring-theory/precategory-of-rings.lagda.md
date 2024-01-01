# The precategory of rings

```agda
module ring-theory.precategory-of-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

The **(large) precategory of rings** consists of [rings](ring-theory.rings.md)
and [ring homomorphisms](ring-theory.homomorphisms-rings.md).

## Definitions

### The large precategory of rings

```agda
Ring-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Ring-Large-Precategory = {!!}
hom-set-Large-Precategory
  Ring-Large-Precategory = {!!}
comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} {T} = {!!}
id-hom-Large-Precategory
  Ring-Large-Precategory {X = R} = {!!}
associative-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} {T} {U} = {!!}
inv-associative-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} {T} {U} = {!!}
left-unit-law-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} = {!!}
right-unit-law-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} = {!!}
```

### The precategory or rings of universe level `l`

```agda
Ring-Precategory : (l : Level) → Precategory (lsuc l) l
Ring-Precategory = {!!}
```
