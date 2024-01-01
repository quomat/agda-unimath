# The precategory of semirings

```agda
module ring-theory.precategory-of-semirings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.homomorphisms-semirings
open import ring-theory.semirings
```

</details>

## Idea

The **precategory of semirings** consists of semirings and homomorphisms of
semirings.

## Definitions

### The large precategory of semirings

```agda
Semiring-Large-Precategory : Large-Precategory lsuc _⊔_
Semiring-Large-Precategory = {!!}
hom-set-Large-Precategory
  Semiring-Large-Precategory = {!!}
comp-hom-Large-Precategory
  Semiring-Large-Precategory {X = R} {S} {T} = {!!}
id-hom-Large-Precategory
  Semiring-Large-Precategory {X = R} = {!!}
associative-comp-hom-Large-Precategory
  Semiring-Large-Precategory {X = R} {S} {T} {U} = {!!}
inv-associative-comp-hom-Large-Precategory
  Semiring-Large-Precategory {X = R} {S} {T} {U} = {!!}
left-unit-law-comp-hom-Large-Precategory
  Semiring-Large-Precategory {X = R} {S} = {!!}
right-unit-law-comp-hom-Large-Precategory
  Semiring-Large-Precategory {X = R} {S} = {!!}
```

### The precategory of semirings of universe level `l`

```agda
Semiring-Precategory : (l : Level) → Precategory (lsuc l) l
Semiring-Precategory = {!!}
```
