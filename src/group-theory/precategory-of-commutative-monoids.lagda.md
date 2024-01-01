# The precategory of commutative monoids

```agda
module group-theory.precategory-of-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
```

</details>

## Idea

The **precategory of commutative monoids** consists of commutative monoids and
homomorphisms of monoids.

## Definitions

### The large precategory of commutative monoids

```agda
Commutative-Monoid-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Commutative-Monoid-Large-Precategory = {!!}
hom-set-Large-Precategory
  Commutative-Monoid-Large-Precategory = {!!}
comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = K} {L} {M} = {!!}
id-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = M} = {!!}
associative-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = K} {L} {M} {N} = {!!}
inv-associative-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = K} {L} {M} {N} = {!!}
left-unit-law-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = M} {N} = {!!}
right-unit-law-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = M} {N} = {!!}
```
