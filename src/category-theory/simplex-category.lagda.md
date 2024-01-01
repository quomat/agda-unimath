# The simplex category

```agda
module category-theory.simplex-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.precategories

open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

**The simplex category** is the category consisting of inhabited finite total
orders and
[order-preserving maps](order-theory.order-preserving-maps-posets.md). However,
we define it as the category whose objects are
[natural numbers](elementary-number-theory.natural-numbers.md) and whose
hom-[sets](foundation-core.sets.md) `hom n m` are order-preserving maps between
the [standard finite types](univalent-combinatorics.standard-finite-types.md)
`Fin (succ-ℕ n)` to `Fin (succ-ℕ m)` [equipped](foundation.structure.md) with
the
[standard ordering](elementary-number-theory.inequality-standard-finite-types.md),
and then show that it is
[equivalent](category-theory.equivalences-of-precategories.md) to the former.

## Definition

### The simplex precategory

```agda
obj-simplex-Category : UU lzero
obj-simplex-Category = {!!}

hom-set-simplex-Category :
  obj-simplex-Category → obj-simplex-Category → Set lzero
hom-set-simplex-Category = {!!}

hom-simplex-Category :
  obj-simplex-Category → obj-simplex-Category → UU lzero
hom-simplex-Category = {!!}

comp-hom-simplex-Category :
  {n m r : obj-simplex-Category} →
  hom-simplex-Category m r → hom-simplex-Category n m → hom-simplex-Category n r
comp-hom-simplex-Category = {!!}

associative-comp-hom-simplex-Category :
  {n m r s : obj-simplex-Category}
  (h : hom-simplex-Category r s)
  (g : hom-simplex-Category m r)
  (f : hom-simplex-Category n m) →
  comp-hom-simplex-Category {n} {m} {s}
    ( comp-hom-simplex-Category {m} {r} {s} h g)
    ( f) ＝
  comp-hom-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-simplex-Category {n} {m} {r} g f)
associative-comp-hom-simplex-Category = {!!}

inv-associative-comp-hom-simplex-Category :
  {n m r s : obj-simplex-Category}
  (h : hom-simplex-Category r s)
  (g : hom-simplex-Category m r)
  (f : hom-simplex-Category n m) →
  comp-hom-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-simplex-Category {n} {m} {r} g f) ＝
  comp-hom-simplex-Category {n} {m} {s}
    ( comp-hom-simplex-Category {m} {r} {s} h g)
    ( f)
inv-associative-comp-hom-simplex-Category = {!!}

associative-composition-operation-simplex-Category :
  associative-composition-operation-binary-family-Set hom-set-simplex-Category
associative-composition-operation-simplex-Category = {!!}

id-hom-simplex-Category : (n : obj-simplex-Category) → hom-simplex-Category n n
id-hom-simplex-Category n = {!!}

left-unit-law-comp-hom-simplex-Category :
  {n m : obj-simplex-Category} (f : hom-simplex-Category n m) →
  comp-hom-simplex-Category {n} {m} {m} (id-hom-simplex-Category m) f ＝ f
left-unit-law-comp-hom-simplex-Category = {!!}

right-unit-law-comp-hom-simplex-Category :
  {n m : obj-simplex-Category} (f : hom-simplex-Category n m) →
  comp-hom-simplex-Category {n} {n} {m} f (id-hom-simplex-Category n) ＝ f
right-unit-law-comp-hom-simplex-Category = {!!}

is-unital-composition-operation-simplex-Category :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-simplex-Category)
    ( comp-hom-simplex-Category)
is-unital-composition-operation-simplex-Category = {!!}
pr1 (pr2 is-unital-composition-operation-simplex-Category) {n} {m} = {!!}
pr2 (pr2 is-unital-composition-operation-simplex-Category) {n} {m} = {!!}

simplex-Precategory : Precategory lzero lzero
pr1 simplex-Precategory = {!!}
pr1 (pr2 simplex-Precategory) = {!!}
pr1 (pr2 (pr2 simplex-Precategory)) = {!!}
pr2 (pr2 (pr2 simplex-Precategory)) = {!!}
```

### The simplex category

It remains to be formalized that the simplex category is univalent.

## Properties

### The simplex category is equivalent to the category of inhabited finite total orders

This remains to be formalized.

### The simplex category has a face map and degeneracy unique factorization system

This remains to be formalized.

### The simplex category has a degeneracy and face map unique factorization system

This remains to be formalized.

### There is a unique non-trivial involution on the simplex category

This remains to be formalized.
