# The augmented simplex category

```agda
module category-theory.augmented-simplex-category where
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

**The augmented simplex category** is the category consisting of
[finite total orders](order-theory.finite-total-orders.md) and
[order-preserving maps](order-theory.order-preserving-maps-posets.md). However,
we define it as the category whose objects are
[natural numbers](elementary-number-theory.natural-numbers.md) and whose
hom-[sets](foundation-core.sets.md) `hom n m` are order-preserving maps between
the [standard finite types](univalent-combinatorics.standard-finite-types.md)
`Fin n` to `Fin m` [equipped](foundation.structure.md) with the
[standard ordering](elementary-number-theory.inequality-standard-finite-types.md),
and then show that it is
[equivalent](category-theory.equivalences-of-precategories.md) to the former.

## Definition

### The augmented simplex precategory

```agda
obj-augmented-simplex-Category : UU lzero
obj-augmented-simplex-Category = {!!}

hom-set-augmented-simplex-Category :
  obj-augmented-simplex-Category → obj-augmented-simplex-Category → Set lzero
hom-set-augmented-simplex-Category = {!!}

hom-augmented-simplex-Category :
  obj-augmented-simplex-Category → obj-augmented-simplex-Category → UU lzero
hom-augmented-simplex-Category = {!!}

comp-hom-augmented-simplex-Category :
  {n m r : obj-augmented-simplex-Category} →
  hom-augmented-simplex-Category m r →
  hom-augmented-simplex-Category n m →
  hom-augmented-simplex-Category n r
comp-hom-augmented-simplex-Category = {!!}

associative-comp-hom-augmented-simplex-Category :
  {n m r s : obj-augmented-simplex-Category}
  (h : hom-augmented-simplex-Category r s)
  (g : hom-augmented-simplex-Category m r)
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {m} {s}
    ( comp-hom-augmented-simplex-Category {m} {r} {s} h g)
    ( f) ＝
  comp-hom-augmented-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-augmented-simplex-Category {n} {m} {r} g f)
associative-comp-hom-augmented-simplex-Category = {!!}

inv-associative-comp-hom-augmented-simplex-Category :
  {n m r s : obj-augmented-simplex-Category}
  (h : hom-augmented-simplex-Category r s)
  (g : hom-augmented-simplex-Category m r)
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-augmented-simplex-Category {n} {m} {r} g f) ＝
  comp-hom-augmented-simplex-Category {n} {m} {s}
    ( comp-hom-augmented-simplex-Category {m} {r} {s} h g)
    ( f)
inv-associative-comp-hom-augmented-simplex-Category = {!!}

associative-composition-operation-augmented-simplex-Category :
  associative-composition-operation-binary-family-Set
    hom-set-augmented-simplex-Category
associative-composition-operation-augmented-simplex-Category = {!!}
pr1
  ( pr2
      associative-composition-operation-augmented-simplex-Category
        { n} {m} {r} {s} h g f) = {!!}
pr2
  ( pr2
      associative-composition-operation-augmented-simplex-Category
        { n} {m} {r} {s} h g f) = {!!}

id-hom-augmented-simplex-Category :
  (n : obj-augmented-simplex-Category) → hom-augmented-simplex-Category n n
id-hom-augmented-simplex-Category = {!!}

left-unit-law-comp-hom-augmented-simplex-Category :
  {n m : obj-augmented-simplex-Category}
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {m} {m}
    ( id-hom-augmented-simplex-Category m)
    ( f) ＝
  f
left-unit-law-comp-hom-augmented-simplex-Category = {!!}

right-unit-law-comp-hom-augmented-simplex-Category :
  {n m : obj-augmented-simplex-Category}
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {n} {m}
    ( f)
    ( id-hom-augmented-simplex-Category n) ＝
  f
right-unit-law-comp-hom-augmented-simplex-Category = {!!}

is-unital-composition-operation-augmented-simplex-Category :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-augmented-simplex-Category)
    ( λ {n} {m} {r} → comp-hom-augmented-simplex-Category {n} {m} {r})
is-unital-composition-operation-augmented-simplex-Category = {!!}
pr1 (pr2 is-unital-composition-operation-augmented-simplex-Category) {n} {m} = {!!}
pr2 (pr2 is-unital-composition-operation-augmented-simplex-Category) {n} {m} = {!!}

augmented-simplex-Precategory : Precategory lzero lzero
augmented-simplex-Precategory = {!!}
pr1 (pr2 augmented-simplex-Precategory) = {!!}
pr1 (pr2 (pr2 augmented-simplex-Precategory)) = {!!}
pr2 (pr2 (pr2 augmented-simplex-Precategory)) = {!!}
```

### The augmented simplex category

It remains to be formalized that the augmented simplex category is univalent.

## Properties

### The augmented simplex category is equivalent to the category of finite total orders

This remains to be formalized.
