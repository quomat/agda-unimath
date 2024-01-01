# Nonunital precategories

```agda
module category-theory.nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A **nonunital precategory** is a [precategory](category-theory.precategories.md)
that may not have identity maps. In other words, it is an associative
[composition operation on binary families of sets](category-theory.composition-operations-on-binary-families-of-sets.md).
Such an object may also be called a **semiprecategory**.

## Definition

### The type of nonunital precategories

```agda
Nonunital-Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Nonunital-Precategory = {!!}

module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  obj-Nonunital-Precategory : UU l1
  obj-Nonunital-Precategory = {!!}

  hom-set-Nonunital-Precategory : (x y : obj-Nonunital-Precategory) → Set l2
  hom-set-Nonunital-Precategory = {!!}

  hom-Nonunital-Precategory : (x y : obj-Nonunital-Precategory) → UU l2
  hom-Nonunital-Precategory = {!!}

  is-set-hom-Nonunital-Precategory :
    (x y : obj-Nonunital-Precategory) → is-set (hom-Nonunital-Precategory x y)
  is-set-hom-Nonunital-Precategory = {!!}

  associative-composition-operation-Nonunital-Precategory :
    associative-composition-operation-binary-family-Set
      hom-set-Nonunital-Precategory
  associative-composition-operation-Nonunital-Precategory = {!!}

  comp-hom-Nonunital-Precategory :
    {x y z : obj-Nonunital-Precategory} →
    hom-Nonunital-Precategory y z →
    hom-Nonunital-Precategory x y →
    hom-Nonunital-Precategory x z
  comp-hom-Nonunital-Precategory = {!!}

  comp-hom-Nonunital-Precategory' :
    {x y z : obj-Nonunital-Precategory} →
    hom-Nonunital-Precategory x y →
    hom-Nonunital-Precategory y z →
    hom-Nonunital-Precategory x z
  comp-hom-Nonunital-Precategory' = {!!}

  associative-comp-hom-Nonunital-Precategory :
    {x y z w : obj-Nonunital-Precategory}
    (h : hom-Nonunital-Precategory z w)
    (g : hom-Nonunital-Precategory y z)
    (f : hom-Nonunital-Precategory x y) →
    comp-hom-Nonunital-Precategory (comp-hom-Nonunital-Precategory h g) f ＝
    comp-hom-Nonunital-Precategory h (comp-hom-Nonunital-Precategory g f)
  associative-comp-hom-Nonunital-Precategory = {!!}

  inv-associative-comp-hom-Nonunital-Precategory :
    {x y z w : obj-Nonunital-Precategory}
    (h : hom-Nonunital-Precategory z w)
    (g : hom-Nonunital-Precategory y z)
    (f : hom-Nonunital-Precategory x y) →
    comp-hom-Nonunital-Precategory h (comp-hom-Nonunital-Precategory g f) ＝
    comp-hom-Nonunital-Precategory (comp-hom-Nonunital-Precategory h g) f
  inv-associative-comp-hom-Nonunital-Precategory = {!!}
```

### The underlying set-magmoid of a nonunital precategory

```agda
module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  set-magmoid-Nonunital-Precategory : Set-Magmoid l1 l2
  set-magmoid-Nonunital-Precategory = {!!}
```

### The total hom-type of a nonunital precategory

```agda
total-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2) → UU (l1 ⊔ l2)
total-hom-Nonunital-Precategory = {!!}

obj-total-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2) →
  total-hom-Nonunital-Precategory C →
  obj-Nonunital-Precategory C × obj-Nonunital-Precategory C
obj-total-hom-Nonunital-Precategory = {!!}
```

### Pre- and postcomposition by a morphism

```agda
module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory C}
  (f : hom-Nonunital-Precategory C x y)
  (z : obj-Nonunital-Precategory C)
  where

  precomp-hom-Nonunital-Precategory :
    hom-Nonunital-Precategory C y z → hom-Nonunital-Precategory C x z
  precomp-hom-Nonunital-Precategory = {!!}

  postcomp-hom-Nonunital-Precategory :
    hom-Nonunital-Precategory C z x → hom-Nonunital-Precategory C z y
  postcomp-hom-Nonunital-Precategory = {!!}
```

### The predicate on nonunital precategories of being unital

**Proof:** To show that unitality is a proposition, suppose
`e e' : (x : A) → hom-set x x` are both right and left units with regard to
composition. It is enough to show that `e ＝ e'` since the right and left unit
laws are propositions (because all hom-types are sets). By function
extensionality, it is enough to show that `e x ＝ e' x` for all `x : A`. But by
the unit laws we have the following chain of equalities:
`e x ＝ (e' x) ∘ (e x) ＝ e' x.`

```agda
module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  is-unital-Nonunital-Precategory : UU (l1 ⊔ l2)
  is-unital-Nonunital-Precategory = {!!}

  is-prop-is-unital-Nonunital-Precategory :
    is-prop
      ( is-unital-composition-operation-binary-family-Set
        ( hom-set-Nonunital-Precategory C)
        ( comp-hom-Nonunital-Precategory C))
  is-prop-is-unital-Nonunital-Precategory = {!!}

  is-unital-prop-Nonunital-Precategory : Prop (l1 ⊔ l2)
  is-unital-prop-Nonunital-Precategory = {!!}
```

## Properties

### If the objects of a nonunital precategory are `k`-truncated for non-negative `k`, the total hom-type is `k`-truncated

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (C : Nonunital-Precategory l1 l2)
  where

  is-trunc-total-hom-is-trunc-obj-Nonunital-Precategory :
    is-trunc (succ-𝕋 (succ-𝕋 k)) (obj-Nonunital-Precategory C) →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (total-hom-Nonunital-Precategory C)
  is-trunc-total-hom-is-trunc-obj-Nonunital-Precategory = {!!}

  total-hom-truncated-type-is-trunc-obj-Nonunital-Precategory :
    is-trunc (succ-𝕋 (succ-𝕋 k)) (obj-Nonunital-Precategory C) →
    Truncated-Type (l1 ⊔ l2) (succ-𝕋 (succ-𝕋 k))
  total-hom-truncated-type-is-trunc-obj-Nonunital-Precategory = {!!}
```

## Comments

As discussed in [Semicategories](https://ncatlab.org/nlab/show/semicategory) at
$n$Lab, it seems that a nonunital precategory should be the underlying nonunital
precategory of a [category](category-theory.categories.md) if and only if the
projection map

```text
  pr1 : (Σ (a : A) Σ (f : hom a a) (is-neutral f)) → A
```

is an [equivalence](foundation-core.equivalences.md).

We can also define one notion of "isomorphism" as those morphisms that induce
equivalences of hom-[sets](foundation-core.sets.md) by pre- and postcomposition.

## External links

- [Semicategories](https://ncatlab.org/nlab/show/semicategory) at $n$Lab
- [Semigroupoid](https://en.wikipedia.org/wiki/Semigroupoid) at Wikipedia
- [semigroupoid](https://www.wikidata.org/wiki/Q4164581) at Wikidata
