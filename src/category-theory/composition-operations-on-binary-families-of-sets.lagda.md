# Composition operations on binary families of sets

```agda
module category-theory.composition-operations-on-binary-families-of-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a type `A`, a **composition operation on a binary family of sets**
`hom : A → A → Set ` is a map

```text
  hom y z → hom x y → hom x z
```

for every triple of elements `x y z : A`.

For such operations, we can consider
[properties](foundation-core.propositions.md) such as **associativity** and
**unitality**.

## Definitions

### Composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  composition-operation-binary-family-Set = {!!}
```

### Associative composition operations in binary families of sets

We give a slightly non-standard definition of associativity, requiring an
associativity witness in each direction. This is of course redundant as `inv` is
a [fibered involution](foundation.fibered-involutions.md) on
[identity types](foundation-core.identity-types.md). However, by recording both
directions we maintain a definitional double inverse law which is practical in
defining the [opposite category](category-theory.opposite-categories.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-associative-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set → UU (l1 ⊔ l2)
  is-associative-composition-operation-binary-family-Set comp-hom = {!!}

  associative-composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  associative-composition-operation-binary-family-Set = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  (H : associative-composition-operation-binary-family-Set hom-set)
  where

  comp-hom-associative-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set
  comp-hom-associative-composition-operation-binary-family-Set = {!!}

  witness-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g) (f)) ＝
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h) (comp-hom-associative-composition-operation-binary-family-Set g f))
  witness-associative-composition-operation-binary-family-Set h g f = {!!}

  inv-witness-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h) (comp-hom-associative-composition-operation-binary-family-Set g f)) ＝
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g) (f))
  inv-witness-associative-composition-operation-binary-family-Set h g f = {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where

  is-associative-witness-associative-composition-operation-binary-family-Set :
    ( {x y z w : A}
      (h : type-Set (hom-set z w))
      (g : type-Set (hom-set y z))
      (f : type-Set (hom-set x y)) →
      comp-hom (comp-hom h g) f ＝ comp-hom h (comp-hom g f)) →
    is-associative-composition-operation-binary-family-Set hom-set comp-hom
  pr1
    ( is-associative-witness-associative-composition-operation-binary-family-Set
        H h g f) = {!!}

  is-associative-inv-witness-associative-composition-operation-binary-family-Set :
    ( {x y z w : A}
      (h : type-Set (hom-set z w))
      (g : type-Set (hom-set y z))
      (f : type-Set (hom-set x y)) →
      comp-hom h (comp-hom g f) ＝ comp-hom (comp-hom h g) f) →
    is-associative-composition-operation-binary-family-Set hom-set comp-hom
  pr1
    ( is-associative-inv-witness-associative-composition-operation-binary-family-Set
        H h g f) = {!!}
```

### Unital composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-unital-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set → UU (l1 ⊔ l2)
  is-unital-composition-operation-binary-family-Set comp-hom = {!!}
```

## Properties

### Being associative is a property of composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where
  is-prop-is-associative-composition-operation-binary-family-Set :
    is-prop
      ( is-associative-composition-operation-binary-family-Set hom-set comp-hom)
  is-prop-is-associative-composition-operation-binary-family-Set = {!!}

  is-associative-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  pr1 is-associative-prop-composition-operation-binary-family-Set = {!!}
```

### Being unital is a property of composition operations in binary families of sets

**Proof:** Suppose `e e' : (x : A) → hom-set x x` are both right and left units
with regard to composition. It is enough to show that `e ＝ e'` since the right
and left unit laws are propositions (because all hom-types are sets). By
function extensionality, it is enough to show that `e x ＝ e' x` for all
`x : A`. But by the unit laws we have the following chain of equalities:
`e x ＝ (e' x) ∘ (e x) ＝ e' x.`

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where

  abstract
    all-elements-equal-is-unital-composition-operation-binary-family-Set :
      all-elements-equal
        ( is-unital-composition-operation-binary-family-Set hom-set comp-hom)
    all-elements-equal-is-unital-composition-operation-binary-family-Set
      ( e , left-unit-law-e , right-unit-law-e)
      ( e' , left-unit-law-e' , right-unit-law-e') = {!!}

  abstract
    is-prop-is-unital-composition-operation-binary-family-Set :
      is-prop
        ( is-unital-composition-operation-binary-family-Set hom-set comp-hom)
    is-prop-is-unital-composition-operation-binary-family-Set = {!!}

  is-unital-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  pr1 is-unital-prop-composition-operation-binary-family-Set = {!!}
```

## See also

- [Set-magmoids](category-theory.set-magmoids.md) capture the structure of
  composition operations on binary families of sets.

- [Precategories](category-theory.precategories.md) are associative and unital
  composition operations on binary families of sets.
- [Nonunital precategories](category-theory.nonunital-precategories.md) are
  associative composition operations on binary families of sets.
