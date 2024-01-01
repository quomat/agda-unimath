# Functors between precategories

```agda
module category-theory.functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoids
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F₁ id_x = {!!}
- `F₁ (g ∘ f) = {!!}

## Definition

### The predicate of being a functor on maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  preserves-comp-hom-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-prop-map-Precategory = {!!}

  preserves-comp-hom-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-map-Precategory = {!!}

  is-prop-preserves-comp-hom-map-Precategory :
    is-prop preserves-comp-hom-map-Precategory
  is-prop-preserves-comp-hom-map-Precategory = {!!}

  preserves-id-hom-map-Precategory : UU (l1 ⊔ l4)
  preserves-id-hom-map-Precategory = {!!}

  is-prop-preserves-id-hom-map-Precategory :
    is-prop preserves-id-hom-map-Precategory
  is-prop-preserves-id-hom-map-Precategory = {!!}

  preserves-id-hom-prop-map-Precategory : Prop (l1 ⊔ l4)
  pr1 preserves-id-hom-prop-map-Precategory = {!!}

  is-functor-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-functor-prop-map-Precategory = {!!}

  is-functor-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-functor-map-Precategory = {!!}

  is-prop-is-functor-map-Precategory :
    is-prop is-functor-map-Precategory
  is-prop-is-functor-map-Precategory = {!!}

  preserves-comp-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-comp-hom-map-Precategory
  preserves-comp-is-functor-map-Precategory = {!!}

  preserves-id-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-id-hom-map-Precategory
  preserves-id-is-functor-map-Precategory = {!!}
```

### functors between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Precategory = {!!}

  obj-functor-Precategory :
    functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-functor-Precategory = {!!}

  hom-functor-Precategory :
    (F : functor-Precategory) →
    {x y : obj-Precategory C} →
    (f : hom-Precategory C x y) →
    hom-Precategory D
      ( obj-functor-Precategory F x)
      ( obj-functor-Precategory F y)
  hom-functor-Precategory = {!!}

  map-functor-Precategory : functor-Precategory → map-Precategory C D
  pr1 (map-functor-Precategory F) = {!!}

  is-functor-functor-Precategory :
    (F : functor-Precategory) →
    is-functor-map-Precategory C D (map-functor-Precategory F)
  is-functor-functor-Precategory = {!!}

  preserves-comp-functor-Precategory :
    (F : functor-Precategory) {x y z : obj-Precategory C}
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    ( hom-functor-Precategory F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( hom-functor-Precategory F g)
      ( hom-functor-Precategory F f))
  preserves-comp-functor-Precategory = {!!}

  preserves-id-functor-Precategory :
    (F : functor-Precategory) (x : obj-Precategory C) →
    ( hom-functor-Precategory F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {obj-functor-Precategory F x})
  preserves-id-functor-Precategory = {!!}
```

## Examples

### The identity functor

There is an identity functor on any precategory.

```agda
id-functor-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → functor-Precategory C C
id-functor-Precategory = {!!}
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Precategory l1 l2) (B : Precategory l3 l4) (C : Precategory l5 l6)
  (G : functor-Precategory B C) (F : functor-Precategory A B)
  where

  obj-comp-functor-Precategory : obj-Precategory A → obj-Precategory C
  obj-comp-functor-Precategory = {!!}

  hom-comp-functor-Precategory :
    {x y : obj-Precategory A} →
    hom-Precategory A x y →
    hom-Precategory C
      ( obj-comp-functor-Precategory x)
      ( obj-comp-functor-Precategory y)
  hom-comp-functor-Precategory = {!!}

  map-comp-functor-Precategory : map-Precategory A C
  pr1 map-comp-functor-Precategory = {!!}

  preserves-comp-comp-functor-Precategory :
    preserves-comp-hom-map-Precategory A C map-comp-functor-Precategory
  preserves-comp-comp-functor-Precategory = {!!}

  preserves-id-comp-functor-Precategory :
    preserves-id-hom-map-Precategory A C map-comp-functor-Precategory
  preserves-id-comp-functor-Precategory = {!!}

  comp-functor-Precategory : functor-Precategory A C
  pr1 comp-functor-Precategory = {!!}
```

## Properties

### Extensionality of functors between precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  equiv-eq-map-eq-functor-Precategory :
    (F ＝ G) ≃ (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  equiv-eq-map-eq-functor-Precategory = {!!}

  eq-map-eq-functor-Precategory :
    (F ＝ G) → (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  eq-map-eq-functor-Precategory = {!!}

  eq-eq-map-functor-Precategory :
    (map-functor-Precategory C D F ＝ map-functor-Precategory C D G) → (F ＝ G)
  eq-eq-map-functor-Precategory = {!!}

  is-section-eq-eq-map-functor-Precategory :
    eq-map-eq-functor-Precategory ∘ eq-eq-map-functor-Precategory ~ id
  is-section-eq-eq-map-functor-Precategory = {!!}

  is-retraction-eq-eq-map-functor-Precategory :
    eq-eq-map-functor-Precategory ∘ eq-map-eq-functor-Precategory ~ id
  is-retraction-eq-eq-map-functor-Precategory = {!!}
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  htpy-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-functor-Precategory = {!!}

  equiv-htpy-eq-functor-Precategory : (F ＝ G) ≃ htpy-functor-Precategory
  equiv-htpy-eq-functor-Precategory = {!!}

  htpy-eq-functor-Precategory : F ＝ G → htpy-functor-Precategory
  htpy-eq-functor-Precategory = {!!}

  eq-htpy-functor-Precategory : htpy-functor-Precategory → F ＝ G
  eq-htpy-functor-Precategory = {!!}

  is-section-eq-htpy-functor-Precategory :
    htpy-eq-functor-Precategory ∘ eq-htpy-functor-Precategory ~ id
  is-section-eq-htpy-functor-Precategory = {!!}

  is-retraction-eq-htpy-functor-Precategory :
    eq-htpy-functor-Precategory ∘ htpy-eq-functor-Precategory ~ id
  is-retraction-eq-htpy-functor-Precategory = {!!}
```

### Functors preserve isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  {x y : obj-Precategory C}
  where

  hom-inv-preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    is-iso-Precategory C f →
    hom-Precategory D
      ( obj-functor-Precategory C D F y)
      ( obj-functor-Precategory C D F x)
  hom-inv-preserves-is-iso-functor-Precategory = {!!}

  is-right-inv-preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    (is-iso-f : is-iso-Precategory C f) →
    comp-hom-Precategory D
      ( hom-functor-Precategory C D F f)
      ( hom-functor-Precategory C D F (hom-inv-is-iso-Precategory C is-iso-f)) ＝
    id-hom-Precategory D
  is-right-inv-preserves-is-iso-functor-Precategory = {!!}

  is-left-inv-preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    (is-iso-f : is-iso-Precategory C f) →
    comp-hom-Precategory D
      ( hom-functor-Precategory C D F (hom-inv-is-iso-Precategory C is-iso-f))
      ( hom-functor-Precategory C D F f) ＝
    id-hom-Precategory D
  is-left-inv-preserves-is-iso-functor-Precategory = {!!}

  preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    is-iso-Precategory C f →
    is-iso-Precategory D (hom-functor-Precategory C D F f)
  preserves-is-iso-functor-Precategory = {!!}

  preserves-iso-functor-Precategory :
    iso-Precategory C x y →
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y)
  preserves-iso-functor-Precategory = {!!}
```

### Categorical laws for functor composition

#### Unit laws for functor composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  left-unit-law-comp-functor-Precategory :
    comp-functor-Precategory C D D (id-functor-Precategory D) F ＝ F
  left-unit-law-comp-functor-Precategory = {!!}

  right-unit-law-comp-functor-Precategory :
    comp-functor-Precategory C C D F (id-functor-Precategory C) ＝ F
  right-unit-law-comp-functor-Precategory = {!!}
```

#### Associativity of functor composition

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Precategory l1 l1')
  (B : Precategory l2 l2')
  (C : Precategory l3 l3')
  (D : Precategory l4 l4')
  (F : functor-Precategory A B)
  (G : functor-Precategory B C)
  (H : functor-Precategory C D)
  where

  associative-comp-functor-Precategory :
    comp-functor-Precategory A B D (comp-functor-Precategory B C D H G) F ＝
    comp-functor-Precategory A C D H (comp-functor-Precategory A B C G F)
  associative-comp-functor-Precategory = {!!}
```

#### Mac Lane pentagon for functor composition

```text
    (I(GH))F ---- I((GH)F)
          /        \
         /          \
  ((IH)G)F          I(H(GF))
          \        /
            \    /
           (IH)(GF)
```

The proof remains to be formalized.

```text
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Precategory l1 l1')
  (B : Precategory l2 l2')
  (C : Precategory l3 l3')
  (D : Precategory l4 l4')
  (E : Precategory l4 l4')
  (F : functor-Precategory A B)
  (G : functor-Precategory B C)
  (H : functor-Precategory C D)
  (I : functor-Precategory D E)
  where

  mac-lane-pentagon-comp-functor-Precategory :
    coherence-pentagon-identifications
      { x = {!!}
```

## See also

- [The precategory of functors and natural transformations between precategories](category-theory.precategory-of-functors.md)

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))
2. Benedikt Ahrens and Krzysztof Kapulkin and Michael Shulman, _Univalent
   Categories and the Rezk completion_ (2015)
   ([arXiv:1303.0584](https://arxiv.org/abs/1303.0584),
   [DOI:10.1017/S0960129514000486](https://doi.org/10.1017/S0960129514000486))

## External links

- [Functors](https://1lab.dev/Cat.Base.html#functors) at 1lab
