# Isomorphisms in precategories

```agda
module category-theory.isomorphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An **isomorphism** in a [precategory](category-theory.precategories.md) `C` is a
morphism `f : x → y` in `C` for which there exists a morphism `g : y → x` such
that `f ∘ g ＝ id` and `g ∘ f ＝ id`.

## Definitions

### The predicate of being an isomorphism in a precategory

```agda
is-iso-Precategory :
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : hom-Precategory C x y) →
  UU l2
is-iso-Precategory = {!!}

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  where

  hom-inv-is-iso-Precategory :
    is-iso-Precategory C f → hom-Precategory C y x
  hom-inv-is-iso-Precategory = {!!}

  is-section-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) →
    comp-hom-Precategory C f (hom-inv-is-iso-Precategory H) ＝
    id-hom-Precategory C
  is-section-hom-inv-is-iso-Precategory = {!!}

  is-retraction-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) →
    comp-hom-Precategory C (hom-inv-is-iso-Precategory H) f ＝
    id-hom-Precategory C
  is-retraction-hom-inv-is-iso-Precategory = {!!}
```

### Isomorphisms in a precategory

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (x y : obj-Precategory C)
  where

  iso-Precategory : UU l2
  iso-Precategory = {!!}

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  hom-iso-Precategory : hom-Precategory C x y
  hom-iso-Precategory = {!!}

  is-iso-iso-Precategory :
    is-iso-Precategory C hom-iso-Precategory
  is-iso-iso-Precategory = {!!}

  hom-inv-iso-Precategory : hom-Precategory C y x
  hom-inv-iso-Precategory = {!!}

  is-section-hom-inv-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-iso-Precategory)
      ( hom-inv-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-iso-Precategory = {!!}

  is-retraction-hom-inv-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-iso-Precategory)
      ( hom-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-iso-Precategory = {!!}
```

## Examples

### The identity isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = {!!}

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x : obj-Precategory C}
  where

  is-iso-id-hom-Precategory :
    is-iso-Precategory C (id-hom-Precategory C {x})
  is-iso-id-hom-Precategory = {!!}

  id-iso-Precategory : iso-Precategory C x x
  pr1 id-iso-Precategory = {!!}
```

### Equalities induce isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because, by the J-rule, it is enough to construct an isomorphism given
`refl : x ＝ x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  iso-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → iso-Precategory C x y
  iso-eq-Precategory = {!!}

  compute-hom-iso-eq-Precategory :
    {x y : obj-Precategory C} →
    (p : x ＝ y) →
    hom-eq-Precategory C x y p ＝
    hom-iso-Precategory C (iso-eq-Precategory x y p)
  compute-hom-iso-eq-Precategory = {!!}
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = {!!}
[propositions](foundation-core.propositions.md) (since the hom-types are sets).
But we have the following chain of equalities:
`g = {!!}

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  all-elements-equal-is-iso-Precategory :
    (f : hom-Precategory C x y)
    (H K : is-iso-Precategory C f) → H ＝ K
  all-elements-equal-is-iso-Precategory = {!!}

  is-prop-is-iso-Precategory :
    (f : hom-Precategory C x y) →
    is-prop (is-iso-Precategory C f)
  is-prop-is-iso-Precategory = {!!}

  is-iso-prop-Precategory :
    (f : hom-Precategory C x y) → Prop l2
  is-iso-prop-Precategory = {!!}
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  eq-iso-eq-hom-Precategory :
    (f g : iso-Precategory C x y) →
    hom-iso-Precategory C f ＝ hom-iso-Precategory C g → f ＝ g
  eq-iso-eq-hom-Precategory = {!!}
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a
[subtype](foundation-core.subtypes.md) of the [foundation-core.sets.md)
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-set-iso-Precategory : is-set (iso-Precategory C x y)
  is-set-iso-Precategory = {!!}

  iso-set-Precategory : Set l2
  pr1 iso-set-Precategory = {!!}
```

### Isomorphisms are closed under composition

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  {g : hom-Precategory C y z}
  {f : hom-Precategory C x y}
  where

  hom-comp-is-iso-Precategory :
    is-iso-Precategory C g →
    is-iso-Precategory C f →
    hom-Precategory C z x
  hom-comp-is-iso-Precategory = {!!}

  is-section-comp-is-iso-Precategory :
    (q : is-iso-Precategory C g)
    (p : is-iso-Precategory C f) →
    comp-hom-Precategory C
      ( comp-hom-Precategory C g f)
      ( hom-comp-is-iso-Precategory q p) ＝
    id-hom-Precategory C
  is-section-comp-is-iso-Precategory = {!!}

  is-retraction-comp-is-iso-Precategory :
    (q : is-iso-Precategory C g)
    (p : is-iso-Precategory C f) →
    ( comp-hom-Precategory C
      ( hom-comp-is-iso-Precategory q p)
      ( comp-hom-Precategory C g f)) ＝
    ( id-hom-Precategory C)
  is-retraction-comp-is-iso-Precategory = {!!}

  is-iso-comp-is-iso-Precategory :
    is-iso-Precategory C g → is-iso-Precategory C f →
    is-iso-Precategory C (comp-hom-Precategory C g f)
  is-iso-comp-is-iso-Precategory = {!!}
```

### The composition operation on isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  (g : iso-Precategory C y z)
  (f : iso-Precategory C x y)
  where

  hom-comp-iso-Precategory :
    hom-Precategory C x z
  hom-comp-iso-Precategory = {!!}

  is-iso-comp-iso-Precategory :
    is-iso-Precategory C hom-comp-iso-Precategory
  is-iso-comp-iso-Precategory = {!!}

  comp-iso-Precategory : iso-Precategory C x z
  pr1 comp-iso-Precategory = {!!}

  hom-inv-comp-iso-Precategory : hom-Precategory C z x
  hom-inv-comp-iso-Precategory = {!!}

  is-section-inv-comp-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-comp-iso-Precategory)
      ( hom-inv-comp-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-inv-comp-iso-Precategory = {!!}

  is-retraction-inv-comp-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-comp-iso-Precategory)
      ( hom-comp-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-retraction-inv-comp-iso-Precategory = {!!}
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  where

  is-iso-inv-is-iso-Precategory :
    (p : is-iso-Precategory C f) →
    is-iso-Precategory C (hom-inv-iso-Precategory C (f , p))
  is-iso-inv-is-iso-Precategory = {!!}
```

### Inverses of isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  inv-iso-Precategory :
    iso-Precategory C x y → iso-Precategory C y x
  inv-iso-Precategory = {!!}

  is-iso-inv-iso-Precategory :
    (f : iso-Precategory C x y) →
    is-iso-Precategory C (hom-inv-iso-Precategory C f)
  is-iso-inv-iso-Precategory = {!!}
```

### Groupoid laws of isomorphisms in precategories

#### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  left-unit-law-comp-iso-Precategory :
    comp-iso-Precategory C (id-iso-Precategory C) f ＝ f
  left-unit-law-comp-iso-Precategory = {!!}

  right-unit-law-comp-iso-Precategory :
    comp-iso-Precategory C f (id-iso-Precategory C) ＝ f
  right-unit-law-comp-iso-Precategory = {!!}
```

#### Composition of isomorphisms is associative

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z w : obj-Precategory C}
  (h : iso-Precategory C z w)
  (g : iso-Precategory C y z)
  (f : iso-Precategory C x y)
  where

  associative-comp-iso-Precategory :
    ( comp-iso-Precategory C (comp-iso-Precategory C h g) f) ＝
    ( comp-iso-Precategory C h (comp-iso-Precategory C g f))
  associative-comp-iso-Precategory = {!!}
```

#### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  left-inverse-law-comp-iso-Precategory :
    ( comp-iso-Precategory C (inv-iso-Precategory C f) f) ＝
    ( id-iso-Precategory C)
  left-inverse-law-comp-iso-Precategory = {!!}

  right-inverse-law-comp-iso-Precategory :
    ( comp-iso-Precategory C f (inv-iso-Precategory C f)) ＝
    ( id-iso-Precategory C)
  right-inverse-law-comp-iso-Precategory = {!!}
```

### The inverse operation is a fibered involution on isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  is-fibered-involution-inv-iso-Precategory :
    {x y : obj-Precategory C} →
    inv-iso-Precategory C {y} {x} ∘ inv-iso-Precategory C {x} {y} ~ id
  is-fibered-involution-inv-iso-Precategory = {!!}

  is-equiv-inv-iso-Precategory :
    {x y : obj-Precategory C} → is-equiv (inv-iso-Precategory C {x} {y})
  is-equiv-inv-iso-Precategory = {!!}

  equiv-inv-iso-Precategory :
    {x y : obj-Precategory C} → iso-Precategory C x y ≃ iso-Precategory C y x
  equiv-inv-iso-Precategory = {!!}
```

### A morphism `f` is an isomorphism if and only if precomposition by `f` is an equivalence

**Proof:** If `f` is an isomorphism with inverse `f⁻¹`, then precomposing with
`f⁻¹` is an inverse of precomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that precomposing with `f` is an equivalence, for any object `z`. Then

```text
  - ∘ f : hom y x → hom x x
```

is an equivalence. In particular, there is a unique morphism `g : y → x` such
that `g ∘ f ＝ id`. Thus we have a retraction of `f`. To see that `g` is also a
section, note that the map

```text
  - ∘ f : hom y y → hom x y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `(f ∘ g) ∘ f ＝ id ∘ f`. To see this, we calculate

```text
  (f ∘ g) ∘ f ＝ f ∘ (g ∘ f) ＝ f ∘ id ＝ f ＝ id ∘ f.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (H : (z : obj-Precategory C) → is-equiv (precomp-hom-Precategory C f z))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Precategory : hom-Precategory C y x
  hom-inv-is-iso-is-equiv-precomp-hom-Precategory = {!!}

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-is-iso-is-equiv-precomp-hom-Precategory)
      ( f)) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory = {!!}

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( f)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategory = {!!}

  is-iso-is-equiv-precomp-hom-Precategory : is-iso-Precategory C f
  pr1 is-iso-is-equiv-precomp-hom-Precategory = {!!}

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (is-iso-f : is-iso-Precategory C f)
  (z : obj-Precategory C)
  where

  map-inv-precomp-hom-is-iso-Precategory :
    hom-Precategory C x z → hom-Precategory C y z
  map-inv-precomp-hom-is-iso-Precategory = {!!}

  is-section-map-inv-precomp-hom-is-iso-Precategory :
    is-section
      ( precomp-hom-Precategory C f z)
      ( map-inv-precomp-hom-is-iso-Precategory)
  is-section-map-inv-precomp-hom-is-iso-Precategory = {!!}

  is-retraction-map-inv-precomp-hom-is-iso-Precategory :
    is-retraction
      ( precomp-hom-Precategory C f z)
      ( map-inv-precomp-hom-is-iso-Precategory)
  is-retraction-map-inv-precomp-hom-is-iso-Precategory = {!!}

  is-equiv-precomp-hom-is-iso-Precategory :
    is-equiv (precomp-hom-Precategory C f z)
  is-equiv-precomp-hom-is-iso-Precategory = {!!}

  equiv-precomp-hom-is-iso-Precategory :
    hom-Precategory C y z ≃ hom-Precategory C x z
  equiv-precomp-hom-is-iso-Precategory = {!!}

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  (z : obj-Precategory C)
  where

  is-equiv-precomp-hom-iso-Precategory :
    is-equiv (precomp-hom-Precategory C (hom-iso-Precategory C f) z)
  is-equiv-precomp-hom-iso-Precategory = {!!}

  equiv-precomp-hom-iso-Precategory :
    hom-Precategory C y z ≃ hom-Precategory C x z
  equiv-precomp-hom-iso-Precategory = {!!}
```

### A morphism `f` is an isomorphism if and only if postcomposition by `f` is an equivalence

**Proof:** If `f` is an isomorphism with inverse `f⁻¹`, then postcomposing with
`f⁻¹` is an inverse of postcomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that postcomposing with `f` is an equivalence, for any object `z`. Then

```text
  f ∘ - : hom y x → hom y y
```

is an equivalence. In particular, there is a unique morphism `g : y → x` such
that `f ∘ g ＝ id`. Thus we have a section of `f`. To see that `g` is also a
retraction, note that the map

```text
  f ∘ - : hom x x → hom x y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `f ∘ (g ∘ f) ＝ f ∘ id`. To see this, we calculate

```text
  f ∘ (g ∘ f) ＝ (f ∘ g) ∘ f ＝ id ∘ f ＝ f ＝ f ∘ id.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (H : (z : obj-Precategory C) → is-equiv (postcomp-hom-Precategory C f z))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Precategory : hom-Precategory C y x
  hom-inv-is-iso-is-equiv-postcomp-hom-Precategory = {!!}

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( f)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory = {!!}

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory :
    comp-hom-Precategory C
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategory)
      ( f) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory = {!!}

  is-iso-is-equiv-postcomp-hom-Precategory : is-iso-Precategory C f
  pr1 is-iso-is-equiv-postcomp-hom-Precategory = {!!}

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (is-iso-f : is-iso-Precategory C f)
  (z : obj-Precategory C)
  where

  map-inv-postcomp-hom-is-iso-Precategory :
    hom-Precategory C z y → hom-Precategory C z x
  map-inv-postcomp-hom-is-iso-Precategory = {!!}

  is-section-map-inv-postcomp-hom-is-iso-Precategory :
    is-section
      ( postcomp-hom-Precategory C f z)
      ( map-inv-postcomp-hom-is-iso-Precategory)
  is-section-map-inv-postcomp-hom-is-iso-Precategory = {!!}

  is-retraction-map-inv-postcomp-hom-is-iso-Precategory :
    is-retraction
      ( postcomp-hom-Precategory C f z)
      ( map-inv-postcomp-hom-is-iso-Precategory)
  is-retraction-map-inv-postcomp-hom-is-iso-Precategory = {!!}

  is-equiv-postcomp-hom-is-iso-Precategory :
    is-equiv (postcomp-hom-Precategory C f z)
  is-equiv-postcomp-hom-is-iso-Precategory = {!!}

  equiv-postcomp-hom-is-iso-Precategory :
    hom-Precategory C z x ≃ hom-Precategory C z y
  equiv-postcomp-hom-is-iso-Precategory = {!!}

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  (z : obj-Precategory C)
  where

  is-equiv-postcomp-hom-iso-Precategory :
    is-equiv (postcomp-hom-Precategory C (hom-iso-Precategory C f) z)
  is-equiv-postcomp-hom-iso-Precategory = {!!}

  equiv-postcomp-hom-iso-Precategory :
    hom-Precategory C z x ≃ hom-Precategory C z y
  equiv-postcomp-hom-iso-Precategory = {!!}
```

### When `hom x y` is a proposition, The type of isomorphisms from `x` to `y` is a proposition

The type of isomorphisms between objects `x y : A` is a subtype of `hom x y`, so
when this type is a proposition, then the type of isomorphisms from `x` to `y`
form a proposition.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-prop-iso-is-prop-hom-Precategory :
    is-prop (hom-Precategory C x y) → is-prop (iso-Precategory C x y)
  is-prop-iso-is-prop-hom-Precategory = {!!}

  iso-prop-is-prop-hom-Precategory :
    is-prop (hom-Precategory C x y) → Prop l2
  iso-prop-is-prop-hom-Precategory = {!!}
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a morphism in each direction to construct an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-iso-is-prop-hom-Precategory' :
    is-prop (hom-Precategory C x x) →
    is-prop (hom-Precategory C y y) →
    (f : hom-Precategory C x y) →
    hom-Precategory C y x →
    is-iso-Precategory C f
  is-iso-is-prop-hom-Precategory' = {!!}

  iso-is-prop-hom-Precategory' :
    is-prop (hom-Precategory C x x) →
    is-prop (hom-Precategory C y y) →
    hom-Precategory C x y →
    hom-Precategory C y x →
    iso-Precategory C x y
  iso-is-prop-hom-Precategory' = {!!}

  is-iso-is-prop-hom-Precategory :
    ((x' y' : obj-Precategory C) → is-prop (hom-Precategory C x' y')) →
    (f : hom-Precategory C x y) → hom-Precategory C y x →
    is-iso-Precategory C f
  is-iso-is-prop-hom-Precategory = {!!}

  iso-is-prop-hom-Precategory :
    ((x' y' : obj-Precategory C) → is-prop (hom-Precategory C x' y')) →
    hom-Precategory C x y →
    hom-Precategory C y x →
    iso-Precategory C x y
  iso-is-prop-hom-Precategory = {!!}
```

### Functoriality of `iso-eq`

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  where

  preserves-concat-iso-eq-Precategory :
    (p : x ＝ y) (q : y ＝ z) →
    iso-eq-Precategory C x z (p ∙ q) ＝
    comp-iso-Precategory C
      ( iso-eq-Precategory C y z q)
      ( iso-eq-Precategory C x y p)
  preserves-concat-iso-eq-Precategory = {!!}
```
