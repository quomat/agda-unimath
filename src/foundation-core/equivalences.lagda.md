# Equivalences

```agda
module foundation-core.equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

An **equivalence** is a map that has a [section](foundation-core.sections.md)
and a (separate) [retraction](foundation-core.retractions.md). This condition is
also called being **biinvertible**.

The condition of biinvertibility may look odd: Why not say that an equivalence
is a map that has a [2-sided inverse](foundation-core.invertible-maps.md)? The
reason is that the condition of invertibility is
[structure](foundation.structure.md), whereas the condition of being
biinvertible is a [property](foundation-core.propositions.md). To quickly see
this: if `f` is an equivalence, then it has up to
[homotopy](foundation-core.homotopies.md) only one section, and it has up to
homotopy only one retraction.

## Definition

### The predicate of being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv : (A → B) → UU (l1 ⊔ l2)
  is-equiv = {!!}
```

### Components of a proof of equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  section-is-equiv : section f
  section-is-equiv = {!!}

  retraction-is-equiv : retraction f
  retraction-is-equiv = {!!}

  map-section-is-equiv : B → A
  map-section-is-equiv = {!!}

  map-retraction-is-equiv : B → A
  map-retraction-is-equiv = {!!}

  is-section-map-section-is-equiv : is-section f map-section-is-equiv
  is-section-map-section-is-equiv = {!!}

  is-retraction-map-retraction-is-equiv :
    is-retraction f map-retraction-is-equiv
  is-retraction-map-retraction-is-equiv = {!!}
```

### Equivalences

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  equiv : UU (l1 ⊔ l2)
  equiv = {!!}

infix 6 _≃_

_≃_ : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A ≃ B = {!!}
```

### Components of an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv : A → B
  map-equiv = {!!}

  is-equiv-map-equiv : is-equiv map-equiv
  is-equiv-map-equiv = {!!}

  section-map-equiv : section map-equiv
  section-map-equiv = {!!}

  map-section-map-equiv : B → A
  map-section-map-equiv = {!!}

  is-section-map-section-map-equiv :
    is-section map-equiv map-section-map-equiv
  is-section-map-section-map-equiv = {!!}

  retraction-map-equiv : retraction map-equiv
  retraction-map-equiv = {!!}

  map-retraction-map-equiv : B → A
  map-retraction-map-equiv = {!!}

  is-retraction-map-retraction-map-equiv :
    is-retraction map-equiv map-retraction-map-equiv
  is-retraction-map-retraction-map-equiv = {!!}
```

### The identity equivalence

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = {!!}

  id-equiv : A ≃ A
  id-equiv = {!!}
```

## Properties

### A map is invertible if and only if it is an equivalence

**Proof:** It is clear that if a map is
[invertible](foundation-core.invertible-maps.md), then it is also biinvertible,
and hence an equivalence.

For the converse, suppose that `f : A → B` is an equivalence with section
`g : B → A` equipped with `G : f ∘ g ~ id`, and retraction `h : B → A` equipped
with `H : h ∘ f ~ id`. We claim that the map `g : B → A` is also a retraction.
To see this, we concatenate the following homotopies

```text
         H⁻¹ ·r g ·r f                  h ·l G ·r f           H
  g ∘ h ---------------> h ∘ f ∘ g ∘ f -------------> h ∘ f -----> id.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-is-invertible' : is-invertible f → is-equiv f
  is-equiv-is-invertible' = {!!}

  is-equiv-is-invertible :
    (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
  is-equiv-is-invertible = {!!}

  is-retraction-map-section-is-equiv :
    (H : is-equiv f) → is-retraction f (map-section-is-equiv H)
  is-retraction-map-section-is-equiv = {!!}

  is-invertible-is-equiv : is-equiv f → is-invertible f
  is-invertible-is-equiv = {!!}
```

### Coherently invertible maps are equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-coherently-invertible-is-equiv : is-equiv f → is-coherently-invertible f
    is-coherently-invertible-is-equiv = {!!}

  abstract
    is-equiv-is-coherently-invertible :
      is-coherently-invertible f → is-equiv f
    is-equiv-is-coherently-invertible = {!!}
```

### Structure obtained from being coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  map-inv-is-equiv : B → A
  map-inv-is-equiv = {!!}

  is-section-map-inv-is-equiv : is-section f map-inv-is-equiv
  is-section-map-inv-is-equiv = {!!}

  is-retraction-map-inv-is-equiv : is-retraction f map-inv-is-equiv
  is-retraction-map-inv-is-equiv = {!!}

  coherence-map-inv-is-equiv :
    coherence-is-coherently-invertible f
      ( map-inv-is-equiv)
      ( is-section-map-inv-is-equiv)
      ( is-retraction-map-inv-is-equiv)
  coherence-map-inv-is-equiv = {!!}

  is-equiv-map-inv-is-equiv : is-equiv map-inv-is-equiv
  is-equiv-map-inv-is-equiv = {!!}
```

### The inverse of an equivalence is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = {!!}

  is-section-map-inv-equiv : is-section (map-equiv e) map-inv-equiv
  is-section-map-inv-equiv = {!!}

  is-retraction-map-inv-equiv : is-retraction (map-equiv e) map-inv-equiv
  is-retraction-map-inv-equiv = {!!}

  coherence-map-inv-equiv :
    coherence-is-coherently-invertible
      ( map-equiv e)
      ( map-inv-equiv)
      ( is-section-map-inv-equiv)
      ( is-retraction-map-inv-equiv)
  coherence-map-inv-equiv = {!!}

  is-equiv-map-inv-equiv : is-equiv map-inv-equiv
  is-equiv-map-inv-equiv = {!!}

  inv-equiv : B ≃ A
  inv-equiv = {!!}
```

### The 3-for-2 property of equivalences

The **3-for-2 property** of equivalences asserts that for any
[commuting triangle](foundation-core.commuting-triangles-of-maps.md) of maps

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      V V
       X,
```

if two of the three maps are equivalences, then so is the third.

We also record special cases of the 3-for-2 property of equivalences, where we
only assume maps `g : B → X` and `h : A → B`. In this special case, we set
`f := {!!}

[André Joyal](https://en.wikipedia.org/wiki/André_Joyal) proposed calling this
property the 3-for-2 property, despite most mathematicians calling it the
_2-out-of-3 property_. The story goes that on the produce market is is common to
advertise a discount as "3-for-2". If you buy two apples, then you get the third
for free. Similarly, if you prove that two maps in a commuting triangle are
equivalences, then you get the third for free.

#### The left map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ g ∘ h)
  where

  abstract
    is-equiv-left-map-triangle : is-equiv h → is-equiv g → is-equiv f
    is-equiv-left-map-triangle = {!!}
```

#### The right map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  abstract
    is-equiv-right-map-triangle :
      is-equiv f → is-equiv h → is-equiv g
    is-equiv-right-map-triangle = {!!}
```

#### If the left and right maps in a commuting triangle are equivalences, then the top map is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  section-is-equiv-top-map-triangle :
    is-equiv g → is-equiv f → section h
  section-is-equiv-top-map-triangle = {!!}

  map-section-is-equiv-top-map-triangle :
    is-equiv g → is-equiv f → B → A
  map-section-is-equiv-top-map-triangle = {!!}

  abstract
    is-equiv-top-map-triangle :
      is-equiv g → is-equiv f → is-equiv h
    is-equiv-top-map-triangle = {!!}
```

#### Composites of equivalences are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-equiv-comp :
      (g : B → X) (h : A → B) → is-equiv h → is-equiv g → is-equiv (g ∘ h)
    is-equiv-comp = {!!}

  equiv-comp : (B ≃ X) → (A ≃ B) → (A ≃ X)
  equiv-comp = {!!}

  infixr 15 _∘e_
  _∘e_ : (B ≃ X) → (A ≃ B) → (A ≃ X)
  _∘e_ = {!!}
```

#### If a composite and its right factor are equivalences, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-equiv-left-factor :
    (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor = {!!}
```

#### If a composite and its left factor are equivalences, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-equiv-right-factor :
    (g : B → X) (h : A → B) →
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor = {!!}
```

### Equivalences are closed under homotopies

We show that if `f ~ g`, then `f` is an equivalence if and only if `g` is an
equivalence. Furthermore, we show that if `f` and `g` are homotopic equivaleces,
then their inverses are also homotopic.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-htpy :
      {f : A → B} (g : A → B) → f ~ g → is-equiv g → is-equiv f
    is-equiv-htpy = {!!}

  is-equiv-htpy-equiv : {f : A → B} (e : A ≃ B) → f ~ map-equiv e → is-equiv f
  is-equiv-htpy-equiv = {!!}

  abstract
    is-equiv-htpy' : (f : A → B) {g : A → B} → f ~ g → is-equiv f → is-equiv g
    is-equiv-htpy' = {!!}

  is-equiv-htpy-equiv' : (e : A ≃ B) {g : A → B} → map-equiv e ~ g → is-equiv g
  is-equiv-htpy-equiv' = {!!}

  htpy-map-inv-is-equiv :
    {f g : A → B} (G : f ~ g) (H : is-equiv f) (K : is-equiv g) →
    map-inv-is-equiv H ~ map-inv-is-equiv K
  htpy-map-inv-is-equiv = {!!}
```

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retraction :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-equiv f → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction = {!!}
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-equiv f → f ∘ g ~ id → is-equiv g
  is-equiv-is-section = {!!}
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-section-is-equiv :
      ( section-f : section f) → is-equiv (pr1 section-f) → is-equiv f
    is-equiv-section-is-equiv = {!!}
```

### Any section of an equivalence is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  htpy-map-inv-equiv-section :
    (f : section (map-equiv e)) → map-inv-equiv e ~ map-section (map-equiv e) f
  htpy-map-inv-equiv-section = {!!}
```

### Any retraction of an equivalence is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  htpy-map-inv-equiv-retraction :
    (f : retraction (map-equiv e)) →
    map-inv-equiv e ~ map-retraction (map-equiv e) f
  htpy-map-inv-equiv-retraction = {!!}
```

### Equivalences in commuting squares

```agda
is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv = {!!}

is-equiv-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv f → is-equiv g
is-equiv-equiv' = {!!}
```

We will assume a commuting square

```text
        h
    A -----> C
    |        |
  f |        | g
    V        V
    B -----> D
        i
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h))
  where

  abstract
    is-equiv-top-is-equiv-left-square :
      is-equiv i → is-equiv f → is-equiv g → is-equiv h
    is-equiv-top-is-equiv-left-square = {!!}

  abstract
    is-equiv-top-is-equiv-bottom-square :
      is-equiv f → is-equiv g → is-equiv i → is-equiv h
    is-equiv-top-is-equiv-bottom-square = {!!}

  abstract
    is-equiv-bottom-is-equiv-top-square :
      is-equiv f → is-equiv g → is-equiv h → is-equiv i
    is-equiv-bottom-is-equiv-top-square = {!!}

  abstract
    is-equiv-left-is-equiv-right-square :
      is-equiv h → is-equiv i → is-equiv g → is-equiv f
    is-equiv-left-is-equiv-right-square = {!!}

  abstract
    is-equiv-right-is-equiv-left-square :
      is-equiv h → is-equiv i → is-equiv f → is-equiv g
    is-equiv-right-is-equiv-left-square = {!!}
```

### Equivalences are embeddings

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-is-equiv :
      {f : A → B} → is-equiv f → (x y : A) → is-equiv (ap f {x} {y})
    is-emb-is-equiv = {!!}

  equiv-ap :
    (e : A ≃ B) (x y : A) → (x ＝ y) ≃ (map-equiv e x ＝ map-equiv e y)
  equiv-ap = {!!}

  map-inv-equiv-ap :
    (e : A ≃ B) (x y : A) → (map-equiv e x ＝ map-equiv e y) → (x ＝ y)
  map-inv-equiv-ap = {!!}
```

## Equivalence reasoning

Equivalences can be constructed by equational reasoning in the following way:

```text
equivalence-reasoning
  X ≃ Y by equiv-1
    ≃ Z by equiv-2
    ≃ V by equiv-3
```

The equivalence constructed in this way is `equiv-1 ∘e (equiv-2 ∘e equiv-3)`,
i.e., the equivivalence is associated fully to the right.

```agda
infixl 1 equivalence-reasoning_
infixl 0 step-equivalence-reasoning

equivalence-reasoning_ :
  {l1 : Level} (X : UU l1) → X ≃ X
equivalence-reasoning X = {!!}

step-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (Z : UU l3) → (Y ≃ Z) → (X ≃ Z)
step-equivalence-reasoning = {!!}

syntax step-equivalence-reasoning e Z f = {!!}
```

## See also

- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
