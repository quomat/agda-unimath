# Retracts of maps

```agda
module foundation.retracts-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.universe-levels
```

</details>

## Idea

A map `f : A → B` is said to be a **retract** of a map `g : X → Y` if it is a
retract in the arrow category of types. In other words, `f` is a retract of `g`
if there are [morphisms of arrows](foundation.morphisms-arrows.md) `i : f → g`
and `r : g → f` equipped with a homotopy of morphisms of arrows `r ∘ i ~ id`.

More explicitly, it consists of [retracts](foundation-core.retractions.md) `A`
of `X` and `B` of `Y` that fit into a commutative diagram

```text
         i₀        r₀
    A ------> X ------> A
    |         |         |
  f |    i    | g   r   | f
    v         v         v
    B ------> Y ------> B
         i₁        r₁
```

with coherences

```text
  i : i₁ ∘ f ~ g ∘ i₀  and   r : r₁ ∘ g ~ f ∘ r₀
```

witnessing that the left and right
[squares commute](foundation-core.commuting-squares-of-maps.md), and a higher
coherence

```text
                    r₀ ·r i₀
       r₁ ∘ g ∘ i₀ ----------> f ∘ r₀ ∘ i₀
            |                      |
            |                      |
  r₁ ·l i⁻¹ |          L           | f ·l H₀
            |                      |
            V                      V
      r₁ ∘ i₁ ∘ f ---------------> f
                       H₁ ·r f
```

witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md) commutes,
where `H₀` and `H₁` are the retracting homotopies of `r₀ ∘ i₀` and `r₁ ∘ i₁`
respectively.

## Definition

### The predicate of being a retraction of a morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g) (r : hom-arrow g f)
  where

  is-retraction-hom-arrow : UU (l1 ⊔ l2)
  is-retraction-hom-arrow = {!!}
```

### The type of retractions of a morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g)
  where

  retraction-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  retraction-hom-arrow = {!!}

  module _
    (r : retraction-hom-arrow)
    where

    hom-retraction-hom-arrow : hom-arrow g f
    hom-retraction-hom-arrow = {!!}

    is-retraction-hom-retraction-hom-arrow :
      is-retraction-hom-arrow f g i hom-retraction-hom-arrow
    is-retraction-hom-retraction-hom-arrow = {!!}
```

### The predicate that a morphism `f` is a retract of a morphism `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  retract-map : (g : X → Y) (f : A → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  retract-map = {!!}
```

### The higher coherence in the definition of retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g) (r : hom-arrow g f)
  where

  coherence-retract-map :
    is-retraction (map-domain-hom-arrow f g i) (map-domain-hom-arrow g f r) →
    is-retraction
      ( map-codomain-hom-arrow f g i)
      ( map-codomain-hom-arrow g f r) →
    UU (l1 ⊔ l2)
  coherence-retract-map = {!!}
```

### The binary relation `f g ↦ f retract-of-map g` asserting that `f` is a retract of the map `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  infix 6 _retract-of-map_

  _retract-of-map_ : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  _retract-of-map_ = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g)
  where

  inclusion-retract-map : hom-arrow f g
  inclusion-retract-map = {!!}

  map-domain-inclusion-retract-map : A → X
  map-domain-inclusion-retract-map = {!!}

  map-codomain-inclusion-retract-map : B → Y
  map-codomain-inclusion-retract-map = {!!}

  coh-inclusion-retract-map :
    coherence-square-maps
      ( map-domain-inclusion-retract-map)
      ( f)
      ( g)
      ( map-codomain-inclusion-retract-map)
  coh-inclusion-retract-map = {!!}

  retraction-retract-map : retraction-hom-arrow f g inclusion-retract-map
  retraction-retract-map = {!!}

  hom-retraction-retract-map : hom-arrow g f
  hom-retraction-retract-map = {!!}

  map-domain-hom-retraction-retract-map : X → A
  map-domain-hom-retraction-retract-map = {!!}

  map-codomain-hom-retraction-retract-map : Y → B
  map-codomain-hom-retraction-retract-map = {!!}

  coh-hom-retraction-retract-map :
    coherence-square-maps
      ( map-domain-hom-retraction-retract-map)
      ( g)
      ( f)
      ( map-codomain-hom-retraction-retract-map)
  coh-hom-retraction-retract-map = {!!}

  is-retraction-hom-retraction-retract-map :
    is-retraction-hom-arrow f g inclusion-retract-map hom-retraction-retract-map
  is-retraction-hom-retraction-retract-map = {!!}

  is-retraction-map-domain-hom-retraction-retract-map :
    is-retraction
      ( map-domain-inclusion-retract-map)
      ( map-domain-hom-retraction-retract-map)
  is-retraction-map-domain-hom-retraction-retract-map = {!!}

  retract-domain-retract-map :
    A retract-of X
  retract-domain-retract-map = {!!}

  is-retraction-map-codomain-hom-retraction-retract-map :
    is-retraction
      ( map-codomain-inclusion-retract-map)
      ( map-codomain-hom-retraction-retract-map)
  is-retraction-map-codomain-hom-retraction-retract-map = {!!}

  retract-codomain-retract-map : B retract-of Y
  retract-codomain-retract-map = {!!}

  coh-retract-map :
    coherence-retract-map f g
      ( inclusion-retract-map)
      ( hom-retraction-retract-map)
      ( is-retraction-map-domain-hom-retraction-retract-map)
      ( is-retraction-map-codomain-hom-retraction-retract-map)
  coh-retract-map = {!!}
```

## Properties

### Retracts of maps with sections have sections

In fact, we only need the following data to show this:

```text
                 r₀
            X ------> A
            |         |
          g |    r    | f
            v         v
  B ------> Y ------> B.
       i₁   H₁   r₁
```

**Proof:** Note that `f` is the right map of a triangle

```text
            r₀
       X ------> A
        \       /
  r₁ ∘ g \     / f
          \   /
           V V
            B.
```

Since both `r₁` and `g` are assumed to have
[sections](foundation-core.sections.md), it follows that the composite `r₁ ∘ g`
has a section, and therefore `f` has a section.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (r₀ : X → A) (R₁ : B retract-of Y)
  (r : coherence-square-maps r₀ g f (map-retraction-retract R₁))
  (s : section g)
  where

  section-retract-map-section' : section f
  section-retract-map-section' = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g)
  where

  section-retract-map-section : section g → section f
  section-retract-map-section = {!!}
```

### Retracts of maps with retractions have retractions

In fact, we only need the following data to show this:

```text
         i₀    H   r₀
    A ------> X ------> A
    |         |
  f |    i    | g
    v         v
    B ------> Y.
         i₁
```

**Proof:** Note that `f` is the top map in the triangle

```text
            f
       A ------> B
        \       /
  g ∘ i₀ \     / i₁
          \   /
           V V
            Y.
```

Since both `g` and `i₀` are assumed to have retractions, it follows that
`g ∘ i₀` has a retraction, and hence that `f` has a retraction.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (i₁ : B → Y)
  (i : coherence-square-maps (inclusion-retract R₀) f g i₁)
  (s : retraction g)
  where

  retraction-retract-map-retraction' : retraction f
  retraction-retract-map-retraction' = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g)
  where

  retraction-retract-map-retraction : retraction g → retraction f
  retraction-retract-map-retraction = {!!}
```

### Equivalences are closed under retracts of maps

Note that the higher coherence of a retract of maps is not needed.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (R₁ : B retract-of Y)
  (i : coherence-square-maps (inclusion-retract R₀) f g (inclusion-retract R₁))
  (r :
    coherence-square-maps
      ( map-retraction-retract R₀)
      ( g)
      ( f)
      ( map-retraction-retract R₁))
  (H : is-equiv g)
  where

  is-equiv-retract-map-is-equiv' : is-equiv f
  is-equiv-retract-map-is-equiv' = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g) (H : is-equiv g)
  where

  section-retract-map-is-equiv : section f
  section-retract-map-is-equiv = {!!}

  retraction-retract-map-is-equiv : retraction f
  retraction-retract-map-is-equiv = {!!}

  is-equiv-retract-map-is-equiv : is-equiv f
  is-equiv-retract-map-is-equiv = {!!}
```

### If `f` is a retract of `g`, then the fiber inclusions of `f` are retracts of the fiber inclusions of `g`

Consider a retract `f : A → B` of a map `g : X → Y`, as indicated in the bottom
row of squares in the diagram below.

```text
              j                     s
  fiber f b -----> fiber g (i₁ b) -----> fiber f b
     |                 |                    |
     |       i'        |         r'         |
     v                 v                    v
     A ----- i₀ -----> X ------- r₀ ------> A
     |                 |                    |
   f |       i         | g       r          | f
     v                 v                    v
     B --------------> Y -----------------> B
             i₁                  r₁
```

Then we claim that the [fiber inclusion](foundation-core.fibers-of-maps.md)
`fiber f b → A` is a retract of the fiber inclusion `fiber g (i' x) → X`.

**Proof:** By
[functoriality of fibers of maps](foundation.functoriality-fibers-of-maps.md) we
obtain a commuting diagram

```text
              j                     s                          ≃
  fiber f b -----> fiber g (i₁ b) -----> fiber f (r₀ (i₀ b)) -----> fiber f b
     |                 |                       |                        |
     |       i'        |           r'          |                        |
     v                 v                       v                        V
     A --------------> X --------------------> A ---------------------> A
             i₀                    r₀                       id
```

which is homotopic to the identity morphism of arrows. We then finish off the
proof with the following steps:

1. We reassociate the composition of morphisms of fibers, which is associated in
   the above diagram as `□ (□ □)`.
2. Then we use that `hom-arrow-fiber` preserves composition.
3. Next, we apply the action on `htpy-hom-arrow` of `fiber`.
4. Finally, we use that `hom-arrow-fiber` preserves identity morphisms of
   arrows.

While each of these steps are very simple to formalize, the operations that are
involved take a lot of arguments and therefore the code is somewhat lengthy.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g) (b : B)
  where

  inclusion-retract-map-inclusion-fiber-retract-map :
    hom-arrow
      ( inclusion-fiber f {b})
      ( inclusion-fiber g {map-codomain-inclusion-retract-map f g R b})
  inclusion-retract-map-inclusion-fiber-retract-map = {!!}

  hom-retraction-retract-map-inclusion-fiber-retract-map :
    hom-arrow
      ( inclusion-fiber g {map-codomain-inclusion-retract-map f g R b})
      ( inclusion-fiber f {b})
  hom-retraction-retract-map-inclusion-fiber-retract-map = {!!}

  is-retraction-hom-retraction-retract-map-inclusion-fiber-retract-map :
    is-retraction-hom-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber g)
      ( inclusion-retract-map-inclusion-fiber-retract-map)
      ( hom-retraction-retract-map-inclusion-fiber-retract-map)
  is-retraction-hom-retraction-retract-map-inclusion-fiber-retract-map = {!!}

  retract-map-inclusion-fiber-retract-map :
    retract-map
      ( inclusion-fiber g {map-codomain-inclusion-retract-map f g R b})
      ( inclusion-fiber f {b})
  retract-map-inclusion-fiber-retract-map = {!!}
```

### If `f` is a retract of `g`, then the fibers of `f` are retracts of the fibers of `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g) (b : B)
  where

  retract-fiber-retract-map :
    retract
      ( fiber g (map-codomain-inclusion-retract-map f g R b))
      ( fiber f b)
  retract-fiber-retract-map = {!!}
```

## References

1. Section 4.7 of Univalent Foundations Project, _Homotopy Type Theory –
   Univalent Foundations of Mathematics_ (2013)
   ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))

## External links

- [Retracts in arrow categories](https://ncatlab.org/nlab/show/retract#in_arrow_categories)
  at $n$Lab

A wikidata identifier was not available for this concept.
