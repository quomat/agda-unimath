# Invertible maps

```agda
module foundation-core.invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

An **inverse** for a map `f : A → B` is a map `g : B → A` equipped with
[homotopies](foundation-core.homotopies.md) ` (f ∘ g) ~ id` and `(g ∘ f) ~ id`.
Such data, however is [structure](foundation.structure.md) on the map `f`, and
not generally a [property](foundation-core.propositions.md).

## Definition

### The predicate that a map `g` is an inverse of a map `f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inverse : (A → B) → (B → A) → UU (l1 ⊔ l2)
  is-inverse = {!!}

  is-section-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → (f ∘ g) ~ id
  is-section-is-inverse = {!!}

  is-retraction-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → (g ∘ f) ~ id
  is-retraction-is-inverse = {!!}
```

### The predicate that a map `f` is invertible

```agda
is-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-invertible = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (g : is-invertible f)
  where

  map-inv-is-invertible : B → A
  map-inv-is-invertible = {!!}

  is-inverse-map-inv-is-invertible : is-inverse f map-inv-is-invertible
  is-inverse-map-inv-is-invertible = {!!}

  is-retraction-is-invertible : (f ∘ map-inv-is-invertible) ~ id
  is-retraction-is-invertible = {!!}

  is-section-is-invertible : (map-inv-is-invertible ∘ f) ~ id
  is-section-is-invertible = {!!}

  section-is-invertible : section f
  section-is-invertible = {!!}

  retraction-is-invertible : retraction f
  retraction-is-invertible = {!!}
```

### The type of invertible maps

```agda
invertible-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
invertible-map = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-invertible-map : invertible-map A B → A → B
  map-invertible-map = {!!}

  is-invertible-map-invertible-map :
    (f : invertible-map A B) → is-invertible (map-invertible-map f)
  is-invertible-map-invertible-map = {!!}

  map-inv-invertible-map : invertible-map A B → B → A
  map-inv-invertible-map = {!!}

  is-section-map-invertible-map :
    (f : invertible-map A B) →
    (map-inv-invertible-map f ∘ map-invertible-map f) ~ id
  is-section-map-invertible-map = {!!}

  is-retraction-map-invertible-map :
    (f : invertible-map A B) →
    (map-invertible-map f ∘ map-inv-invertible-map f) ~ id
  is-retraction-map-invertible-map = {!!}
```

## Properties

### The invertible inverse of an invertible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  inv-is-inverse : {g : B → A} → is-inverse f g → is-inverse g f
  inv-is-inverse = {!!}

  inv-is-invertible :
    (g : is-invertible f) → is-invertible (map-inv-is-invertible g)
  inv-is-invertible = {!!}
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
