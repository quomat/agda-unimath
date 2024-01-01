# Coherently invertible maps

```agda
module foundation-core.coherently-invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.universe-levels

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

An [inverse](foundation-core.invertible-maps.md) for a map `f : A → B` is a map
`g : B → A` equipped with [homotopies](foundation-core.homotopies.md)
` (f ∘ g) ~ id` and `(g ∘ f) ~ id`. Such data, however is
[structure](foundation.structure.md) on the map `f`, and not generally a
[property](foundation-core.propositions.md). Therefore we include a coherence
condition for the homotopies of an inverse. A **coherently invertible map**
`f : A → B` is a map equipped with a two-sided inverse and this additional
coherence law. They are also called half-adjoint equivalences.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-is-coherently-invertible :
    (f : A → B) (g : B → A) (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible = {!!}

  is-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-coherently-invertible = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-coherently-invertible f)
  where

  map-inv-is-coherently-invertible : B → A
  map-inv-is-coherently-invertible = {!!}

  is-retraction-is-coherently-invertible :
    (f ∘ map-inv-is-coherently-invertible) ~ id
  is-retraction-is-coherently-invertible = {!!}

  is-section-is-coherently-invertible :
    (map-inv-is-coherently-invertible ∘ f) ~ id
  is-section-is-coherently-invertible = {!!}

  coh-is-coherently-invertible :
    coherence-is-coherently-invertible f
      ( map-inv-is-coherently-invertible)
      ( is-retraction-is-coherently-invertible)
      ( is-section-is-coherently-invertible)
  coh-is-coherently-invertible = {!!}

  is-invertible-is-coherently-invertible : is-invertible f
  is-invertible-is-coherently-invertible = {!!}

  section-is-coherently-invertible : section f
  section-is-coherently-invertible = {!!}

  retraction-is-coherently-invertible : retraction f
  retraction-is-coherently-invertible = {!!}
```

## Properties

### Invertible maps are coherently invertible

#### Lemma: A coherence for homotopies to an identity map

```agda
coh-is-coherently-invertible-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ (λ x → x)) →
  (x : A) → H (f x) ＝ ap f (H x)
coh-is-coherently-invertible-id = {!!}
```

#### The proof that invertible maps are coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-section-map-inv-is-invertible :
      (H : is-invertible f) → (f ∘ map-inv-is-invertible H) ~ id
    is-section-map-inv-is-invertible = {!!}

    is-retraction-map-inv-is-invertible :
      (H : is-invertible f) → (map-inv-is-invertible H ∘ f) ~ id
    is-retraction-map-inv-is-invertible = {!!}

    coherence-map-inv-is-invertible :
      ( H : is-invertible f) →
      ( is-section-map-inv-is-invertible H ·r f) ~
      ( f ·l is-retraction-map-inv-is-invertible H)
    coherence-map-inv-is-invertible = {!!}

  abstract
    is-coherently-invertible-is-invertible :
      (H : is-invertible f) → is-coherently-invertible f
    is-coherently-invertible-is-invertible = {!!}
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
