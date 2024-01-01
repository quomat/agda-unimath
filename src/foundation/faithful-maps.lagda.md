# Faithful maps

```agda
module foundation.faithful-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
```

</details>

## Idea

Since we sometimes think of types as ∞-groupoids, with the groupoid structure
provided implicitly by the identity type and its induction principle, we can
think of maps as functors of ∞-groupoids. We borrow some terminology of
functors, and call a map faithful if it induces embeddings on identity types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-faithful : (A → B) → UU (l1 ⊔ l2)
  is-faithful f = {!!}

faithful-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
faithful-map A B = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-faithful-map : faithful-map A B → A → B
  map-faithful-map = {!!}

  is-faithful-map-faithful-map :
    (f : faithful-map A B) → is-faithful (map-faithful-map f)
  is-faithful-map-faithful-map = {!!}

  emb-ap-faithful-map :
    (f : faithful-map A B) {x y : A} →
    (x ＝ y) ↪ (map-faithful-map f x ＝ map-faithful-map f y)
  emb-ap-faithful-map = {!!}

  is-faithful-is-emb : {f : A → B} → is-emb f → is-faithful f
  is-faithful-is-emb {f} H x y = {!!}

  faithful-map-emb : (A ↪ B) → faithful-map A B
  pr1 (faithful-map-emb f) = {!!}

  is-faithful-is-equiv : {f : A → B} → is-equiv f → is-faithful f
  is-faithful-is-equiv H = {!!}

  faithful-map-equiv : (A ≃ B) → faithful-map A B
  pr1 (faithful-map-equiv e) = {!!}

  emb-ap : (f : A ↪ B) (x y : A) → (x ＝ y) ↪ (map-emb f x ＝ map-emb f y)
  pr1 (emb-ap f x y) = {!!}
```

## Examples

### The identity map is faithful

```agda
module _
  {l : Level} {A : UU l}
  where

  id-faithful-map : faithful-map A A
  id-faithful-map = {!!}

  is-faithful-id-faithful-map : is-faithful (id {A = A})
  is-faithful-id-faithful-map = {!!}
```

### Any `0`-map is faithful

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-0-map-is-faithful : is-faithful f → is-0-map f
  is-0-map-is-faithful H = {!!}

  is-faithful-is-0-map : is-0-map f → is-faithful f
  is-faithful-is-0-map H x y = {!!}
```

## Properties

### The projection map of a family of sets is faithful

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-faithful-pr1 :
      {B : A → UU l2} → ((x : A) → is-set (B x)) → is-faithful (pr1 {B = B})
    is-faithful-pr1 H = {!!}

  pr1-faithful-map :
    (B : A → Set l2) → faithful-map (Σ A (λ x → type-Set (B x))) A
  pr1-faithful-map = {!!}
```

### Faithful maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  where

  abstract
    is-faithful-htpy : is-faithful g → is-faithful f
    is-faithful-htpy K = {!!}
```

### Faithful maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-faithful-comp :
      (g : B → X) (h : A → B) →
      is-faithful g → is-faithful h → is-faithful (g ∘ h)
    is-faithful-comp = {!!}

  abstract
    is-faithful-left-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-faithful g → is-faithful h → is-faithful f
    is-faithful-left-map-triangle = {!!}
```

### If a composite is faithful, then its right factor is faithful

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-faithful-right-factor :
    (g : B → X) (h : A → B) →
    is-faithful g → is-faithful (g ∘ h) → is-faithful h
  is-faithful-right-factor = {!!}

  is-faithful-top-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-faithful g → is-faithful f → is-faithful h
  is-faithful-top-map-triangle = {!!}
```

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  is-faithful-tot : ((x : A) → is-faithful (f x)) → is-faithful (tot f)
  is-faithful-tot H = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  tot-faithful-map :
    ((x : A) → faithful-map (B x) (C x)) → faithful-map (Σ A B) (Σ A C)
  tot-faithful-map = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  module _
    {f : A → B} (C : B → UU l3)
    where

    abstract
      is-faithful-map-Σ-map-base :
        is-faithful f → is-faithful (map-Σ-map-base f C)
      is-faithful-map-Σ-map-base = {!!}

  faithful-map-Σ-faithful-map-base :
    (f : faithful-map A B) (C : B → UU l3) →
    faithful-map (Σ A (λ a → C (map-faithful-map f a))) (Σ B C)
  faithful-map-Σ-faithful-map-base = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
  where

  is-faithful-map-Σ :
    is-faithful f → ((x : A) → is-faithful (g x)) → is-faithful (map-Σ D f g)
  is-faithful-map-Σ = {!!}
```
