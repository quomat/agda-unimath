# Diagonal maps of types

```agda
module foundation-core.diagonal-maps-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

The diagonal map `δ : A → A × A` of `A` is the map that includes `A` as the
diagonal into `A × A`.

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where

  diagonal : A → A × A
  pr1 (diagonal x) = {!!}
```

## Properties

### The action on paths of a diagonal

```agda
ap-diagonal :
  {l : Level} {A : UU l} {x y : A} (p : x ＝ y) →
  ap (diagonal A) p ＝ eq-pair p p
ap-diagonal refl = {!!}
```

### If the diagonal of `A` is an equivalence, then `A` is a proposition

```agda
module _
  {l : Level} (A : UU l)
  where

  abstract
    is-prop-is-equiv-diagonal : is-equiv (diagonal A) → is-prop A
    is-prop-is-equiv-diagonal is-equiv-d = {!!}

  equiv-diagonal-is-prop :
    is-prop A → A ≃ (A × A)
  pr1 (equiv-diagonal-is-prop is-prop-A) = {!!}
```

### The fibers of the diagonal map

```agda
module _
  {l : Level} (A : UU l)
  where

  eq-fiber-diagonal : (t : A × A) → fiber (diagonal A) t → pr1 t ＝ pr2 t
  eq-fiber-diagonal (pair x y) (pair z α) = {!!}

  fiber-diagonal-eq : (t : A × A) → pr1 t ＝ pr2 t → fiber (diagonal A) t
  pr1 (fiber-diagonal-eq (pair x y) β) = {!!}

  is-section-fiber-diagonal-eq :
    (t : A × A) → ((eq-fiber-diagonal t) ∘ (fiber-diagonal-eq t)) ~ id
  is-section-fiber-diagonal-eq (pair x .x) refl = {!!}

  is-retraction-fiber-diagonal-eq :
    (t : A × A) → ((fiber-diagonal-eq t) ∘ (eq-fiber-diagonal t)) ~ id
  is-retraction-fiber-diagonal-eq .(pair z z) (pair z refl) = {!!}

  abstract
    is-equiv-eq-fiber-diagonal : (t : A × A) → is-equiv (eq-fiber-diagonal t)
    is-equiv-eq-fiber-diagonal t = {!!}
```
