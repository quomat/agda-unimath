# The universal propert of cartesian product types

```agda
module foundation.universal-property-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

The universal property of cartesian products characterizes maps into a cartesian
product

## Theorems

### The universal property of cartesian products as pullbacks

```agda
map-up-product :
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3} →
  ((x : X) → A x × B x) → (((x : X) → A x) × ((x : X) → B x))
pr1 (map-up-product f) x = {!!}
pr2 (map-up-product f) x = {!!}

up-product :
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3} →
  is-equiv (map-up-product {A = A} {B})
up-product = {!!}

equiv-up-product :
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3} →
  ((x : X) → A x × B x) ≃ (((x : X) → A x) × ((x : X) → B x))
pr1 equiv-up-product = {!!}
pr2 equiv-up-product = {!!}
```

We construct the cone for two maps into the unit type.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  cone-prod : cone (const A unit star) (const B unit star) (A × B)
  pr1 cone-prod = {!!}
```

Cartesian products are a special case of pullbacks.

```agda
  gap-prod : A × B → standard-pullback (const A unit star) (const B unit star)
  gap-prod = {!!}

  inv-gap-prod :
    standard-pullback (const A unit star) (const B unit star) → A × B
  pr1 (inv-gap-prod (pair a (pair b p))) = {!!}

  abstract
    is-section-inv-gap-prod : (gap-prod ∘ inv-gap-prod) ~ id
    is-section-inv-gap-prod (pair a (pair b p)) = {!!}

  abstract
    is-retraction-inv-gap-prod : (inv-gap-prod ∘ gap-prod) ~ id
    is-retraction-inv-gap-prod (pair a b) = {!!}

  abstract
    is-pullback-prod :
      is-pullback (const A unit star) (const B unit star) cone-prod
    is-pullback-prod = {!!}
```

We conclude that cartesian products satisfy the universal property of pullbacks.

```agda
  abstract
    universal-property-pullback-prod :
      universal-property-pullback
        ( const A unit star)
        ( const B unit star)
        ( cone-prod)
    universal-property-pullback-prod = {!!}
```
