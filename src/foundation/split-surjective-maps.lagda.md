# Split surjective maps

```agda
module foundation.split-surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.injective-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A map `f : A → B` is split surjective if we can construct for every `b : B` an
element in the fiber of `b`, meaning an element `a : A` equipped with an
identification `f a ＝ b`.

## Warning

Note that split-surjectiveness is the Curry-Howard interpretation of
surjectiveness. However, this is not a property, and the split surjective maps
don't fit in a factorization system along with the injective maps.

## Definition

### Split surjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-split-surjective : (A → B) → UU (l1 ⊔ l2)
  is-split-surjective = {!!}

  split-surjection : UU (l1 ⊔ l2)
  split-surjection = {!!}

  map-split-surjection : split-surjection → (A → B)
  map-split-surjection = {!!}

  is-split-surjective-split-surjection :
    (f : split-surjection) → is-split-surjective (map-split-surjection f)
  is-split-surjective-split-surjection = {!!}
```

## Properties

### Split surjections are equivalent to maps equipped with a section

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  section-is-split-surjective : is-split-surjective f → section f
  section-is-split-surjective = {!!}

  is-split-surjective-section : section f → is-split-surjective f
  is-split-surjective-section = {!!}

  equiv-section-is-split-surjective : is-split-surjective f ≃ section f
  equiv-section-is-split-surjective = {!!}

  equiv-is-split-surjective-section : section f ≃ is-split-surjective f
  equiv-is-split-surjective-section = {!!}
```

### A map is an equivalence if and only if it is injective and split surjective

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  retraction-is-split-surjective-is-injective :
    is-injective f → is-split-surjective f → retraction f
  retraction-is-split-surjective-is-injective = {!!}

  is-equiv-is-split-surjective-is-injective :
    is-injective f → is-split-surjective f → is-equiv f
  is-equiv-is-split-surjective-is-injective = {!!}

  is-split-surjective-is-equiv : is-equiv f → is-split-surjective f
  is-split-surjective-is-equiv = {!!}

  is-split-surjective-is-injective-is-equiv :
    is-equiv f → is-injective f × is-split-surjective f
  is-split-surjective-is-injective-is-equiv = {!!}
```
