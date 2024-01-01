# Truncated maps

```agda
module foundation.truncated-maps where

open import foundation-core.truncated-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being a truncated map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-trunc-map : (k : 𝕋) (f : A → B) → is-prop (is-trunc-map k f)
  is-prop-is-trunc-map k f = {!!}

  is-trunc-map-Prop : (k : 𝕋) → (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-trunc-map-Prop k f) = {!!}
```

### Pullbacks of truncated maps are truncated maps

```agda
module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-trunc-is-pullback :
      is-pullback f g c → is-trunc-map k g → is-trunc-map k (pr1 c)
    is-trunc-is-pullback pb is-trunc-g a = {!!}

abstract
  is-trunc-is-pullback' :
    {l1 l2 l3 l4 : Level} (k : 𝕋)
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-trunc-map k f → is-trunc-map k (pr1 (pr2 c))
  is-trunc-is-pullback' k f g (pair p (pair q H)) pb is-trunc-f = {!!}
```
