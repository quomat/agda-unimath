# Retractions

```agda
module foundation.retractions where

open import foundation-core.retractions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coslice
open import foundation.dependent-pair-types
open import foundation.retracts-of-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.whiskering-homotopies
```

</details>

## Properties

### Characterizing the identity type of `retraction f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-retraction :
    (g h : retraction f) → map-retraction f g ~ map-retraction f h → UU l1
  coherence-htpy-retraction = {!!}

  htpy-retraction : retraction f → retraction f → UU (l1 ⊔ l2)
  htpy-retraction = {!!}

  extensionality-retraction :
    (g h : retraction f) → (g ＝ h) ≃ htpy-retraction g h
  extensionality-retraction = {!!}

  eq-htpy-retraction :
    ( g h : retraction f)
    ( H : map-retraction f g ~ map-retraction f h)
    ( K :
      ( is-retraction-map-retraction f g) ~
      ( (H ·r f) ∙h is-retraction-map-retraction f h)) →
    g ＝ h
  eq-htpy-retraction = {!!}
```

### If the left factor of a composite has a retraction, then the type of retractions of the right factor is a retract of the type of retractions of the composite

```agda
is-retraction-retraction-left-map-triangle :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ (g ∘ h)) (rg : retraction g) →
  ( ( retraction-top-map-triangle f g h H) ∘
    ( retraction-left-map-triangle f g h H rg)) ~ id
is-retraction-retraction-left-map-triangle f g h H (l , L) (k , K) = {!!}

retraction-right-factor-retract-of-retraction-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) →
  retraction g → (retraction h) retract-of (retraction f)
pr1 (retraction-right-factor-retract-of-retraction-left-factor f g h H rg) = {!!}
pr1
  ( pr2
    ( retraction-right-factor-retract-of-retraction-left-factor f g h H rg)) = {!!}
pr2
  ( pr2
    ( retraction-right-factor-retract-of-retraction-left-factor f g h H rg)) = {!!}
```

### If `f` has a retraction, then `f` is injective

```agda
abstract
  is-injective-retraction :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → retraction f →
    is-injective f
  is-injective-retraction f (h , H) {x} {y} p = {!!}
```

### Transposing identifications along retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  transpose-eq-retraction :
    (g : B → A) (H : (g ∘ f) ~ id) {x : B} {y : A} →
    x ＝ f y → g x ＝ y
  transpose-eq-retraction g H refl = {!!}

  transpose-eq-retraction' :
    (g : B → A) (H : (g ∘ f) ~ id) {x : A} {y : B} →
    f x ＝ y → x ＝ g y
  transpose-eq-retraction' g H refl = {!!}
```
