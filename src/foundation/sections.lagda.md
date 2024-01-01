# Sections

```agda
module foundation.sections where

open import foundation-core.sections public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.retracts-of-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.whiskering-homotopies
```

</details>

## Definitions

### Sections of the projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-section-family : ((x : A) → B x) → (A → Σ A B)
  pr1 (map-section-family b a) = {!!}

  htpy-map-section-family :
    (b : (x : A) → B x) → (pr1 ∘ map-section-family b) ~ id
  htpy-map-section-family b a = {!!}

  section-dependent-function : ((x : A) → B x) → section (pr1 {B = B})
  pr1 (section-dependent-function b) = {!!}
```

## Properties

### Extensionality of sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-section :
    (s t : section f) → (map-section f s ~ map-section f t) → UU l2
  coherence-htpy-section s t H = {!!}

  htpy-section : (s t : section f) → UU (l1 ⊔ l2)
  htpy-section s t = {!!}

  extensionality-section : (s t : section f) → (s ＝ t) ≃ htpy-section s t
  extensionality-section (s , H) = {!!}

  eq-htpy-section :
    (s t : section f)
    (H : map-section f s ~ map-section f t)
    (K : coherence-htpy-section s t H) →
    s ＝ t
  eq-htpy-section s t H K = {!!}
```

### If the right factor of a composite has a section, then the type of sections of the left factor is a retract of the type of sections of the composite

```agda
is-retraction-section-left-map-triangle :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ (g ∘ h)) (s : section h) →
  section-right-map-triangle f g h H ∘ section-left-map-triangle f g h H s ~ id
is-retraction-section-left-map-triangle f g h H (k , K) (l , L) = {!!}

section-left-factor-retract-of-section-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  section h → (section g) retract-of (section f)
pr1 (section-left-factor-retract-of-section-composition f g h H s) = {!!}
pr1 (pr2 (section-left-factor-retract-of-section-composition f g h H s)) = {!!}

pr2 (pr2 (section-left-factor-retract-of-section-composition f g h H s)) = {!!}
```

### The equivalence of sections of the projection map and sections of the type family

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-section-pr1 : section (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-section-pr1 = {!!}
```

### Any section of a type family is an equivalence if and only if each type in the family is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x)
  where

  is-equiv-map-section-family :
    ((x : A) → is-contr (B x)) → is-equiv (map-section-family b)
  is-equiv-map-section-family C = {!!}

  equiv-section :
    ((x : A) → is-contr (B x)) → A ≃ Σ A B
  pr1 (equiv-section C) = {!!}

  is-contr-fam-is-equiv-map-section-family :
    is-equiv (map-section-family b) → ((x : A) → is-contr (B x))
  is-contr-fam-is-equiv-map-section-family H = {!!}
```

### Any section of a type family is an injective map

```agda
is-injective-map-section-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section-family b)
is-injective-map-section-family b = {!!}
```

### Transposing identifications along sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  transpose-eq-section :
    (g : B → A) (H : (f ∘ g) ~ id) {x : A} {y : B} →
    x ＝ g y → f x ＝ y
  transpose-eq-section g H refl = {!!}

  transpose-eq-section' :
    (g : B → A) (H : (f ∘ g) ~ id) {x : B} {y : A} →
    g x ＝ y → x ＝ f y
  transpose-eq-section' g H refl = {!!}
```
