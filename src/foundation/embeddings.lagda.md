# Embeddings

```agda
module foundation.embeddings where

open import foundation-core.embeddings public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being an embedding is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-property-is-emb : (f : A → B) → is-prop (is-emb f)
  is-property-is-emb f = {!!}

  is-emb-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-emb-Prop f) = {!!}
```

### Embeddings are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-htpy : {f g : A → B} (H : f ~ g) → is-emb g → is-emb f
    is-emb-htpy {f} {g} H is-emb-g x y = {!!}

  is-emb-htpy-emb : {f : A → B} (e : A ↪ B) → f ~ map-emb e → is-emb f
  is-emb-htpy-emb e H = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-htpy' : {f g : A → B} (H : f ~ g) → is-emb f → is-emb g
    is-emb-htpy' H is-emb-f = {!!}

  is-emb-htpy-emb' : (e : A ↪ B) {g : A → B} → map-emb e ~ g → is-emb g
  is-emb-htpy-emb' e H = {!!}
```

### Any map between propositions is an embedding

```agda
is-emb-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop A → is-prop B → is-emb f
is-emb-is-prop H K = {!!}
```

### Embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-comp :
    (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
  is-emb-comp g h is-emb-g is-emb-h x y = {!!}

  abstract
    is-emb-left-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-emb g → is-emb h → is-emb f
    is-emb-left-map-triangle f g h H is-emb-g is-emb-h = {!!}

  comp-emb :
    (B ↪ C) → (A ↪ B) → (A ↪ C)
  pr1 (comp-emb (g , H) (f , K)) = {!!}
```

### The right factor of a composed embedding is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-right-factor :
    (g : B → C) (h : A → B) →
    is-emb g → is-emb (g ∘ h) → is-emb h
  is-emb-right-factor g h is-emb-g is-emb-gh x y = {!!}

  abstract
    is-emb-top-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-emb g → is-emb f → is-emb h
    is-emb-top-map-triangle f g h H is-emb-g is-emb-f x y = {!!}

  abstract
    is-emb-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e → is-emb f → is-emb g
    is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f = {!!}
```

### The map on total spaces induced by a family of embeddings is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-emb-tot :
    {f : (x : A) → B x → C x} → ((x : A) → is-emb (f x)) → is-emb (tot f)
  is-emb-tot H = {!!}

  emb-tot : ((x : A) → B x ↪ C x) → Σ A B ↪ Σ A C
  pr1 (emb-tot f) = {!!}
```

### The functoriality of dependent pair types preserves embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) → is-emb f → is-emb (map-Σ-map-base f C)
    is-emb-map-Σ-map-base C H = {!!}

  emb-Σ-emb-base :
    (f : A ↪ B) (C : B → UU l3) → Σ A (λ a → C (map-emb f a)) ↪ Σ B C
  pr1 (emb-Σ-emb-base f C) = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-emb-map-Σ :
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-emb f → ((x : A) → is-emb (g x)) → is-emb (map-Σ D f g)
  is-emb-map-Σ D H K = {!!}

  emb-Σ :
    (D : B → UU l4) (f : A ↪ B) (g : (x : A) → C x ↪ D (map-emb f x)) →
    Σ A C ↪ Σ B D
  pr1 (emb-Σ D f g) = {!!}
```

### Equivalence on total spaces induced by embedding on the base types

We saw above that given an embedding `f : A ↪ B` and a type family `C` over `B`
we obtain an embedding

```text
  Σ A (C ∘ f) ↪ Σ B C.
```

This embedding can be upgraded to an equivalence if we furthermore know that the
support of `C` is contained in the image of `f`. More precisely, if we are given
a section `((b , c) : Σ B C) → fiber f b`, then it follows that

```text
  Σ A (C ∘ f) ≃ Σ B C.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} (f : A ↪ B)
  (H : ((b , c) : Σ B C) → fiber (map-emb f) b)
  where

  inv-map-Σ-emb-base : Σ B C → Σ A (C ∘ map-emb f)
  pr1 (inv-map-Σ-emb-base u) = {!!}

  is-section-inv-map-Σ-emb-base :
    is-section (map-Σ-map-base (map-emb f) C) inv-map-Σ-emb-base
  is-section-inv-map-Σ-emb-base (b , c) = {!!}

  is-retraction-inv-map-Σ-emb-base :
    is-retraction (map-Σ-map-base (map-emb f) C) inv-map-Σ-emb-base
  is-retraction-inv-map-Σ-emb-base (a , c) = {!!}

  equiv-Σ-emb-base : Σ A (C ∘ map-emb f) ≃ Σ B C
  pr1 equiv-Σ-emb-base = {!!}
```

### The product of two embeddings is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  emb-prod : (A ↪ C) → (B ↪ D) → ((A × B) ↪ (C × D))
  emb-prod f g = {!!}

  is-emb-map-prod :
    (f : A → C) (g : B → D) → is-emb f → is-emb g → (is-emb (map-prod f g))
  is-emb-map-prod f g is-emb-f is-emb-g = {!!}
```

### If the action on identifications has a section, then `f` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-emb-section-ap :
      ((x y : A) → section (ap f {x = x} {y = y})) → is-emb f
    is-emb-section-ap section-ap-f x y = {!!}
```

### If there is an equivalence `(f x = {!!}

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-emb-equiv-refl-to-refl :
      (e : (x y : A) → (f x ＝ f y) ≃ (x ＝ y)) →
      ((x : A) → map-equiv (e x x) refl ＝ refl) →
      is-emb f
    is-emb-equiv-refl-to-refl e p x y = {!!}
```

### Embeddings are closed under pullback

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-emb-vertical-map-cone-is-pullback :
      is-pullback f g c → is-emb g → is-emb (vertical-map-cone f g c)
    is-emb-vertical-map-cone-is-pullback pb is-emb-g = {!!}

  abstract
    is-emb-horizontal-map-cone-is-pullback :
      is-pullback f g c → is-emb f → is-emb (horizontal-map-cone f g c)
    is-emb-horizontal-map-cone-is-pullback pb is-emb-f = {!!}
```

### In a commuting square of which the sides are embeddings, the top map is an embedding if and only if the bottom map is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  (H : coherence-square-maps top left right bottom)
  where

  is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps :
    is-equiv left → is-equiv right → is-emb bottom → is-emb top
  is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps K L M = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  (H : coherence-square-maps top left right bottom)
  where

  is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps :
    is-equiv left → is-equiv right → is-emb top → is-emb bottom
  is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps K L M = {!!}
```

### A map is an embedding if and only if it has contractible fibers at values

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-emb-is-contr-fibers-values' :
    ((a : A) → is-contr (fiber' f (f a))) → is-emb f
  is-emb-is-contr-fibers-values' c a = {!!}

  is-emb-is-contr-fibers-values :
    ((a : A) → is-contr (fiber f (f a))) → is-emb f
  is-emb-is-contr-fibers-values c = {!!}

  is-contr-fibers-values-is-emb' :
    is-emb f → ((a : A) → is-contr (fiber' f (f a)))
  is-contr-fibers-values-is-emb' e a = {!!}

  is-contr-fibers-values-is-emb :
    is-emb f → ((a : A) → is-contr (fiber f (f a)))
  is-contr-fibers-values-is-emb e a = {!!}
```
