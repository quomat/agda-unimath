# The universal property of propositional truncations with respect to sets

```agda
module foundation.universal-property-propositional-truncation-into-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
```

</details>

## Idea

The propositional truncation of `A` can be thought of as the quotient of `A` by
the full equivalence relation, i.e., the equivalence relation by which all
elements of `A` are considered to be equivalent. This idea leads to the
universal property of the propositional truncations with respect to sets.

## Definition

### The precomposition map that is used to state the universal property

```agda
is-weakly-constant-map-precomp-unit-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : type-trunc-Prop A → B) →
  is-weakly-constant-map (g ∘ unit-trunc-Prop)
is-weakly-constant-map-precomp-unit-trunc-Prop g x y = {!!}

precomp-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  (type-trunc-Prop A → type-Set B) → Σ (A → type-Set B) is-weakly-constant-map
pr1 (precomp-universal-property-set-quotient-trunc-Prop B g) = {!!}
pr2 (precomp-universal-property-set-quotient-trunc-Prop B g) = {!!}
```

## Properties

### The image of the propositional truncation into a set is a proposition

```agda
abstract
  all-elements-equal-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-weakly-constant-map f →
    all-elements-equal (Σ (type-Set B) (λ b → type-trunc-Prop (fiber f b)))
  all-elements-equal-image-is-weakly-constant-map B f H (x , s) (y , t) = {!!}

abstract
  is-prop-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-weakly-constant-map f →
    is-prop (Σ (type-Set B) (λ b → type-trunc-Prop (fiber f b)))
  is-prop-image-is-weakly-constant-map B f H = {!!}

image-weakly-constant-map-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → Prop (l1 ⊔ l2)
pr1 (image-weakly-constant-map-Prop B f H) = {!!}
pr2 (image-weakly-constant-map-Prop B f H) = {!!}
```

### The universal property

```agda
map-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → type-trunc-Prop A → type-Set B
map-universal-property-set-quotient-trunc-Prop B f H = {!!}

map-universal-property-set-quotient-trunc-Prop' :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  Σ (A → type-Set B) is-weakly-constant-map → type-trunc-Prop A → type-Set B
map-universal-property-set-quotient-trunc-Prop' B (f , H) = {!!}

abstract
  htpy-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    (H : is-weakly-constant-map f) →
    map-universal-property-set-quotient-trunc-Prop B f H ∘ unit-trunc-Prop ~ f
  htpy-universal-property-set-quotient-trunc-Prop B f H a = {!!}

  is-section-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) →
    ( ( precomp-universal-property-set-quotient-trunc-Prop {A = A} B) ∘
      ( map-universal-property-set-quotient-trunc-Prop' B)) ~ id
  is-section-map-universal-property-set-quotient-trunc-Prop B (f , H) = {!!}

  is-retraction-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) →
    ( ( map-universal-property-set-quotient-trunc-Prop' B) ∘
      ( precomp-universal-property-set-quotient-trunc-Prop {A = A} B)) ~ id
  is-retraction-map-universal-property-set-quotient-trunc-Prop B g = {!!}

  universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) →
    is-equiv (precomp-universal-property-set-quotient-trunc-Prop {A = A} B)
  universal-property-set-quotient-trunc-Prop B = {!!}
```
