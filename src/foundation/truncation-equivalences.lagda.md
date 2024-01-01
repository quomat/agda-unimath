# `k`-Equivalences

```agda
module foundation.truncation-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.precomposition-functions-into-subuniverses
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.surjective-maps
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-truncation
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.precomposition-functions
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A map `f : A → B` is said to be a `k`-equivalence if the map
`map-trunc k f : trunc k A → trunc k B` is an equivalence.

## Definition

```agda
is-truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-truncation-equivalence = {!!}

truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
truncation-equivalence = {!!}

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  (f : truncation-equivalence k A B)
  where

  map-truncation-equivalence : A → B
  map-truncation-equivalence = {!!}

  is-truncation-equivalence-truncation-equivalence :
    is-truncation-equivalence k map-truncation-equivalence
  is-truncation-equivalence-truncation-equivalence = {!!}
```

## Properties

### A map `f : A → B` is a `k`-equivalence if and only if `- ∘ f : (B → X) → (A → X)` is an equivalence for every `k`-truncated type `X`

```agda
is-equiv-precomp-is-truncation-equivalence :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  (X : Truncated-Type l3 k) → is-equiv (precomp f (type-Truncated-Type X))
is-equiv-precomp-is-truncation-equivalence = {!!}

is-truncation-equivalence-is-equiv-precomp :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  ( (l : Level) (X : Truncated-Type l k) →
    is-equiv (precomp f (type-Truncated-Type X))) →
  is-truncation-equivalence k f
is-truncation-equivalence-is-equiv-precomp = {!!}
```

### An equivalence is a `k`-equivalence for all `k`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-is-equiv :
    is-equiv f → is-truncation-equivalence k f
  is-truncation-equivalence-is-equiv = {!!}
```

### Every `k`-connected map is a `k`-equivalence

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-is-connected-map :
    is-connected-map k f → is-truncation-equivalence k f
  is-truncation-equivalence-is-connected-map = {!!}
```

### The `k`-equivalences are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-truncation-equivalence-comp :
    (g : B → C) (f : A → B) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k g →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-comp = {!!}

  truncation-equivalence-comp :
    truncation-equivalence k B C →
    truncation-equivalence k A B →
    truncation-equivalence k A C
  truncation-equivalence-comp = {!!}
```

### The class of `k`-equivalences has the 3-for-2 property

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (e : is-truncation-equivalence k (g ∘ f))
  where

  is-truncation-equivalence-left-factor :
    is-truncation-equivalence k f → is-truncation-equivalence k g
  is-truncation-equivalence-left-factor = {!!}

  is-truncation-equivalence-right-factor :
    is-truncation-equivalence k g → is-truncation-equivalence k f
  is-truncation-equivalence-right-factor = {!!}
```

### Composing `k`-equivalences with equivalences

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-truncation-equivalence-is-equiv-is-truncation-equivalence :
    (g : B → C) (f : A → B) →
    is-truncation-equivalence k g →
    is-equiv f →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-is-equiv-is-truncation-equivalence = {!!}

  is-truncation-equivalence-is-truncation-equivalence-is-equiv :
    (g : B → C) (f : A → B) →
    is-equiv g →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-is-truncation-equivalence-is-equiv = {!!}

  is-truncation-equivalence-equiv-is-truncation-equivalence :
    (g : B → C) (f : A ≃ B) →
    is-truncation-equivalence k g →
    is-truncation-equivalence k (g ∘ map-equiv f)
  is-truncation-equivalence-equiv-is-truncation-equivalence = {!!}

  is-truncation-equivalence-is-truncation-equivalence-equiv :
    (g : B ≃ C) (f : A → B) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (map-equiv g ∘ f)
  is-truncation-equivalence-is-truncation-equivalence-equiv = {!!}
```

### The map on dependent pair types induced by the unit of the `(k+1)`-truncation is a `k`-equivalence

This is an instance of Lemma 2.27 in Christensen, Opie, Rijke & Scoccola
\[CORS'20\] listed below.

```agda
module _
  {l1 l2 : Level} {k : 𝕋}
  {X : UU l1} (P : (type-trunc (succ-𝕋 k) X) → UU l2)
  where

  map-Σ-map-base-unit-trunc :
    Σ X (P ∘ unit-trunc) → Σ (type-trunc (succ-𝕋 k) X) P
  map-Σ-map-base-unit-trunc = {!!}

  is-truncation-equivalence-map-Σ-map-base-unit-trunc :
    is-truncation-equivalence k map-Σ-map-base-unit-trunc
  is-truncation-equivalence-map-Σ-map-base-unit-trunc = {!!}
```

### There is an `k`-equivalence between the fiber of a map and the fiber of its `(k+1)`-truncation

This is an instance of Corollary 2.29 in \[CORS'20\].

We consider the following composition of maps

```text
   fiber f b = {!!}
```

where the first and last maps are `k`-equivalences.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber-map-trunc-fiber :
    fiber f b → fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b)
  fiber-map-trunc-fiber = {!!}

  is-truncation-equivalence-fiber-map-trunc-fiber :
    is-truncation-equivalence k fiber-map-trunc-fiber
  is-truncation-equivalence-fiber-map-trunc-fiber = {!!}

  truncation-equivalence-fiber-map-trunc-fiber :
    truncation-equivalence k
      ( fiber f b)
      ( fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b))
  truncation-equivalence-fiber-map-trunc-fiber = {!!}
```

### Being `k`-connected is invariant under `k`-equivalences

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-is-truncation-equivalence-is-connected :
    (f : A → B) → is-truncation-equivalence k f →
    is-connected k B → is-connected k A
  is-connected-is-truncation-equivalence-is-connected = {!!}

  is-connected-truncation-equivalence-is-connected :
    truncation-equivalence k A B → is-connected k B → is-connected k A
  is-connected-truncation-equivalence-is-connected = {!!}
```

### Every `(k+1)`-equivalence is `k`-connected

This is an instance of Proposition 2.30 in \[CORS'20\].

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-is-succ-truncation-equivalence :
    is-truncation-equivalence (succ-𝕋 k) f → is-connected-map k f
  is-connected-map-is-succ-truncation-equivalence = {!!}
```

### The codomain of a `k`-connected map is `(k+1)`-connected if its domain is `(k+1)`-connected

This follows part of the proof of Proposition 2.31 in \[CORS'20\].

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-trunc-fiber-map-trunc-is-succ-connected :
    is-connected (succ-𝕋 k) A →
    (b : B) →
    is-trunc k (fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b))
  is-trunc-fiber-map-trunc-is-succ-connected = {!!}

  is-succ-connected-is-connected-map-is-succ-connected :
    is-connected (succ-𝕋 k) A →
    is-connected-map k f →
    is-connected (succ-𝕋 k) B
  is-succ-connected-is-connected-map-is-succ-connected = {!!}
```

### If `g ∘ f` is `(k+1)`-connected, then `f` is `k`-connected if and only if `g` is `(k+1)`-connected

This is an instance of Proposition 2.31 in \[CORS'20\].

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (cgf : is-connected-map (succ-𝕋 k) (g ∘ f))
  where

  is-connected-map-right-factor-is-succ-connected-map-left-factor :
    is-connected-map (succ-𝕋 k) g → is-connected-map k f
  is-connected-map-right-factor-is-succ-connected-map-left-factor = {!!}

  is-connected-map-right-factor-is-succ-connected-map-right-factor :
    is-connected-map k f → is-connected-map (succ-𝕋 k) g
  is-connected-map-right-factor-is-succ-connected-map-right-factor = {!!}
```

### A `k`-equivalence with a section is `k`-connected

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-is-truncation-equivalence-section :
    (k : 𝕋) →
    section f → is-truncation-equivalence k f → is-connected-map k f
  is-connected-map-is-truncation-equivalence-section = {!!}
```

## References

The notion of `k`-equivalence is a special case of the notion of
`L`-equivalence, where `L` is a reflective subuniverse. They were studied in the
paper

- \[CORS'20\]: J. D. Christensen, M. Opie, E. Rijke, and L. Scoccola.
  Localization in Homotopy Type Theory. Higher Structures, 2020.

The class of `k`-equivalences is left orthogonal to the class of `k`-étale maps.
This was shown in

- \[CR'21\]: F. Cherubini, and E. Rijke. Modal descent. Mathematical Structures
  in Computer Science, 2021.
