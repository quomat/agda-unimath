# Epimorphisms with respect to truncated types

```agda
module foundation.epimorphisms-with-respect-to-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.functoriality-function-types
open import foundation.functoriality-truncation
open import foundation.precomposition-functions
open import foundation.sections
open import foundation.truncation-equivalences
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be a **`k`-epimorphism** if the precomposition
function

```text
  - ∘ f : (B → X) → (A → X)
```

is an embedding for every `k`-truncated type `X`.

## Definitions

### `k`-epimorphisms

```agda
is-epimorphism-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (A → B) → UUω
is-epimorphism-Truncated-Type = {!!}
```

## Properties

### Every `k+1`-epimorphism is a `k`-epimorphism

```agda
is-epimorphism-is-epimorphism-succ-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-epimorphism-Truncated-Type (succ-𝕋 k) f →
  is-epimorphism-Truncated-Type k f
is-epimorphism-is-epimorphism-succ-Truncated-Type = {!!}
```

### Every map is a `-1`-epimorphism

```agda
is-neg-one-epimorphism :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-epimorphism-Truncated-Type neg-one-𝕋 f
is-neg-one-epimorphism = {!!}
```

### Every `k`-equivalence is a `k`-epimorphism

```agda
is-epimorphism-is-truncation-equivalence-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  is-epimorphism-Truncated-Type k f
is-epimorphism-is-truncation-equivalence-Truncated-Type = {!!}
```

### A map is a `k`-epimorphism if and only if its `k`-truncation is a `k`-epimorphism

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-epimorphism-map-trunc-Truncated-Type :
    is-epimorphism-Truncated-Type k (map-trunc k f) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-epimorphism-map-trunc-Truncated-Type = {!!}

  is-epimorphism-map-trunc-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k (map-trunc k f)
  is-epimorphism-map-trunc-is-epimorphism-Truncated-Type = {!!}
```

### The class of `k`-epimorphisms is closed under composition and has the right cancellation property

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-epimorphism-comp-Truncated-Type :
    is-epimorphism-Truncated-Type k g →
    is-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k (g ∘ f)
  is-epimorphism-comp-Truncated-Type = {!!}

  is-epimorphism-left-factor-Truncated-Type :
    is-epimorphism-Truncated-Type k (g ∘ f) →
    is-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k g
  is-epimorphism-left-factor-Truncated-Type = {!!}
```

### A map `f` is a `k`-epimorphism if and only if the horizontal/vertical projections from `cocone {X} f f` are equivalences for all `k`-types `X`

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (diagonal-into-fibers-precomp f (type-Truncated-Type X))
  is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Type = {!!}

  is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (diagonal-into-cocone f (type-Truncated-Type X))
  is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Type = {!!}

  is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (horizontal-map-cocone {X = type-Truncated-Type X} f f)
  is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Type = {!!}

  is-equiv-vertical-map-cocone-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (vertical-map-cocone {X = type-Truncated-Type X} f f)
  is-equiv-vertical-map-cocone-is-epimorphism-Truncated-Type = {!!}

  is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Type :
    ( {l : Level} (X : Truncated-Type l k) →
      is-equiv (horizontal-map-cocone {X = type-Truncated-Type X} f f)) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Type = {!!}

  is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Type :
    ( {l : Level} (X : Truncated-Type l k) →
      is-equiv (vertical-map-cocone {X = type-Truncated-Type X} f f)) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Type = {!!}
```

### The codiagonal of a `k`-epimorphism is a `k`-equivalence

We consider the commutative diagram for any `k`-type `X`:

```text
             horizontal-map-cocone
 (B → X) <---------------------------- cocone f f X
    |                  ≃                  ^
 id | ≃                                 ≃ | (universal property)
    v                                     |
 (B → X) ------------------------> (pushout f f → X)
          precomp (codiagonal f)
```

Since the top (in case `f` is epic), left and right maps are all equivalences,
so is the bottom map.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-truncation-equivalence k (codiagonal-map f)
  is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Type = {!!}
```

### A map is a `k`-epimorphism if its codiagonal is a `k`-equivalence

We use the same diagram as above.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-map :
    is-truncation-equivalence k (codiagonal-map f) →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (horizontal-map-cocone {X = type-Truncated-Type X} f f)
  is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-map = {!!}

  is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Type :
    is-truncation-equivalence k (codiagonal-map f) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Type = {!!}
```

### A map is a `k`-epimorphism if and only if its codiagonal is `k`-connected

This strengthens the above result about the codiagonal being a `k`-equivalence.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-connected-codiagonal-map-Truncated-Type :
    is-connected-map k (codiagonal-map f) → is-epimorphism-Truncated-Type k f
  is-epimorphism-is-connected-codiagonal-map-Truncated-Type = {!!}

  is-connected-codiagonal-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f → is-connected-map k (codiagonal-map f)
  is-connected-codiagonal-map-is-epimorphism-Truncated-Type = {!!}
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
