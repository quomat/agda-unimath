# Functoriality of suspensions

```agda
module synthetic-homotopy-theory.functoriality-suspensions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.universe-levels

open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

Any map `f : A → B` induces a map
`map-suspension f : suspension A → suspension B` on the
[suspensions](synthetic-homotopy-theory.suspensions-of-types.md) suspensions of
`A` and `B`.

Furthermore, this operation is functorial: it preserves identities and function
composition.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-suspension-structure : suspension-structure A (suspension B)
  map-suspension-structure = {!!}

  map-suspension : suspension A → suspension B
  map-suspension = {!!}

  compute-north-map-suspension :
    map-suspension (north-suspension) ＝ north-suspension
  compute-north-map-suspension = {!!}

  compute-south-map-suspension :
    map-suspension (south-suspension) ＝ south-suspension
  compute-south-map-suspension = {!!}

  compute-meridian-map-suspension :
    (a : A) →
    coherence-square-identifications
      ( compute-north-map-suspension)
      ( ap map-suspension (meridian-suspension a))
      ( meridian-suspension (f a))
      ( compute-south-map-suspension)
  compute-meridian-map-suspension = {!!}
```

## Properties

### The induced map on suspensions of the identity is the identity again

```agda
module _
  {l : Level} (A : UU l)
  where

  htpy-function-out-of-suspension-id-map-suspension :
    htpy-function-out-of-suspension A (map-suspension id) id
  htpy-function-out-of-suspension-id-map-suspension = {!!}

  id-map-suspension : map-suspension (id {A = A}) ~ id
  id-map-suspension = {!!}
```

### The induced map on suspensions of a composition is the composition of the induced maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → B) (g : B → C)
  where

  preserves-comp-map-suspension-north :
    (map-suspension g ∘ map-suspension f) north-suspension ＝
    map-suspension (g ∘ f) north-suspension
  preserves-comp-map-suspension-north = {!!}

  preserves-comp-map-suspension-south :
    (map-suspension g ∘ map-suspension f) south-suspension ＝
    map-suspension (g ∘ f) south-suspension
  preserves-comp-map-suspension-south = {!!}

  coherence-square-identifications-comp-map-suspension :
    (a : A) →
    coherence-square-identifications
      ( preserves-comp-map-suspension-north)
      ( ap (map-suspension g ∘ map-suspension f) (meridian-suspension a))
      ( ap (map-suspension (g ∘ f)) (meridian-suspension a))
      ( preserves-comp-map-suspension-south)
  coherence-square-identifications-comp-map-suspension = {!!}

  htpy-function-out-of-suspension-comp-map-suspension :
    htpy-function-out-of-suspension A
      ( map-suspension g ∘ map-suspension f)
      ( map-suspension (g ∘ f))
  htpy-function-out-of-suspension-comp-map-suspension = {!!}

  inv-preserves-comp-map-suspension :
    map-suspension g ∘ map-suspension f ~ map-suspension (g ∘ f)
  inv-preserves-comp-map-suspension = {!!}

  preserves-comp-map-suspension :
    map-suspension (g ∘ f) ~ map-suspension g ∘ map-suspension f
  preserves-comp-map-suspension = {!!}
```

### Suspensions preserve retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  section-map-suspension-section :
    (f : A → B) → section f → section (map-suspension f)
  section-map-suspension-section = {!!}

  retraction-map-suspension-retraction :
    (f : A → B) → retraction f → retraction (map-suspension f)
  retraction-map-suspension-retraction = {!!}

  retract-of-suspension-retract-of :
    A retract-of B → (suspension A) retract-of (suspension B)
  retract-of-suspension-retract-of = {!!}
```

### Equivalent types have equivalent suspensions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv-map-suspension-is-equiv :
    (f : A → B) → is-equiv f → is-equiv (map-suspension f)
  is-equiv-map-suspension-is-equiv = {!!}

  equiv-suspension : A ≃ B → suspension A ≃ suspension B
  equiv-suspension = {!!}
```
