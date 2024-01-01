# Factorizations of maps

```agda
module orthogonal-factorization-systems.factorizations-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies
```

</details>

## Idea

A **factorization** of a map `f : A → B` is a pair of maps `g : X → B` and
`h : A → X` such that their composite `g ∘ h` is `f`.

```text
       X
      ^ \
   h /   \ g
    /     v
  A -----> B
      f
```

We use diagrammatic order and say the map `h` is the _left_ and `g` the _right_
map of the factorization.

## Definitions

### The predicate on a triangle of maps of being a factorization

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-factorization :
    {l3 : Level} {X : UU l3} →
    (g : X → B) (h : A → X) → UU (l1 ⊔ l2)
  is-factorization g h = {!!}
```

### The type of factorizations of a map through a specified image/type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  factorization-through : (f : A → B) (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  factorization-through f X = {!!}

  right-map-factorization-through :
    {f : A → B} {X : UU l3} → factorization-through f X → X → B
  right-map-factorization-through = {!!}

  left-map-factorization-through :
    {f : A → B} {X : UU l3} → factorization-through f X → A → X
  left-map-factorization-through = {!!}

  is-factorization-factorization-through :
    {f : A → B} {X : UU l3}
    (F : factorization-through f X) →
      is-factorization f
        ( right-map-factorization-through F)
        ( left-map-factorization-through F)
  is-factorization-factorization-through = {!!}
```

### The type of factorizations of a map through images in a universe

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  factorization : (l3 : Level) (f : A → B) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  factorization l3 f = {!!}

  image-factorization : {l3 : Level} {f : A → B} → factorization l3 f → UU l3
  image-factorization = {!!}

  factorization-through-factorization :
    {l3 : Level} {f : A → B} (F : factorization l3 f) →
    factorization-through f (image-factorization F)
  factorization-through-factorization = {!!}

  right-map-factorization :
    {l3 : Level} {f : A → B} (F : factorization l3 f) →
    image-factorization F → B
  right-map-factorization F = {!!}

  left-map-factorization :
    {l3 : Level} {f : A → B} (F : factorization l3 f) →
    A → image-factorization F
  left-map-factorization F = {!!}

  is-factorization-factorization :
    {l3 : Level} {f : A → B} (F : factorization l3 f) →
    is-factorization f (right-map-factorization F) (left-map-factorization F)
  is-factorization-factorization F = {!!}
```

## Properties

### Whiskering of factorizations by retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  whisker-image-factorization-through :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} →
    X retract-of Y → factorization-through f X → factorization-through f Y
  pr1 (whisker-image-factorization-through (s , r , h) (fr , fl , fH)) = {!!}
```

### Characterization of identifications of factorizations through a type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  {X : UU l3}
  where

  coherence-htpy-factorization-through :
    (F E : factorization-through f X) →
    right-map-factorization-through F ~ right-map-factorization-through E →
    left-map-factorization-through F ~ left-map-factorization-through E →
    UU (l1 ⊔ l2)
  coherence-htpy-factorization-through F E R L = {!!}

  htpy-factorization-through :
    (F E : factorization-through f X) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-factorization-through F E = {!!}

  refl-htpy-factorization-through :
    (F : factorization-through f X) → htpy-factorization-through F F
  pr1 (refl-htpy-factorization-through F) = {!!}

  htpy-eq-factorization-through :
    (F E : factorization-through f X) →
    F ＝ E → htpy-factorization-through F E
  htpy-eq-factorization-through F .F refl = {!!}

  is-torsorial-htpy-factorization-through :
    (F : factorization-through f X) →
    is-torsorial (htpy-factorization-through F)
  is-torsorial-htpy-factorization-through F = {!!}

  is-equiv-htpy-eq-factorization-through :
    (F E : factorization-through f X) →
    is-equiv (htpy-eq-factorization-through F E)
  is-equiv-htpy-eq-factorization-through F = {!!}

  extensionality-factorization-through :
    (F E : factorization-through f X) →
    (F ＝ E) ≃ (htpy-factorization-through F E)
  pr1 (extensionality-factorization-through F E) = {!!}

  eq-htpy-factorization-through :
    (F E : factorization-through f X) →
    htpy-factorization-through F E → F ＝ E
  eq-htpy-factorization-through F E = {!!}
```

### Characterization of identifications of factorizations of a map in a universe level

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  equiv-factorization :
    (F E : factorization l3 f) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-factorization F E = {!!}

  id-equiv-factorization :
    (F : factorization l3 f) → equiv-factorization F F
  pr1 (id-equiv-factorization F) = {!!}

  equiv-eq-factorization :
    (F E : factorization l3 f) →
    F ＝ E → equiv-factorization F E
  equiv-eq-factorization F .F refl = {!!}

  is-torsorial-equiv-factorization :
    (F : factorization l3 f) →
    is-torsorial (equiv-factorization F)
  is-torsorial-equiv-factorization F = {!!}

  is-equiv-equiv-eq-factorization :
    (F E : factorization l3 f) → is-equiv (equiv-eq-factorization F E)
  is-equiv-equiv-eq-factorization F = {!!}

  extensionality-factorization :
    (F E : factorization l3 f) → (F ＝ E) ≃ (equiv-factorization F E)
  pr1 (extensionality-factorization F E) = {!!}

  eq-equiv-factorization :
    (F E : factorization l3 f) → equiv-factorization F E → F ＝ E
  eq-equiv-factorization F E = {!!}
```

## See also

- [Factorizations of maps into function classes](orthogonal-factorization-systems.factorizations-of-maps-function-classes.md)
