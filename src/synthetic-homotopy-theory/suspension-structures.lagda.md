# Suspension Structures

```agda
module synthetic-homotopy-theory.suspension-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

The suspension of `X` is the [pushout](synthetic-homotopy-theory.pushouts.md) of
the span `unit <-- X --> unit`. A
[cocone under such a span](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
is called a `suspension-cocone`. Explicitly, a suspension cocone with nadir `Y`
consists of functions

```text
f : unit → Y
g : unit → Y
```

and a homotopy

```text
h : (x : X) → (f ∘ (const X unit star)) x ＝ (g ∘ (const X unit star)) x
```

Using the
[universal property of the unit type](foundation.universal-property-unit-type.md),
we can characterize suspension cocones as equivalent to a selection of "north"
and "south" poles

```text
north , south : Y
```

and a meridian function

```text
meridian : X → north ＝ south
```

We call this type of structure `suspension-structure`.

## Definition

### Suspension cocones on a type

```agda
suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone = {!!}
```

### Suspension structures on a type

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  where

  suspension-structure : UU (l1 ⊔ l2)
  suspension-structure = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  north-suspension-structure : suspension-structure X Y → Y
  north-suspension-structure = {!!}

  south-suspension-structure : suspension-structure X Y → Y
  south-suspension-structure = {!!}

  meridian-suspension-structure :
    (c : suspension-structure X Y) →
    X → north-suspension-structure c ＝ south-suspension-structure c
  meridian-suspension-structure = {!!}
```

## Properties

### Equivalence between suspension structures and suspension cocones

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  suspension-cocone-suspension-structure :
    suspension-structure X Y → suspension-cocone X Y
  suspension-cocone-suspension-structure = {!!}

  suspension-structure-suspension-cocone :
    suspension-cocone X Y → suspension-structure X Y
  suspension-structure-suspension-cocone = {!!}

  is-equiv-suspension-cocone-suspension-structure :
    is-equiv suspension-cocone-suspension-structure
  is-equiv-suspension-cocone-suspension-structure = {!!}

  is-equiv-suspension-structure-suspension-cocone :
    is-equiv suspension-structure-suspension-cocone
  is-equiv-suspension-structure-suspension-cocone = {!!}

  equiv-suspension-structure-suspension-cocone :
    suspension-structure X Y ≃ suspension-cocone X Y
  equiv-suspension-structure-suspension-cocone = {!!}

  equiv-suspension-cocone-suspension-structure :
    suspension-cocone X Y ≃ suspension-structure X Y
  equiv-suspension-cocone-suspension-structure = {!!}
```

#### Characterization of equalities in `suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  htpy-suspension-structure :
    (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
  htpy-suspension-structure = {!!}

  north-htpy-suspension-structure :
    {c c' : suspension-structure X Z} →
    htpy-suspension-structure c c' →
    north-suspension-structure c ＝ north-suspension-structure c'
  north-htpy-suspension-structure = {!!}

  south-htpy-suspension-structure :
    {c c' : suspension-structure X Z} →
    htpy-suspension-structure c c' →
    south-suspension-structure c ＝ south-suspension-structure c'
  south-htpy-suspension-structure = {!!}

  meridian-htpy-suspension-structure :
    {c c' : suspension-structure X Z} →
    (h : htpy-suspension-structure c c') →
    ( x : X) →
    coherence-square-identifications
      ( north-htpy-suspension-structure h)
      ( meridian-suspension-structure c x)
      ( meridian-suspension-structure c' x)
      ( south-htpy-suspension-structure h)
  meridian-htpy-suspension-structure = {!!}

  extensionality-suspension-structure :
    (c c' : suspension-structure X Z) →
    (c ＝ c') ≃ (htpy-suspension-structure c c')
  extensionality-suspension-structure = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c c' : suspension-structure X Z}
  where

  htpy-eq-suspension-structure : (c ＝ c') → htpy-suspension-structure c c'
  htpy-eq-suspension-structure = {!!}

  eq-htpy-suspension-structure : htpy-suspension-structure c c' → (c ＝ c')
  eq-htpy-suspension-structure = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  refl-htpy-suspension-structure : htpy-suspension-structure c c
  refl-htpy-suspension-structure = {!!}

  is-refl-refl-htpy-suspension-structure :
    refl-htpy-suspension-structure ＝ htpy-eq-suspension-structure refl
  is-refl-refl-htpy-suspension-structure = {!!}

  extensionality-suspension-structure-refl-htpy-suspension-structure :
    eq-htpy-suspension-structure refl-htpy-suspension-structure ＝ refl
  extensionality-suspension-structure-refl-htpy-suspension-structure = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  ind-htpy-suspension-structure :
    { l : Level}
    ( P :
      (c' : suspension-structure X Z) → htpy-suspension-structure c c' → UU l) →
    ( P c refl-htpy-suspension-structure) →
    ( c' : suspension-structure X Z)
    ( H : htpy-suspension-structure c c') →
    P c' H
  ind-htpy-suspension-structure = {!!}
```

#### The action of paths of the projections have the expected effect

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c : suspension-structure X Z)
  where

  ap-pr1-eq-htpy-suspension-structure :
    (c' : suspension-structure X Z) (H : htpy-suspension-structure c c') →
    (ap (pr1) (eq-htpy-suspension-structure H)) ＝ (pr1 H)
  ap-pr1-eq-htpy-suspension-structure = {!!}

  ap-pr1∘pr2-eq-htpy-suspension-structure :
    (c' : suspension-structure X Z) (H : htpy-suspension-structure c c') →
    (ap (pr1 ∘ pr2) (eq-htpy-suspension-structure H)) ＝ ((pr1 ∘ pr2) H)
  ap-pr1∘pr2-eq-htpy-suspension-structure = {!!}
```

### Characterization of equalities in `htpy-suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  {c c' : suspension-structure X Z}
  where

  htpy-in-htpy-suspension-structure :
    htpy-suspension-structure c c' →
    htpy-suspension-structure c c' → UU (l1 ⊔ l2)
  htpy-in-htpy-suspension-structure = {!!}

  extensionality-htpy-suspension-structure :
    (h h' : htpy-suspension-structure c c') →
      (h ＝ h') ≃ htpy-in-htpy-suspension-structure h h'
  extensionality-htpy-suspension-structure = {!!}

  north-htpy-in-htpy-suspension-structure :
    {h h' : htpy-suspension-structure c c'} →
    htpy-in-htpy-suspension-structure h h' →
    ( north-htpy-suspension-structure h) ＝
    ( north-htpy-suspension-structure h')
  north-htpy-in-htpy-suspension-structure = {!!}

  south-htpy-in-htpy-suspension-structure :
    {h h' : htpy-suspension-structure c c'} →
    htpy-in-htpy-suspension-structure h h' →
    ( south-htpy-suspension-structure h) ＝
    ( south-htpy-suspension-structure h')
  south-htpy-in-htpy-suspension-structure = {!!}

  meridian-htpy-in-htpy-suspension-structure :
    {h h' : htpy-suspension-structure c c'} →
    (H : htpy-in-htpy-suspension-structure h h') →
    (x : X) →
      coherence-square-identifications
        ( meridian-htpy-suspension-structure h x)
        ( identification-left-whisk
          ( meridian-suspension-structure c x)
          ( south-htpy-in-htpy-suspension-structure H))
        ( identification-right-whisk
          ( north-htpy-in-htpy-suspension-structure H)
          ( meridian-suspension-structure c' x))
        ( meridian-htpy-suspension-structure h' x)
  meridian-htpy-in-htpy-suspension-structure = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  {c c' : suspension-structure X Z} {h h' : htpy-suspension-structure c c'}
  where

  htpy-eq-htpy-suspension-structure :
    h ＝ h' → htpy-in-htpy-suspension-structure h h'
  htpy-eq-htpy-suspension-structure = {!!}

  eq-htpy-in-htpy-suspension-structure :
    htpy-in-htpy-suspension-structure h h' → h ＝ h'
  eq-htpy-in-htpy-suspension-structure = {!!}
```
