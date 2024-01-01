# Dependent cocones under spans

```agda
module synthetic-homotopy-theory.dependent-cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

Consider a span `𝒮 := {!!}
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) `c` of `𝒮`
into a type `X`. Furthermore, consider a type family `P` over `X`. In this case
we may consider _dependent_ cocone structures on `P` over `c`.

A **dependent cocone** `d` over `(i , j , H)` on `P` consists of two dependent
functions

```text
  i' : (a : A) → P (i a)
  j' : (b : B) → P (j b)
```

and a family of
[dependent identifications](foundation.dependent-identifications.md)

```text
  (s : S) → dependent-identification P (H s) (i' (f s)) (j' (g s)).
```

## Definitions

### Dependent cocones

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5)
  where

  dependent-cocone : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  dependent-cocone = {!!}

  module _
    (d : dependent-cocone)
    where

    horizontal-map-dependent-cocone :
      (a : A) → P (horizontal-map-cocone f g c a)
    horizontal-map-dependent-cocone = {!!}

    vertical-map-dependent-cocone :
      (b : B) → P (vertical-map-cocone f g c b)
    vertical-map-dependent-cocone = {!!}

    coherence-square-dependent-cocone :
      (s : S) →
      dependent-identification P
        ( coherence-square-cocone f g c s)
        ( horizontal-map-dependent-cocone (f s))
        ( vertical-map-dependent-cocone (g s))
    coherence-square-dependent-cocone = {!!}
```

### Postcomposing dependent cocones with maps

```agda
dependent-cocone-map :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5) →
  ( (x : X) → P x) → dependent-cocone f g c P
dependent-cocone-map = {!!}
```

## Properties

### Characterization of identifications of dependent cocones

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} (c : cocone f g X)
  (P : X → UU l5) (d : dependent-cocone f g c P)
  where

  coherence-htpy-dependent-cocone :
    ( d' : dependent-cocone f g c P)
    ( K :
      horizontal-map-dependent-cocone f g c P d ~
      horizontal-map-dependent-cocone f g c P d')
    ( L :
      vertical-map-dependent-cocone f g c P d ~
      vertical-map-dependent-cocone f g c P d') →
    UU (l1 ⊔ l5)
  coherence-htpy-dependent-cocone = {!!}

  htpy-dependent-cocone :
    (d' : dependent-cocone f g c P) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  htpy-dependent-cocone = {!!}

  refl-htpy-dependent-cocone :
    htpy-dependent-cocone d
  refl-htpy-dependent-cocone = {!!}

  htpy-eq-dependent-cocone :
    (d' : dependent-cocone f g c P) → d ＝ d' → htpy-dependent-cocone d'
  htpy-eq-dependent-cocone = {!!}

  module _
    (d' : dependent-cocone f g c P)
    (p : d ＝ d')
    where

    horizontal-htpy-eq-dependent-cocone :
      horizontal-map-dependent-cocone f g c P d ~
      horizontal-map-dependent-cocone f g c P d'
    horizontal-htpy-eq-dependent-cocone = {!!}

    vertical-htpy-eq-dependent-cocone :
      vertical-map-dependent-cocone f g c P d ~
      vertical-map-dependent-cocone f g c P d'
    vertical-htpy-eq-dependent-cocone = {!!}

    coherence-square-htpy-eq-dependent-cocone :
      coherence-htpy-dependent-cocone d'
        ( horizontal-htpy-eq-dependent-cocone)
        ( vertical-htpy-eq-dependent-cocone)
    coherence-square-htpy-eq-dependent-cocone = {!!}

  abstract
    is-torsorial-htpy-dependent-cocone :
      is-torsorial htpy-dependent-cocone
    is-torsorial-htpy-dependent-cocone = {!!}

  abstract
    is-equiv-htpy-eq-dependent-cocone :
      (d' : dependent-cocone f g c P) → is-equiv (htpy-eq-dependent-cocone d')
    is-equiv-htpy-eq-dependent-cocone = {!!}

    eq-htpy-dependent-cocone :
      (d' : dependent-cocone f g c P) → htpy-dependent-cocone d' → d ＝ d'
    eq-htpy-dependent-cocone = {!!}

    is-section-eq-htpy-dependent-cocone :
      (d' : dependent-cocone f g c P) →
      ( htpy-eq-dependent-cocone d' ∘ eq-htpy-dependent-cocone d') ~ id
    is-section-eq-htpy-dependent-cocone = {!!}

    is-retraction-eq-htpy-dependent-cocone :
      (d' : dependent-cocone f g c P) →
      ( eq-htpy-dependent-cocone d' ∘ htpy-eq-dependent-cocone d') ~ id
    is-retraction-eq-htpy-dependent-cocone = {!!}
```
