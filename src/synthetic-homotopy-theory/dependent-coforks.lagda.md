# Dependent coforks

```agda
module synthetic-homotopy-theory.dependent-coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.constant-type-families
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-spans
```

</details>

## Idea

Given a parallel pair `f, g : A → B`, a
[cofork](synthetic-homotopy-theory.coforks.md) `e : B → X` with vertex `X`, and
a type family `P : X → 𝓤` over `X`, we may construct _dependent_ coforks on `P`
over `e`.

A **dependent cofork** on `P` over `e` consists of a dependent map

```text
k : (b : B) → P (e b)
```

and a family of
[dependent identifications](foundation.dependent-identifications.md) indexed by
`A`

```text
(a : A) → dependent-identification P (H a) (k (f a)) (k (g a)).
```

Dependent coforks are an analogue of
[dependent cocones under spans](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
for parallel pairs.

## Definitions

### Dependent coforks

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) (P : X → UU l4)
  where

  dependent-cofork : UU (l1 ⊔ l2 ⊔ l4)
  dependent-cofork = {!!}

module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  { e : cofork f g X} (P : X → UU l4)
  ( k : dependent-cofork f g e P)
  where

  map-dependent-cofork : (b : B) → P (map-cofork f g e b)
  map-dependent-cofork = {!!}

  coherence-dependent-cofork :
    ( a : A) →
    dependent-identification P
      ( coherence-cofork f g e a)
      ( map-dependent-cofork (f a))
      ( map-dependent-cofork (g a))
  coherence-dependent-cofork = {!!}
```

### Homotopies of dependent coforks

A homotopy between dependent coforks is a homotopy between the underlying maps,
together with a coherence condition.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  { e : cofork f g X} (P : X → UU l4)
  where

  coherence-htpy-dependent-cofork :
    ( k k' : dependent-cofork f g e P) →
    ( K : map-dependent-cofork f g P k ~ map-dependent-cofork f g P k') →
    UU (l1 ⊔ l4)
  coherence-htpy-dependent-cofork = {!!}

  htpy-dependent-cofork :
    ( k k' : dependent-cofork f g e P) →
    UU (l1 ⊔ l2 ⊔ l4)
  htpy-dependent-cofork = {!!}
```

### Obtaining dependent coforks as postcomposition of coforks with dependent maps

One way to obtains dependent coforks is to postcompose the underlying cofork by
a dependent map, according to the diagram

```text
     g
   ----->     e              h
 A -----> B -----> (x : X) -----> (P x)
     f
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  dependent-cofork-map :
    { l : Level} {P : X → UU l} → ((x : X) → P x) → dependent-cofork f g e P
  dependent-cofork-map = {!!}
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  { e : cofork f g X} (P : X → UU l4)
  where

  reflexive-htpy-dependent-cofork :
    ( k : dependent-cofork f g e P) →
    htpy-dependent-cofork f g P k k
  reflexive-htpy-dependent-cofork = {!!}

  htpy-dependent-cofork-eq :
    ( k k' : dependent-cofork f g e P) →
    ( k ＝ k') → htpy-dependent-cofork f g P k k'
  htpy-dependent-cofork-eq = {!!}

  abstract
    is-torsorial-htpy-dependent-cofork :
      ( k : dependent-cofork f g e P) →
      is-torsorial (htpy-dependent-cofork f g P k)
    is-torsorial-htpy-dependent-cofork = {!!}

    is-equiv-htpy-dependent-cofork-eq :
      ( k k' : dependent-cofork f g e P) →
      is-equiv (htpy-dependent-cofork-eq k k')
    is-equiv-htpy-dependent-cofork-eq = {!!}

  eq-htpy-dependent-cofork :
    ( k k' : dependent-cofork f g e P) →
    htpy-dependent-cofork f g P k k' → k ＝ k'
  eq-htpy-dependent-cofork = {!!}
```

### Dependent coforks on constant type families are equivalent to regular coforks

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) (Y : UU l4)
  where

  compute-dependent-cofork-constant-family :
    dependent-cofork f g e (λ _ → Y) ≃ cofork f g Y
  compute-dependent-cofork-constant-family = {!!}

  map-compute-dependent-cofork-constant-family :
    dependent-cofork f g e (λ _ → Y) → cofork f g Y
  map-compute-dependent-cofork-constant-family = {!!}

  triangle-compute-dependent-cofork-constant-family :
    coherence-triangle-maps
      ( cofork-map f g e)
      ( map-compute-dependent-cofork-constant-family)
      ( dependent-cofork-map f g e)
  triangle-compute-dependent-cofork-constant-family = {!!}
```

### Dependent coforks are special cases of dependent cocones under spans

The type of dependent coforks on `P` over `e` is equivalent to the type of
[dependent cocones](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
on `P` over a cocone corresponding to `e` via `cocone-codiagonal-cofork`.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  module _
    { l4 : Level} (P : X → UU l4)
    where

    dependent-cofork-dependent-cocone-codiagonal :
      dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P) →
      dependent-cofork f g e P
    dependent-cofork-dependent-cocone-codiagonal = {!!}
    pr2 (dependent-cofork-dependent-cocone-codiagonal k) a = {!!}

    dependent-cocone-codiagonal-dependent-cofork :
      dependent-cofork f g e P →
      dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P)
    dependent-cocone-codiagonal-dependent-cofork = {!!}
    pr1 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) = {!!}
    pr2 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) (inl a) = {!!}
    pr2 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) (inr a) = {!!}

    abstract
      is-section-dependent-cocone-codiagonal-dependent-cofork :
        ( ( dependent-cofork-dependent-cocone-codiagonal) ∘
          ( dependent-cocone-codiagonal-dependent-cofork)) ~
        ( id)
      is-section-dependent-cocone-codiagonal-dependent-cofork = {!!}

      is-retraction-dependent-cocone-codiagonal-dependent-cofork :
        ( ( dependent-cocone-codiagonal-dependent-cofork) ∘
          ( dependent-cofork-dependent-cocone-codiagonal)) ~
        ( id)
      is-retraction-dependent-cocone-codiagonal-dependent-cofork = {!!}

    is-equiv-dependent-cofork-dependent-cocone-codiagonal :
      is-equiv dependent-cofork-dependent-cocone-codiagonal
    is-equiv-dependent-cofork-dependent-cocone-codiagonal = {!!}

    equiv-dependent-cofork-dependent-cocone-codiagonal :
      dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P) ≃
      dependent-cofork f g e P
    equiv-dependent-cofork-dependent-cocone-codiagonal = {!!}
    pr2 equiv-dependent-cofork-dependent-cocone-codiagonal = {!!}

  triangle-dependent-cofork-dependent-cocone-codiagonal :
    { l4 : Level} (P : X → UU l4) →
    coherence-triangle-maps
      ( dependent-cofork-map f g e)
      ( dependent-cofork-dependent-cocone-codiagonal P)
      ( dependent-cocone-map
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P))
  triangle-dependent-cofork-dependent-cocone-codiagonal = {!!}
```
