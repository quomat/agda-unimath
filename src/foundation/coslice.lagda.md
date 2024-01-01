# Morphisms in the coslice category of types

```agda
module foundation.coslice where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a span of maps

```text
      X
     / \
  f /   \ g
   v     v
  A       B,
```

we define a morphism between the maps in the coslice category of types to be a
map `h : A → B` together with a coherence triangle `(h ∘ f) ~ g`:

```text
      X
     / \
  f /   \ g
   v     v
  A ----> B.
      h
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : X → A) (g : X → B)
  where

  hom-coslice = {!!}

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {f : X → A} {g : X → B}
  where

  map-hom-coslice : hom-coslice f g → A → B
  map-hom-coslice = {!!}

  triangle-hom-coslice :
    (h : hom-coslice f g) → map-hom-coslice h ∘ f ~ g
  triangle-hom-coslice = {!!}
```

## Properties

### Characterizing the identity type of coslice morphisms

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {f : X → A} {g : X → B}
  where

  coherence-htpy-hom-coslice :
    (h k : hom-coslice f g) →
    map-hom-coslice h ~ map-hom-coslice k → UU (l1 ⊔ l3)
  coherence-htpy-hom-coslice = {!!}

  htpy-hom-coslice :
    (h k : hom-coslice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-coslice = {!!}

  extensionality-hom-coslice :
    (h k : hom-coslice f g) → (h ＝ k) ≃ htpy-hom-coslice h k
  extensionality-hom-coslice = {!!}

  eq-htpy-hom-coslice :
    ( h k : hom-coslice f g)
    ( H : map-hom-coslice h ~ map-hom-coslice k)
    ( K : coherence-htpy-hom-coslice h k H) →
    h ＝ k
  eq-htpy-hom-coslice = {!!}
```
