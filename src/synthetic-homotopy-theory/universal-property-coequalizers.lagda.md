# The universal property of coequalizers

```agda
module synthetic-homotopy-theory.universal-property-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Given a parallel pair `f, g : A → B`, consider a
[cofork](synthetic-homotopy-theory.coforks.md) `e : B → X` with vertex X. The
**universal property of coequalizers** is the statement that the cofork
postcomposition map

```text
cofork-map : (X → Y) → cofork Y
```

is an equivalence.

## Definitions

### The universal property of coequalizers

```agda
module _
  { l1 l2 l3 : Level} (l : Level) {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} (e : cofork f g X)
  where

  universal-property-coequalizer : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  universal-property-coequalizer = {!!}

module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) {Y : UU l4}
  ( up-coequalizer : universal-property-coequalizer l4 f g e)
  where

  map-universal-property-coequalizer : cofork f g Y → (X → Y)
  map-universal-property-coequalizer = {!!}
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) {Y : UU l4}
  ( up-coequalizer : universal-property-coequalizer l4 f g e)
  ( e' : cofork f g Y)
  where

  htpy-cofork-map-universal-property-coequalizer :
    htpy-cofork f g
      ( cofork-map f g e
        ( map-universal-property-coequalizer f g e up-coequalizer e'))
      ( e')
  htpy-cofork-map-universal-property-coequalizer = {!!}

  abstract
    uniqueness-map-universal-property-coequalizer :
      is-contr (Σ (X → Y) (λ h → htpy-cofork f g (cofork-map f g e h) e'))
    uniqueness-map-universal-property-coequalizer = {!!}
```

### A cofork has the universal property of coequalizers if and only if the corresponding cocone has the universal property of pushouts

As mentioned in [coforks](synthetic-homotopy-theory.coforks.md), coforks can be
thought of as special cases of cocones under spans. This theorem makes it more
precise, asserting that under this mapping,
[coequalizers](synthetic-homotopy-theory.coequalizers.md) correspond to
[pushouts](synthetic-homotopy-theory.pushouts.md).

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f g : A → B)
  ( e : cofork f g X)
  where

  universal-property-coequalizer-universal-property-pushout :
    ( {l : Level} →
      universal-property-pushout l
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)) →
    ( {l : Level} →
      universal-property-coequalizer l f g e)
  universal-property-coequalizer-universal-property-pushout = {!!}

  universal-property-pushout-universal-property-coequalizer :
    ( {l : Level} →
      universal-property-coequalizer l f g e) →
    ( {l : Level} →
      universal-property-pushout l
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e))
  universal-property-pushout-universal-property-coequalizer = {!!}
```
