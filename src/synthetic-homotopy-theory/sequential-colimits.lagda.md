# Sequential colimits

```agda
module synthetic-homotopy-theory.sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.propositions
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coequalizers
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, we can construct its **standard sequential colimit** `A∞`, which is a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
satisfying the
[universal property of sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

In other words, the sequential colimit universally completes the diagram

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ ---> A∞ .
```

We often abuse notation and write `A∞` for just the codomain of the universal
cocone. You may also see the colimit written as `colimₙ Aₙ`.

## Properties

### All sequential diagrams admit a standard colimit

The standard colimit may be constructed from
[coequalizers](synthetic-homotopy-theory.coequalizers.md), because we
[have shown](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
that cocones of sequential diagrams correspond to a certain class of
[coforks](synthetic-homotopy-theory.coforks.md), and the coequalizers correspond
to sequential colimits. Since all coequalizers exist, we conclude that all
sequential colimits exist.

```agda
abstract
  standard-sequential-colimit : {l : Level} (A : sequential-diagram l) → UU l
  standard-sequential-colimit A = {!!}

  cocone-standard-sequential-colimit :
    { l : Level} (A : sequential-diagram l) →
    cocone-sequential-diagram A (standard-sequential-colimit A)
  cocone-standard-sequential-colimit = {!!}

  dup-standard-sequential-colimit :
    { l : Level} {A : sequential-diagram l} →
    dependent-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
  dup-standard-sequential-colimit = {!!}

  up-standard-sequential-colimit :
    { l : Level} {A : sequential-diagram l} →
    universal-property-sequential-colimit A
      (cocone-standard-sequential-colimit A)
  up-standard-sequential-colimit = {!!}

module _
  { l : Level} {A : sequential-diagram l}
  where

  map-cocone-standard-sequential-colimit :
    ( n : ℕ) → family-sequential-diagram A n → standard-sequential-colimit A
  map-cocone-standard-sequential-colimit = {!!}

  coherence-triangle-cocone-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-triangle-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram A n)
  coherence-triangle-cocone-standard-sequential-colimit = {!!}
```

### Corollaries of the universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1}
  where

  equiv-up-standard-sequential-colimit :
    { X : UU l2} →
    (standard-sequential-colimit A → X) ≃ (cocone-sequential-diagram A X)
  equiv-up-standard-sequential-colimit = {!!}

  cogap-standard-sequential-colimit :
    { X : UU l2} →
    cocone-sequential-diagram A X → standard-sequential-colimit A → X
  cogap-standard-sequential-colimit = {!!}

  equiv-dup-standard-sequential-colimit :
    { P : standard-sequential-colimit A → UU l2} →
    ( (x : standard-sequential-colimit A) → P x) ≃
    ( dependent-cocone-sequential-diagram A
      ( cocone-standard-sequential-colimit A)
      ( P))
  equiv-dup-standard-sequential-colimit = {!!}

  dependent-cogap-standard-sequential-colimit :
    { P : standard-sequential-colimit A → UU l2} →
    dependent-cocone-sequential-diagram A
      ( cocone-standard-sequential-colimit A)
      ( P) →
    ( x : standard-sequential-colimit A) → P x
  dependent-cogap-standard-sequential-colimit = {!!}
```

### The small predicate of being a sequential colimit cocone

The [proposition](foundation-core.propositions.md) `is-sequential-colimit` is
the assertion that the cogap map is an
[equivalence](foundation-core.equivalences.md). Note that this proposition is
[small](foundation-core.small-types.md), whereas
[the universal property](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
is a large proposition.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  (c : cocone-sequential-diagram A X)
  where

  is-sequential-colimit : UU (l1 ⊔ l2)
  is-sequential-colimit = {!!}

  is-prop-is-sequential-colimit : is-prop is-sequential-colimit
  is-prop-is-sequential-colimit = {!!}

  is-sequential-colimit-Prop : Prop (l1 ⊔ l2)
  pr1 is-sequential-colimit-Prop = {!!}
```

### Homotopies between maps from the standard sequential colimit

Maps from the standard sequential colimit induce cocones under the sequential
diagrams, and a [homotopy](foundation-core.homotopies.md) between the maps is
exactly a homotopy of the cocones.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( f g : standard-sequential-colimit A → X)
  where

  htpy-out-of-standard-sequential-colimit : UU (l1 ⊔ l2)
  htpy-out-of-standard-sequential-colimit = {!!}

  equiv-htpy-htpy-out-of-standard-sequential-colimit :
    htpy-out-of-standard-sequential-colimit ≃ (f ~ g)
  equiv-htpy-htpy-out-of-standard-sequential-colimit = {!!}
```

We may then obtain a homotopy of maps from a homotopy of their induced cocones.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  { f g : standard-sequential-colimit A → X}
  ( H : htpy-out-of-standard-sequential-colimit A f g)
  where

  htpy-htpy-out-of-standard-sequential-colimit : f ~ g
  htpy-htpy-out-of-standard-sequential-colimit = {!!}
```

### A type satisfies `is-sequential-colimit` if and only if it has the (dependent) universal property of sequential colimits

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  (c : cocone-sequential-diagram A X)
  where

  universal-property-is-sequential-colimit :
    is-sequential-colimit c → universal-property-sequential-colimit A c
  universal-property-is-sequential-colimit = {!!}

  dependent-universal-property-is-sequential-colimit :
    is-sequential-colimit c →
    dependent-universal-property-sequential-colimit A c
  dependent-universal-property-is-sequential-colimit = {!!}

  is-sequential-colimit-universal-property :
    universal-property-sequential-colimit A c → is-sequential-colimit c
  is-sequential-colimit-universal-property = {!!}

  is-sequential-colimit-dependent-universal-property :
    dependent-universal-property-sequential-colimit A c →
    is-sequential-colimit c
  is-sequential-colimit-dependent-universal-property = {!!}
```
