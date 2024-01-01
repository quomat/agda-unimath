# Functoriality of higher modalities

```agda
module orthogonal-factorization-systems.functoriality-higher-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.small-types
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

Every [higher modality](orthogonal-factorization-systems.higher-modalities.md)
`○` is functorial. Given a map `f : A → B`, there is a
[unique](foundation-core.contractible-types.md) map `○f : ○A → ○B` that fits
into a [natural square](foundation-core.commuting-squares-of-maps.md)

```text
         f
    X ------> Y
    |         |
    |         |
    v         v
   ○ X ----> ○ Y.
        ○ f
```

This construction preserves [composition](foundation-core.function-types.md),
[identifications](foundation-core.identity-types.md),
[homotopies](foundation-core.homotopies.md), and
[equivalences](foundation-core.equivalences.md).

## Properties

### Action on maps

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

  ap-map-higher-modality :
    {X Y : UU l1} →
    (X → Y) → operator-higher-modality m X → operator-higher-modality m Y
  ap-map-higher-modality = {!!}
```

### Functoriality

```agda
module _
  {l : Level} (m : higher-modality l l)
  where

  functoriality-higher-modality :
    {X Y Z : UU l} (g : Y → Z) (f : X → Y) →
    ( ap-map-higher-modality m g ∘ ap-map-higher-modality m f) ~
    ( ap-map-higher-modality m (g ∘ f))
  functoriality-higher-modality {X} {Y} {Z} g f = {!!}
```

### Naturality of the unit of a higher modality

For every map `f : X → Y` there is a naturality square

```text
         f
    X ------> Y
    |         |
    |         |
    v         v
   ○ X ----> ○ Y.
        ○ f
```

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

  naturality-unit-higher-modality :
    {X Y : UU l1} (f : X → Y) →
    ( ap-map-higher-modality m f ∘ unit-higher-modality m) ~
    ( unit-higher-modality m ∘ f)
  naturality-unit-higher-modality = {!!}
```

```agda
  naturality-unit-higher-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-higher-modality m x ＝ unit-higher-modality m x' →
    unit-higher-modality m (f x) ＝ unit-higher-modality m (f x')
  naturality-unit-higher-modality' = {!!}

module _
  {l : Level} (m : higher-modality l l)
  where

  compute-naturality-unit-ind-modality :
    {X Y Z : UU l} (g : Y → Z) (f : X → Y) (x : X) →
    ( ( functoriality-higher-modality m g f (unit-higher-modality m x)) ∙
      ( naturality-unit-higher-modality m (g ∘ f) x)) ＝
    ( ( ap
        ( ap-map-higher-modality m g)
        ( naturality-unit-higher-modality m f x)) ∙
      ( naturality-unit-higher-modality m g (f x)))
  compute-naturality-unit-ind-modality g f x = {!!}
```

### Action on homotopies

This definition of action on [homotopies](foundation-core.homotopies.md) is
meant to avoid using
[function extensionality](foundation.function-extensionality.md). This is left
for future work.

```agda
module _
  {l : Level} (m : higher-modality l l)
  where

  htpy-ap-higher-modality :
    {X Y : UU l} {f g : X → Y} →
    f ~ g → ap-map-higher-modality m f ~ ap-map-higher-modality m g
  htpy-ap-higher-modality H x' = {!!}
```

## References

- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
