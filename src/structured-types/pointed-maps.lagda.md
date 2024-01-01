# Pointed maps

```agda
module structured-types.pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-types
```

</details>

## Idea

A pointed map from a pointed type `A` to a pointed type `B` is a base point
preserving function from `A` to `B`.

## Definitions

### Pointed maps

```agda
module _
  {l1 l2 : Level}
  where

  pointed-map : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  pointed-map A B = {!!}

  infixr 5 _→∗_
  _→∗_ = {!!}
```

**Note**: the subscript asterisk symbol used for the pointed map type `_→∗_`,
and pointed type constructions in general, is the
[asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`), not
the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
  constant-pointed-map : (A : Pointed-Type l1) (B : Pointed-Type l2) → A →∗ B
  pr1 (constant-pointed-map A B) = {!!}

  pointed-map-Pointed-Type :
    Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
  pointed-map-Pointed-Type = {!!}

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-pointed-map : A →∗ B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map = {!!}

  preserves-point-pointed-map :
    (f : A →∗ B) →
    map-pointed-map f (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-pointed-map = {!!}
```

### Precomposing pointed maps

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Fam l3 B) (f : A →∗ B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  pr1 precomp-Pointed-Fam = {!!}

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  pr1 (precomp-pointed-Π g) x = {!!}
```

### Composing pointed maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  map-comp-pointed-map :
    B →∗ C → A →∗ B → type-Pointed-Type A → type-Pointed-Type C
  map-comp-pointed-map = {!!}

  preserves-point-comp-pointed-map :
    (g : B →∗ C) (f : A →∗ B) →
    (map-comp-pointed-map g f (point-Pointed-Type A)) ＝ point-Pointed-Type C
  preserves-point-comp-pointed-map = {!!}

  comp-pointed-map : B →∗ C → A →∗ B → A →∗ C
  pr1 (comp-pointed-map g f) = {!!}

precomp-pointed-map :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} (C : Pointed-Type l3) →
  A →∗ B → B →∗ C → A →∗ C
precomp-pointed-map = {!!}

infixr 15 _∘∗_
_∘∗_ :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3} →
  B →∗ C → A →∗ B → A →∗ C
_∘∗_ = {!!}
```

### The identity pointed map

```agda
module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →∗ A
  pr1 id-pointed-map = {!!}
```
