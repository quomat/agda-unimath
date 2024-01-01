# Universal property of suspensions

```agda
module synthetic-homotopy-theory.universal-property-suspensions where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Since suspensions are just [pushouts](synthetic-homotopy-theory.pushouts.md),
they retain the expected
[universal property](synthetic-homotopy-theory.universal-property-pushouts.md),
which states that the map `cocone-map` is a equivalence. We denote this
universal property by `universal-property-pushout-suspension`. But, due to the
special nature of the span being pushed out, the suspension of a type enjoys an
equivalent universal property, here denoted by `universal-property-suspension`.
This universal property states that the map `ev-suspension` is an equivalence.

## Definitions

### The universal property of the suspension

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (s : suspension-structure X Y)
  where

  ev-suspension :
    {l3 : Level} (Z : UU l3) → (Y → Z) → suspension-structure X Z
  pr1 (ev-suspension Z h) = {!!}

  universal-property-suspension : UUω
  universal-property-suspension = {!!}
```

### The universal property of the suspension as a pushout

```agda
universal-property-pushout-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (s : suspension-structure X Y) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-pushout-suspension l X Y s = {!!}
```

## Properties

```agda
triangle-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (s : suspension-structure X Y) →
  (Z : UU l3) →
  ( ( suspension-structure-suspension-cocone) ∘
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( suspension-cocone-suspension-structure s))) ~
  ( ev-suspension s Z)
triangle-ev-suspension (N , S , merid) Z h = {!!}

is-equiv-ev-suspension :
  { l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  ( s : suspension-structure X Y) →
  ( up-Y : universal-property-pushout-suspension l3 X Y s) →
  ( Z : UU l3) → is-equiv (ev-suspension s Z)
is-equiv-ev-suspension {X = X} s up-Y Z = {!!}
```
