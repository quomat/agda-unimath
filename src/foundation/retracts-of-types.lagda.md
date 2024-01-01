# Retracts of types

```agda
module foundation.retracts-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

We say that a type `A` is a **retract of** a type `B` if the types `A` and `B`
come equipped with **retract data**, i.e., with maps

```text
      i        r
  A -----> B -----> A
```

and a [homotopy](foundation-core.homotopies.md) `r ∘ i ~ id`. The map `i` is
called the **inclusion** of the retract data, and the map `r` is called the
**underlying map of the retraction**.

## Definitions

### The type of witnesses that `A` is a retract of `B`

The predicate `retract B` is used to assert that a type is a retract of `B`,
i.e., the type `retract B A` is the type of maps from `A` to `B` that come
equipped with a retraction.

We also introduce more intuitive infix notation `A retract-of B` to assert that
`A` is a retract of `B`.

```agda
retract : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
retract B A = {!!}

infix 6 _retract-of_

_retract-of_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A retract-of B = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : retract B A)
  where

  inclusion-retract : A → B
  inclusion-retract = {!!}

  retraction-retract : retraction inclusion-retract
  retraction-retract = {!!}

  map-retraction-retract : B → A
  map-retraction-retract = {!!}

  is-retraction-map-retraction-retract :
    is-section map-retraction-retract inclusion-retract
  is-retraction-map-retraction-retract = {!!}

  section-retract : section map-retraction-retract
  pr1 section-retract = {!!}
```

## Properties

### If `A` is a retract of `B` with inclusion `i : A → B`, then `x ＝ y` is a retract of `i x ＝ i y` for any two elements `x y : A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : retract B A) (x y : A)
  where

  retract-eq :
    (x ＝ y) retract-of (inclusion-retract R x ＝ inclusion-retract R y)
  pr1 retract-eq = {!!}
```

## See also

- [Retracts of maps](foundation.retracts-of-maps.md)
