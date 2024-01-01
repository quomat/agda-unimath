# Universal Property of suspensions of pointed types

```agda
module synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [suspension](synthetic-homotopy-theory.suspensions-of-types.md) of a
[pointed type](structured-types.pointed-types.md) enjoys an additional universal
property, on top of
[the universal property associtated with being a suspension](synthetic-homotopy-theory.universal-property-suspensions.md).
This universal property is packaged in an adjunction: the suspension
construction on pointed types is left adjoint to the loop space construction.

#### The unit and counit of the adjunction

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  pointed-equiv-loop-pointed-identity-suspension :
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X))) ≃∗
    ( Ω (suspension-Pointed-Type X))
  pointed-equiv-loop-pointed-identity-suspension = {!!}

  pointed-map-loop-pointed-identity-suspension :
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X))) →∗
    Ω (suspension-Pointed-Type X)
  pointed-map-loop-pointed-identity-suspension = {!!}

  pointed-map-concat-meridian-suspension :
    X →∗
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X)))
  pointed-map-concat-meridian-suspension = {!!}

  pointed-map-unit-suspension-loop-adjunction :
    X →∗ Ω (suspension-Pointed-Type X)
  pointed-map-unit-suspension-loop-adjunction = {!!}

  map-unit-suspension-loop-adjunction :
    type-Pointed-Type X → type-Ω (suspension-Pointed-Type X)
  map-unit-suspension-loop-adjunction = {!!}

  map-counit-suspension-loop-adjunction :
    suspension (type-Ω X) → type-Pointed-Type X
  map-counit-suspension-loop-adjunction = {!!}

  pointed-map-counit-suspension-loop-adjunction :
    pair (suspension (type-Ω X)) (north-suspension) →∗ X
  pointed-map-counit-suspension-loop-adjunction = {!!}
```

#### The transposing maps of the adjunction

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) → (X →∗ Ω Y)
  transpose-suspension-loop-adjunction = {!!}

module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  inv-transpose-suspension-loop-adjunction :
    (X →∗ Ω Y) → (suspension-Pointed-Type X →∗ Y)
  inv-transpose-suspension-loop-adjunction = {!!}
```

We now show these maps are inverses of each other.

#### The transposing equivalence between pointed maps out of the suspension of `X` and pointed maps into the loop space of `Y`

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  equiv-transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  equiv-transpose-suspension-loop-adjunction = {!!}
```

#### The equivalence in the suspension-loop space adjunction is pointed

This remains to be shown.
[#702](https://github.com/UniMath/agda-unimath/issues/702)
