# The universal property of the natural numbers

```agda
module elementary-number-theory.universal-property-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

The universal property of the natural numbers asserts that for any type `X`
equipped with a point `x : X` and an endomorphism `f : X → X`, the type of
structure preserving maps from `ℕ` to `X` is contractible.

```agda
module _
  {l : Level} {X : UU l} (x : X) (f : X → X)
  where

  structure-preserving-map-ℕ : UU l
  structure-preserving-map-ℕ = {!!}

  htpy-structure-preserving-map-ℕ :
    (h k : structure-preserving-map-ℕ) → UU l
  htpy-structure-preserving-map-ℕ = {!!}

  refl-htpy-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) → htpy-structure-preserving-map-ℕ h h
  refl-htpy-structure-preserving-map-ℕ = {!!}

  htpy-eq-structure-preserving-map-ℕ :
    {h k : structure-preserving-map-ℕ} → h ＝ k →
    htpy-structure-preserving-map-ℕ h k
  htpy-eq-structure-preserving-map-ℕ = {!!}

  is-torsorial-htpy-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) →
    is-torsorial (htpy-structure-preserving-map-ℕ h)
  is-torsorial-htpy-structure-preserving-map-ℕ = {!!}

  is-equiv-htpy-eq-structure-preserving-map-ℕ :
    (h k : structure-preserving-map-ℕ) →
    is-equiv (htpy-eq-structure-preserving-map-ℕ {h} {k})
  is-equiv-htpy-eq-structure-preserving-map-ℕ = {!!}

  eq-htpy-structure-preserving-map-ℕ :
    {h k : structure-preserving-map-ℕ} →
    htpy-structure-preserving-map-ℕ h k → h ＝ k
  eq-htpy-structure-preserving-map-ℕ = {!!}

  center-structure-preserving-map-ℕ : structure-preserving-map-ℕ
  center-structure-preserving-map-ℕ = {!!}

  contraction-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) → center-structure-preserving-map-ℕ ＝ h
  contraction-structure-preserving-map-ℕ = {!!}

  is-contr-structure-preserving-map-ℕ : is-contr structure-preserving-map-ℕ
  is-contr-structure-preserving-map-ℕ = {!!}
```
