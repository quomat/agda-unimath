# Pointed types equipped with automorphisms

```agda
module structured-types.pointed-types-equipped-with-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

A pointed type equipped with an automorphism is a pair consisting of a pointed
type `A` and an automorphism on the underlying type of `A`. The base point is
not required to be preserved.

## Definitions

### Types equipped with an automorphism

```agda
Pointed-Type-With-Aut :
  (l : Level) → UU (lsuc l)
Pointed-Type-With-Aut l = {!!}

module _
  {l : Level} (X : Pointed-Type-With-Aut l)
  where

  pointed-type-Pointed-Type-With-Aut : Pointed-Type l
  pointed-type-Pointed-Type-With-Aut = {!!}

  type-Pointed-Type-With-Aut : UU l
  type-Pointed-Type-With-Aut = {!!}

  point-Pointed-Type-With-Aut : type-Pointed-Type-With-Aut
  point-Pointed-Type-With-Aut = {!!}

  aut-Pointed-Type-With-Aut : Aut type-Pointed-Type-With-Aut
  aut-Pointed-Type-With-Aut = {!!}

  map-aut-Pointed-Type-With-Aut :
    type-Pointed-Type-With-Aut → type-Pointed-Type-With-Aut
  map-aut-Pointed-Type-With-Aut = {!!}

  inv-map-aut-Pointed-Type-With-Aut :
    type-Pointed-Type-With-Aut → type-Pointed-Type-With-Aut
  inv-map-aut-Pointed-Type-With-Aut = {!!}

  is-section-inv-map-aut-Pointed-Type-With-Aut :
    (map-aut-Pointed-Type-With-Aut ∘ inv-map-aut-Pointed-Type-With-Aut) ~ id
  is-section-inv-map-aut-Pointed-Type-With-Aut = {!!}

  is-retraction-inv-map-aut-Pointed-Type-With-Aut :
    (inv-map-aut-Pointed-Type-With-Aut ∘ map-aut-Pointed-Type-With-Aut) ~ id
  is-retraction-inv-map-aut-Pointed-Type-With-Aut = {!!}
```

### Morphisms of pointed types with automorphisms

```agda
hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} →
  Pointed-Type-With-Aut l1 → Pointed-Type-With-Aut l2 → UU (l1 ⊔ l2)
hom-Pointed-Type-With-Aut {l1} {l2} X Y = {!!}

module _
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1) (Y : Pointed-Type-With-Aut l2)
  (f : hom-Pointed-Type-With-Aut X Y)
  where

  map-hom-Pointed-Type-With-Aut :
    type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y
  map-hom-Pointed-Type-With-Aut = {!!}

  preserves-point-map-hom-Pointed-Type-With-Aut :
    ( map-hom-Pointed-Type-With-Aut (point-Pointed-Type-With-Aut X)) ＝
    ( point-Pointed-Type-With-Aut Y)
  preserves-point-map-hom-Pointed-Type-With-Aut = {!!}

  preserves-aut-map-hom-Pointed-Type-With-Aut :
    ( map-hom-Pointed-Type-With-Aut ∘ map-aut-Pointed-Type-With-Aut X) ~
    ( ( map-aut-Pointed-Type-With-Aut Y) ∘ map-hom-Pointed-Type-With-Aut)
  preserves-aut-map-hom-Pointed-Type-With-Aut = {!!}
```

## Properties

### Characterization of the identity type of morphisms of pointed types with automorphisms

```agda
htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1)
  (Y : Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  UU (l1 ⊔ l2)
htpy-hom-Pointed-Type-With-Aut X Y h1 h2 = {!!}

refl-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1)
  (Y : Pointed-Type-With-Aut l2) (h : hom-Pointed-Type-With-Aut X Y) →
  htpy-hom-Pointed-Type-With-Aut X Y h h
refl-htpy-hom-Pointed-Type-With-Aut X Y h = {!!}

htpy-hom-Pointed-Type-With-Aut-eq :
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1)
  (Y : Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  h1 ＝ h2 → htpy-hom-Pointed-Type-With-Aut X Y h1 h2
htpy-hom-Pointed-Type-With-Aut-eq X Y h1 .h1 refl = {!!}

is-torsorial-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1)
  (Y : Pointed-Type-With-Aut l2) (h1 : hom-Pointed-Type-With-Aut X Y) →
  is-torsorial (htpy-hom-Pointed-Type-With-Aut X Y h1)
is-torsorial-htpy-hom-Pointed-Type-With-Aut X Y h1 = {!!}

is-equiv-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1)
  (Y : Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  is-equiv (htpy-hom-Pointed-Type-With-Aut-eq X Y h1 h2)
is-equiv-htpy-hom-Pointed-Type-With-Aut X Y h1 = {!!}

eq-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : Pointed-Type-With-Aut l1)
  (Y : Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  htpy-hom-Pointed-Type-With-Aut X Y h1 h2 → h1 ＝ h2
eq-htpy-hom-Pointed-Type-With-Aut X Y h1 h2 = {!!}
```
