# Pointed equivalences

```agda
module structured-types.pointed-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A **pointed equivalence** is an equivalence in the category of pointed spaces.
Equivalently, a pointed equivalence is a
[pointed map](structured-types.pointed-maps.md) of which the underlying function
is an [equivalence](foundation-core.equivalences.md).

## Definitions

### Pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-equiv-pointed-map : (A →∗ B) → UU (l1 ⊔ l2)
  is-equiv-pointed-map = {!!}

  is-prop-is-equiv-pointed-map : (f : A →∗ B) → is-prop (is-equiv-pointed-map f)
  is-prop-is-equiv-pointed-map = {!!}

  is-equiv-pointed-map-Prop : (A →∗ B) → Prop (l1 ⊔ l2)
  is-equiv-pointed-map-Prop = {!!}

pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → UU (l1 ⊔ l2)
pointed-equiv = {!!}

infix 6 _≃∗_
_≃∗_ = {!!}

compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ≃∗ B) ≃ Σ (A →∗ B) (is-equiv-pointed-map {A = A} {B})
compute-pointed-equiv = {!!}

inv-compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Σ (A →∗ B) (is-equiv-pointed-map {A = A} {B}) ≃ (A ≃∗ B)
inv-compute-pointed-equiv = {!!}

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (e : A ≃∗ B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = {!!}

  map-equiv-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-equiv-pointed-equiv = {!!}

  is-equiv-map-equiv-pointed-equiv : is-equiv map-equiv-pointed-equiv
  is-equiv-map-equiv-pointed-equiv = {!!}

  preserves-point-equiv-pointed-equiv :
    Id (map-equiv-pointed-equiv (point-Pointed-Type A)) (point-Pointed-Type B)
  preserves-point-equiv-pointed-equiv = {!!}

  pointed-map-pointed-equiv : A →∗ B
  pointed-map-pointed-equiv = {!!}

  is-equiv-pointed-map-pointed-equiv :
    is-equiv-pointed-map pointed-map-pointed-equiv
  is-equiv-pointed-map-pointed-equiv = {!!}
```

### The identity pointed equivalence

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  id-pointed-equiv : A ≃∗ A
  id-pointed-equiv = {!!}
```

### Composition of pointed equivalences

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  comp-pointed-equiv : (B ≃∗ C) → (A ≃∗ B) → (A ≃∗ C)
  comp-pointed-equiv = {!!}
```

### Pointed isomorphisms

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  section-pointed-map : UU (l1 ⊔ l2)
  section-pointed-map = {!!}

  retraction-pointed-map : UU (l1 ⊔ l2)
  retraction-pointed-map = {!!}

  is-iso-pointed-map : UU (l1 ⊔ l2)
  is-iso-pointed-map = {!!}
```

## Properties

### Extensionality of the universe of pointed types

```agda
module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  is-torsorial-equiv-Pointed-Type :
    is-torsorial (λ B → A ≃∗ B)
  is-torsorial-equiv-Pointed-Type = {!!}

  extensionality-Pointed-Type : (B : Pointed-Type l1) → Id A B ≃ (A ≃∗ B)
  extensionality-Pointed-Type = {!!}

  eq-pointed-equiv : (B : Pointed-Type l1) → A ≃∗ B → Id A B
  eq-pointed-equiv = {!!}
```

### Being a pointed equivalence is equivalent to being a pointed isomorphism

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-contr-section-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-contr (section-pointed-map f)
  is-contr-section-is-equiv-pointed-map = {!!}

  is-contr-retraction-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-contr (retraction-pointed-map f)
  is-contr-retraction-is-equiv-pointed-map = {!!}

  is-contr-is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-contr (is-iso-pointed-map f)
  is-contr-is-iso-is-equiv-pointed-map = {!!}

  is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-iso-pointed-map f
  is-iso-is-equiv-pointed-map = {!!}

  is-equiv-is-iso-pointed-map :
    is-iso-pointed-map f → is-equiv-pointed-map f
  is-equiv-is-iso-pointed-map = {!!}

  is-prop-is-iso-pointed-map : is-prop (is-iso-pointed-map f)
  is-prop-is-iso-pointed-map = {!!}

  equiv-is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map f ≃ (is-iso-pointed-map f)
  equiv-is-iso-is-equiv-pointed-map = {!!}
```

### Precomposing by pointed equivalences is a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-equiv-is-equiv-precomp-pointed-map :
    ( {l : Level} (C : Pointed-Type l) → is-equiv (precomp-pointed-map C f)) →
    is-equiv-pointed-map f
  is-equiv-is-equiv-precomp-pointed-map = {!!}

  is-equiv-precomp-is-equiv-pointed-map :
    is-equiv-pointed-map f →
    {l : Level} → (C : Pointed-Type l) → is-equiv (precomp-pointed-map C f)
  is-equiv-precomp-is-equiv-pointed-map = {!!}

equiv-precomp-pointed-map :
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Type l3) → (A ≃∗ B) → (B →∗ C) ≃ (A →∗ C)
equiv-precomp-pointed-map = {!!}
pr2 (equiv-precomp-pointed-map C f) = {!!}
```

### Postcomposing by pointed equivalences is a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-equiv-is-equiv-comp-pointed-map :
    ({l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map {A = X} f)) →
    is-equiv-pointed-map f
  is-equiv-is-equiv-comp-pointed-map = {!!}

  is-equiv-comp-is-equiv-pointed-map :
    is-equiv-pointed-map f →
    {l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map {A = X} f)
  is-equiv-comp-is-equiv-pointed-map = {!!}
```
