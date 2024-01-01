# Set truncations

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.set-truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equality-coproduct-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.mere-equality
open import foundation.postcomposition-functions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.slice
open import foundation.surjective-maps
open import foundation.truncations
open import foundation.uniqueness-set-truncations
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universal-property-set-quotients
open import foundation.universal-property-set-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Idea

The **set truncation** of a type `A` is a map `η : A → trunc-Set A` that
satisfies
[the universal property of set truncations](foundation.universal-property-set-truncation.md).

## Definition

```agda
type-trunc-Set : {l : Level} → UU l → UU l
type-trunc-Set = {!!}

is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)
is-set-type-trunc-Set = {!!}

trunc-Set : {l : Level} → UU l → Set l
trunc-Set = {!!}

unit-trunc-Set : {l : Level} {A : UU l} → A → type-trunc-Set A
unit-trunc-Set = {!!}

is-set-truncation-trunc-Set :
  {l1 : Level} (A : UU l1) → is-set-truncation (trunc-Set A) unit-trunc-Set
is-set-truncation-trunc-Set A = {!!}
```

## Properties

### The dependent universal property of set truncations

```agda
dependent-universal-property-trunc-Set :
  {l1 : Level} {A : UU l1} →
  dependent-universal-property-set-truncation (trunc-Set A) unit-trunc-Set
dependent-universal-property-trunc-Set = {!!}

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2)
  (f : (x : A) → type-Set (B (unit-trunc-Set x)))
  where

  Π-trunc-Set : UU (l1 ⊔ l2)
  Π-trunc-Set = {!!}

  function-dependent-universal-property-trunc-Set :
    (x : type-trunc-Set A) → type-Set (B x)
  function-dependent-universal-property-trunc-Set = {!!}

  compute-dependent-universal-property-trunc-Set :
    function-dependent-universal-property-trunc-Set ∘ unit-trunc-Set ~ f
  compute-dependent-universal-property-trunc-Set = {!!}

  apply-dependent-universal-property-trunc-Set' :
    (x : type-trunc-Set A) → type-Set (B x)
  apply-dependent-universal-property-trunc-Set' = {!!}
```

### The universal property of set truncations

```agda
universal-property-trunc-Set :
  {l1 : Level} (A : UU l1) →
  universal-property-set-truncation (trunc-Set A) (unit-trunc-Set)
universal-property-trunc-Set A = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2)
  where

  equiv-universal-property-trunc-Set :
    (type-trunc-Set A → type-Set B) ≃ (A → type-Set B)
  equiv-universal-property-trunc-Set = {!!}

  apply-universal-property-trunc-Set :
    (t : type-trunc-Set A) → (A → type-Set B) → type-Set B
  apply-universal-property-trunc-Set t f = {!!}

  map-universal-property-trunc-Set :
    (A → type-Set B) → hom-Set (trunc-Set A) B
  map-universal-property-trunc-Set = {!!}

  triangle-universal-property-trunc-Set :
    (f : A → type-Set B) →
    map-universal-property-trunc-Set f ∘ unit-trunc-Set ~ f
  triangle-universal-property-trunc-Set = {!!}

apply-universal-property-trunc-Set' :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Set A) (B : Set l2) →
  (A → type-Set B) → type-Set B
apply-universal-property-trunc-Set' t B f = {!!}
```

### The set truncation of `X` is the set quotient by the mere equality relation

```agda
reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-equivalence-relation
    ( mere-eq-equivalence-relation A)
    ( type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A = {!!}

abstract
  is-set-quotient-trunc-Set :
    {l1 : Level} (A : UU l1) →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( trunc-Set A)
      ( reflecting-map-mere-eq-unit-trunc-Set A)
  is-set-quotient-trunc-Set A = {!!}

module _
  {l : Level}
  where

  abstract
    is-surjective-and-effective-unit-trunc-Set :
      (A : UU l) →
      is-surjective-and-effective
        ( mere-eq-equivalence-relation A)
        ( unit-trunc-Set)
    is-surjective-and-effective-unit-trunc-Set A = {!!}

  abstract
    is-surjective-unit-trunc-Set :
      (A : UU l) → is-surjective (unit-trunc-Set {A = A})
    is-surjective-unit-trunc-Set A = {!!}

  abstract
    is-effective-unit-trunc-Set :
      (A : UU l) →
      is-effective (mere-eq-equivalence-relation A) (unit-trunc-Set {A = A})
    is-effective-unit-trunc-Set A = {!!}

  abstract
    apply-effectiveness-unit-trunc-Set :
      {A : UU l} {x y : A} → unit-trunc-Set x ＝ unit-trunc-Set y → mere-eq x y
    apply-effectiveness-unit-trunc-Set {A = A} {x} {y} = {!!}

  abstract
    apply-effectiveness-unit-trunc-Set' :
      {A : UU l} {x y : A} → mere-eq x y → unit-trunc-Set x ＝ unit-trunc-Set y
    apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} = {!!}

  emb-trunc-Set : (A : UU l) → type-trunc-Set A ↪ (A → Prop l)
  emb-trunc-Set A = {!!}

  hom-slice-trunc-Set :
    (A : UU l) → hom-slice (mere-eq-Prop {A = A}) (map-emb (emb-trunc-Set A))
  pr1 (hom-slice-trunc-Set A) = {!!}

  abstract
    is-image-trunc-Set :
      (A : UU l) →
      is-image
        ( mere-eq-Prop {A = A})
        ( emb-trunc-Set A)
        ( hom-slice-trunc-Set A)
    is-image-trunc-Set A = {!!}
```

### Uniqueness of `trunc-Set`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  {h : hom-Set B (trunc-Set A)} (H : h ∘ f ~ unit-trunc-Set)
  where

  abstract
    is-equiv-is-set-truncation' : is-set-truncation B f → is-equiv h
    is-equiv-is-set-truncation' Sf = {!!}

  abstract
    is-set-truncation-is-equiv' :
      is-equiv h → is-set-truncation B f
    is-set-truncation-is-equiv' Eh = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  {h : hom-Set (trunc-Set A) B} (H : h ∘ unit-trunc-Set ~ f)
  where

  abstract
    is-equiv-is-set-truncation : is-set-truncation B f → is-equiv h
    is-equiv-is-set-truncation Sf = {!!}

  abstract
    is-set-truncation-is-equiv :
      is-equiv h → is-set-truncation B f
    is-set-truncation-is-equiv Eh = {!!}

is-equiv-unit-trunc-Set :
  {l : Level} (A : Set l) → is-equiv (unit-trunc-Set {A = type-Set A})
is-equiv-unit-trunc-Set = {!!}

equiv-unit-trunc-Set :
  {l : Level} (A : Set l) → type-Set A ≃ type-trunc-Set (type-Set A)
equiv-unit-trunc-Set = {!!}

equiv-unit-trunc-empty-Set : empty ≃ type-trunc-Set empty
equiv-unit-trunc-empty-Set = {!!}

abstract
  is-empty-trunc-Set :
    {l : Level} {A : UU l} → is-empty A → is-empty (type-trunc-Set A)
  is-empty-trunc-Set f x = {!!}

abstract
  is-empty-is-empty-trunc-Set :
    {l : Level} {A : UU l} → is-empty (type-trunc-Set A) → is-empty A
  is-empty-is-empty-trunc-Set f = {!!}

equiv-unit-trunc-unit-Set : unit ≃ type-trunc-Set unit
equiv-unit-trunc-unit-Set = {!!}

abstract
  is-contr-trunc-Set :
    {l : Level} {A : UU l} → is-contr A → is-contr (type-trunc-Set A)
  is-contr-trunc-Set {l} {A} H = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (Sf : is-set-truncation B f)
  where

  abstract
    uniqueness-trunc-Set :
      is-contr
        ( Σ (type-trunc-Set A ≃ type-Set B)
        ( λ e → map-equiv e ∘ unit-trunc-Set ~ f))
    uniqueness-trunc-Set = {!!}

  equiv-uniqueness-trunc-Set : type-trunc-Set A ≃ type-Set B
  equiv-uniqueness-trunc-Set = {!!}

  map-equiv-uniqueness-trunc-Set : type-trunc-Set A → type-Set B
  map-equiv-uniqueness-trunc-Set = {!!}

  triangle-uniqueness-trunc-Set :
    map-equiv-uniqueness-trunc-Set ∘ unit-trunc-Set ~ f
  triangle-uniqueness-trunc-Set = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (Sf : is-set-truncation B f)
  where

  abstract
    uniqueness-trunc-Set' :
      is-contr
        ( Σ ( type-Set B ≃ type-trunc-Set A)
            ( λ e → map-equiv e ∘ f ~ unit-trunc-Set))
    uniqueness-trunc-Set' = {!!}

  equiv-uniqueness-trunc-Set' : type-Set B ≃ type-trunc-Set A
  equiv-uniqueness-trunc-Set' = {!!}

  map-equiv-uniqueness-trunc-Set' : type-Set B → type-trunc-Set A
  map-equiv-uniqueness-trunc-Set' = {!!}

  triangle-uniqueness-trunc-Set' :
    map-equiv-uniqueness-trunc-Set' ∘ f ~ unit-trunc-Set
  triangle-uniqueness-trunc-Set' = {!!}
```

### The set truncation of a set is equivalent to the set

```agda
module _
  {l : Level} (A : Set l)
  where

  equiv-unit-trunc-set : type-Set A ≃ type-trunc-Set (type-Set A)
  equiv-unit-trunc-set = {!!}
```

### Distributive of set truncation over coproduct

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-coprod-Set :
      is-contr
        ( Σ ( type-equiv-Set
              ( trunc-Set (A + B))
              ( coprod-Set (trunc-Set A) (trunc-Set B)))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-coprod unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-coprod-Set = {!!}

  equiv-distributive-trunc-coprod-Set :
    type-equiv-Set (trunc-Set (A + B)) (coprod-Set (trunc-Set A) (trunc-Set B))
  equiv-distributive-trunc-coprod-Set = {!!}

  map-equiv-distributive-trunc-coprod-Set :
    hom-Set (trunc-Set (A + B)) (coprod-Set (trunc-Set A) (trunc-Set B))
  map-equiv-distributive-trunc-coprod-Set = {!!}

  triangle-distributive-trunc-coprod-Set :
    ( map-equiv-distributive-trunc-coprod-Set ∘ unit-trunc-Set) ~
    ( map-coprod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-coprod-Set = {!!}
```

### Set truncations of Σ-types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  abstract
    trunc-Σ-Set :
      is-contr
        ( Σ ( type-trunc-Set (Σ A B) ≃
              type-trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))))
    trunc-Σ-Set = {!!}

  equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) ≃ type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  equiv-trunc-Σ-Set = {!!}

  map-equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) → type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  map-equiv-trunc-Σ-Set = {!!}
```

### `trunc-Set` distributes over products

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-prod-Set :
      is-contr
        ( Σ ( type-trunc-Set (A × B) ≃ (type-trunc-Set A × type-trunc-Set B))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-prod unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-prod-Set = {!!}

  equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) ≃ (type-trunc-Set A × type-trunc-Set B)
  equiv-distributive-trunc-prod-Set = {!!}

  map-equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) → type-trunc-Set A × type-trunc-Set B
  map-equiv-distributive-trunc-prod-Set = {!!}

  map-inv-equiv-distributive-trunc-prod-Set :
    type-trunc-Set A × type-trunc-Set B → type-trunc-Set (A × B)
  map-inv-equiv-distributive-trunc-prod-Set = {!!}

  triangle-distributive-trunc-prod-Set :
    ( map-equiv-distributive-trunc-prod-Set ∘ unit-trunc-Set) ~
    ( map-prod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-prod-Set = {!!}
```
