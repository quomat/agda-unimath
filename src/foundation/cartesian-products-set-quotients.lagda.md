# Cartesian products of set quotients

```agda
module foundation.cartesian-products-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.products-equivalence-relations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given two types `A` and `B`, equipped with equivalence relations `R` and `S`,
respectively, the cartesian product of their set quotients is the set quotient
of their product.

## Definition

### The product of two relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  prod-set-quotient-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  prod-set-quotient-Set = {!!}

  prod-set-quotient : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  prod-set-quotient = {!!}

  is-set-prod-set-quotient : is-set prod-set-quotient
  is-set-prod-set-quotient = {!!}

  prod-set-quotient-map : (A × B) → prod-set-quotient
  prod-set-quotient-map (a , b) = {!!}

  reflecting-map-prod-quotient-map :
    reflecting-map-equivalence-relation
      ( prod-equivalence-relation R S)
      ( prod-set-quotient)
  reflecting-map-prod-quotient-map = {!!}
```

## Properties

### The product of sets quotients is a set quotient

```agda
  inv-precomp-set-quotient-prod-set-quotient :
    {l : Level}
    (X : Set l) →
    reflecting-map-equivalence-relation
      ( prod-equivalence-relation R S)
      ( type-Set X) →
    hom-Set prod-set-quotient-Set X
  inv-precomp-set-quotient-prod-set-quotient = {!!}

  is-section-inv-precomp-set-quotient-prod-set-quotient :
    { l : Level}
    ( X : Set l) →
    ( precomp-Set-Quotient
      ( prod-equivalence-relation R S)
      ( prod-set-quotient-Set)
      ( reflecting-map-prod-quotient-map)
      ( X) ∘
      ( inv-precomp-set-quotient-prod-set-quotient X)) ~
    ( id)
  is-section-inv-precomp-set-quotient-prod-set-quotient = {!!}

  is-retraction-inv-precomp-set-quotient-prod-set-quotient :
    { l : Level}
    ( X : Set l) →
    ( ( inv-precomp-set-quotient-prod-set-quotient X) ∘
      ( precomp-Set-Quotient
        ( prod-equivalence-relation R S)
        ( prod-set-quotient-Set)
        ( reflecting-map-prod-quotient-map)
        ( X))) ~
    ( id)
  is-retraction-inv-precomp-set-quotient-prod-set-quotient = {!!}

  is-set-quotient-prod-set-quotient :
    is-set-quotient
      ( prod-equivalence-relation R S)
      ( prod-set-quotient-Set)
      ( reflecting-map-prod-quotient-map)
  is-set-quotient-prod-set-quotient = {!!}

  quotient-prod : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-prod = {!!}

  type-quotient-prod : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-quotient-prod = {!!}

  equiv-quotient-prod-prod-set-quotient :
    prod-set-quotient ≃ type-Set (quotient-prod)
  equiv-quotient-prod-prod-set-quotient = {!!}

  triangle-uniqueness-prod-set-quotient :
    ( map-equiv equiv-quotient-prod-prod-set-quotient ∘
      prod-set-quotient-map) ~
    quotient-map (prod-equivalence-relation R S)
  triangle-uniqueness-prod-set-quotient = {!!}
```
