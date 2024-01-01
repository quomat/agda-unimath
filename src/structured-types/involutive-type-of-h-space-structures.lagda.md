# The involutive type of H-space structures on a pointed type

```agda
module structured-types.involutive-type-of-h-space-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.symmetric-identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.constant-maps-pointed-types
open import structured-types.pointed-types

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

We construct the **involutive type of H-space structures** on a pointed type.

## Definition

### The involutive type of H-space structures on a pointed type

```agda
h-space-Involutive-Type :
  {l1 : Level} (A : Pointed-Type l1) (X : 2-Element-Type lzero) → UU l1
h-space-Involutive-Type = {!!}
```

## Properties

### Characterization of equality in the involutive type of H-space structures on a pointed type

```agda
module _
  {l1 : Level} (A : Pointed-Type l1) (X : 2-Element-Type lzero)
  where

  htpy-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) → UU l1
  htpy-h-space-Involutive-Type = {!!}

  refl-htpy-h-space-Involutive-Type :
    (μ : h-space-Involutive-Type A X) → htpy-h-space-Involutive-Type μ μ
  refl-htpy-h-space-Involutive-Type = {!!}

  is-torsorial-htpy-h-space-Involutive-Type :
    ( μ : h-space-Involutive-Type A X) →
    is-torsorial (htpy-h-space-Involutive-Type μ)
  is-torsorial-htpy-h-space-Involutive-Type = {!!}

  htpy-eq-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    (μ ＝ μ') → htpy-h-space-Involutive-Type μ μ'
  htpy-eq-h-space-Involutive-Type = {!!}

  is-equiv-htpy-eq-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    is-equiv (htpy-eq-h-space-Involutive-Type μ μ')
  is-equiv-htpy-eq-h-space-Involutive-Type = {!!}

  extensionality-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    (μ ＝ μ') ≃ htpy-h-space-Involutive-Type μ μ'
  extensionality-h-space-Involutive-Type = {!!}

  eq-htpy-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    htpy-h-space-Involutive-Type μ μ' → μ ＝ μ'
  eq-htpy-h-space-Involutive-Type = {!!}
```
