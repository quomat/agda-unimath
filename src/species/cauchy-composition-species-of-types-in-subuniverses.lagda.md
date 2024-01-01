# Cauchy composition of species of types in a subuniverse

```agda
module species.cauchy-composition-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-closed-subuniverses
open import foundation.sigma-decomposition-subuniverse
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.species-of-types-in-subuniverses
open import species.unit-cauchy-composition-species-of-types
open import species.unit-cauchy-composition-species-of-types-in-subuniverses
```

</details>

## Idea

A species `S : type-subuniverse P → type-subuniverse Q` induces its
[Cauchy series](species.cauchy-series-species-of-types-in-subuniverses.md)

```text
  X ↦ Σ (A : type-subuniverse P), (S A) × (A → X)
```

The **Cauchy composition** of species `S` and `T` is obtained from the
coefficients of the composite of the Cauchy series of `S` and `T`.

## Definition

### Cauchy composition of species

```agda
module _
  {l1 l2 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  where

  type-cauchy-composition-species-subuniverse :
    {l3 l4 : Level} →
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3)) →
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l4)) →
    type-subuniverse P → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-cauchy-composition-species-subuniverse = {!!}

  is-closed-under-cauchy-composition-species-subuniverse : UUω
  is-closed-under-cauchy-composition-species-subuniverse = {!!}

module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C2 : is-closed-under-Σ-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  where

  cauchy-composition-species-subuniverse :
    species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
  cauchy-composition-species-subuniverse = {!!}
```

## Properties

### Σ-extension of species of types in a subuniverse preserves cauchy composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C2 : is-closed-under-Σ-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  where

  preserves-cauchy-composition-Σ-extension-species-subuniverse :
    ( X : UU l1) →
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
      ( X) ≃
    ( cauchy-composition-species-types
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( X))
  preserves-cauchy-composition-Σ-extension-species-subuniverse = {!!}
```

### Unit laws for Cauchy composition of species-subuniverse

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l))
  ( C3 : is-in-subuniverse P (raise-unit l1))
  ( C4 :
    is-closed-under-is-contr-subuniverses P
      ( subuniverse-global-subuniverse Q l1))
  (X : UU l1)
  where

  map-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    Σ-extension-species-subuniverse P
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( X) →
    unit-species-types X
  map-equiv-Σ-extension-cauchy-composition-unit-subuniverse = {!!}

  map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    unit-species-types X →
    Σ-extension-species-subuniverse P
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( X)
  map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse = {!!}

  is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    ( map-equiv-Σ-extension-cauchy-composition-unit-subuniverse ∘
      map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse) ~ id
  is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse = {!!}

  is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    ( map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse ∘
      map-equiv-Σ-extension-cauchy-composition-unit-subuniverse) ~ id
  is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse = {!!}

  is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    is-equiv map-equiv-Σ-extension-cauchy-composition-unit-subuniverse
  is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverse = {!!}

  equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( X) ≃
    unit-species-types X
  equiv-Σ-extension-cauchy-composition-unit-subuniverse = {!!}

module _
  { l1 l2 l3 : Level}
  ( P : subuniverse l1 l2)
  ( Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  ( C2 : is-closed-under-Σ-subuniverse P)
  ( C3 : is-in-subuniverse P (raise-unit l1))
  ( C4 :
    is-closed-under-is-contr-subuniverses P
      ( subuniverse-global-subuniverse Q l1))
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  where

  equiv-left-unit-law-cauchy-composition-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse P Q C1 C2
        ( cauchy-composition-unit-species-subuniverse P Q C4)
        ( S)
        ( X)) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-left-unit-law-cauchy-composition-species-subuniverse = {!!}

  equiv-right-unit-law-cauchy-composition-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S
        ( cauchy-composition-unit-species-subuniverse P Q C4)
        ( X)) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-right-unit-law-cauchy-composition-species-subuniverse = {!!}
```

### Associativity of composition of species of types in subuniverse

```agda
module _
  { l1 l2 l3 l4 l5 : Level}
  ( P : subuniverse l1 l2)
  ( Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  ( C2 : is-closed-under-Σ-subuniverse P)
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  ( T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  ( U : species-subuniverse P (subuniverse-global-subuniverse Q l5))
  where

  equiv-associative-cauchy-composition-species-subuniverse :
    (X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S
        ( cauchy-composition-species-subuniverse P Q C1 C2 T U)
        ( X)) ≃
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse P Q C1 C2
        ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
        ( U)
        ( X))
  equiv-associative-cauchy-composition-species-subuniverse = {!!}
```
