# Equivalences between semigroups

```agda
module group-theory.equivalences-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

An equivalence between semigroups is an equivalence between their underlying
types that preserves the binary operation.

## Definition

### Equivalences preserving binary operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul-equiv :
    (μA : A → A → A) (μB : B → B → B) → (A ≃ B) → UU (l1 ⊔ l2)
  preserves-mul-equiv = {!!}
```

### Equivalences of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-equiv-Semigroup :
    (type-Semigroup G ≃ type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-equiv-Semigroup = {!!}

  equiv-Semigroup : UU (l1 ⊔ l2)
  equiv-Semigroup = {!!}

  is-equiv-hom-Semigroup : hom-Semigroup G H → UU (l1 ⊔ l2)
  is-equiv-hom-Semigroup = {!!}
```

## Properties

### The total space of all equivalences of semigroups with domain `G` is contractible

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  center-total-preserves-mul-id-Semigroup :
    Σ ( has-associative-mul (type-Semigroup G))
      ( λ μ → preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)
  pr1 (pr1 (center-total-preserves-mul-id-Semigroup)) = {!!}

  contraction-total-preserves-mul-id-Semigroup :
    ( t : Σ ( has-associative-mul (type-Semigroup G))
            ( λ μ →
              preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)) →
    Id center-total-preserves-mul-id-Semigroup t
  contraction-total-preserves-mul-id-Semigroup = {!!}

  is-torsorial-preserves-mul-id-Semigroup :
    is-torsorial
      ( λ (μ : has-associative-mul (type-Semigroup G)) →
        preserves-mul (mul-Semigroup G) (pr1 μ) id)
  is-torsorial-preserves-mul-id-Semigroup = {!!}

  is-torsorial-equiv-Semigroup :
    is-torsorial (equiv-Semigroup G)
  is-torsorial-equiv-Semigroup = {!!}
```
