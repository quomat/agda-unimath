# Coproduct decompositions

```agda
module foundation.coproduct-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-decompositions-subuniverse
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1 : Level} (l2 l3 : Level) (X : UU l1)
  where

  binary-coproduct-Decomposition : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  binary-coproduct-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {X : UU l1}
  (d : binary-coproduct-Decomposition l2 l3 X)
  where

  left-summand-binary-coproduct-Decomposition : UU l2
  left-summand-binary-coproduct-Decomposition = {!!}

  right-summand-binary-coproduct-Decomposition : UU l3
  right-summand-binary-coproduct-Decomposition = {!!}

  matching-correspondence-binary-coproduct-Decomposition :
    X ≃
    ( left-summand-binary-coproduct-Decomposition +
      right-summand-binary-coproduct-Decomposition)
  matching-correspondence-binary-coproduct-Decomposition = {!!}
```

## Propositions

### Coproduct decomposition is equivalent to coproduct decomposition of a full subuniverse

```agda
equiv-coproduct-Decomposition-full-subuniverse :
  {l1 : Level} → (X : UU l1) →
  binary-coproduct-Decomposition l1 l1 X ≃
  binary-coproduct-Decomposition-subuniverse (λ _ → unit-Prop) (X , star)
pr1 (equiv-coproduct-Decomposition-full-subuniverse X) d = {!!}
pr2 (equiv-coproduct-Decomposition-full-subuniverse X) = {!!}
```

### Characterization of equality of binary coproduct Decomposition

```agda
equiv-binary-coproduct-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : binary-coproduct-Decomposition l2 l3 A)
  (Y : binary-coproduct-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-binary-coproduct-Decomposition X Y = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : binary-coproduct-Decomposition l2 l3 A)
  (Y : binary-coproduct-Decomposition l4 l5 A)
  (e : equiv-binary-coproduct-Decomposition X Y)
  where

  equiv-left-summand-equiv-binary-coproduct-Decomposition :
    left-summand-binary-coproduct-Decomposition X ≃
    left-summand-binary-coproduct-Decomposition Y
  equiv-left-summand-equiv-binary-coproduct-Decomposition = {!!}

  map-equiv-left-summand-equiv-binary-coproduct-Decomposition :
    left-summand-binary-coproduct-Decomposition X →
    left-summand-binary-coproduct-Decomposition Y
  map-equiv-left-summand-equiv-binary-coproduct-Decomposition = {!!}

  equiv-right-summand-equiv-binary-coproduct-Decomposition :
    right-summand-binary-coproduct-Decomposition X ≃
    right-summand-binary-coproduct-Decomposition Y
  equiv-right-summand-equiv-binary-coproduct-Decomposition = {!!}

  map-equiv-right-summand-equiv-binary-coproduct-Decomposition :
    right-summand-binary-coproduct-Decomposition X →
    right-summand-binary-coproduct-Decomposition Y
  map-equiv-right-summand-equiv-binary-coproduct-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : binary-coproduct-Decomposition l2 l3 A)
  where

  id-equiv-binary-coproduct-Decomposition :
    equiv-binary-coproduct-Decomposition X X
  pr1 id-equiv-binary-coproduct-Decomposition = {!!}

  is-torsorial-equiv-binary-coproduct-Decomposition :
    is-torsorial (equiv-binary-coproduct-Decomposition X)
  is-torsorial-equiv-binary-coproduct-Decomposition = {!!}

  equiv-eq-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) → (X ＝ Y) →
    equiv-binary-coproduct-Decomposition X Y
  equiv-eq-binary-coproduct-Decomposition .X refl = {!!}

  is-equiv-equiv-eq-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) →
    is-equiv (equiv-eq-binary-coproduct-Decomposition Y)
  is-equiv-equiv-eq-binary-coproduct-Decomposition = {!!}

  extensionality-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) →
    (X ＝ Y) ≃ equiv-binary-coproduct-Decomposition X Y
  pr1 (extensionality-binary-coproduct-Decomposition Y) = {!!}
  pr2 (extensionality-binary-coproduct-Decomposition Y) = {!!}

  eq-equiv-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) →
    equiv-binary-coproduct-Decomposition X Y → (X ＝ Y)
  eq-equiv-binary-coproduct-Decomposition Y = {!!}
```

### Equivalence between `X → Fin 2` and `binary-coproduct-Decomposition l1 l1 X`

```agda
module _
  {l1 : Level}
  (X : UU l1)
  where

  module _
    (f : X → Fin 2)
    where

    matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
      (X ≃ ((fiber f (inl (inr star))) + (fiber f (inr star))))
    matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ = {!!}

    compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
      (x : X) →
      (inl (inr star) ＝ f x) →
      Σ ( Σ ( fiber f (inl (inr star)))
            ( λ y →
              inl y ＝
              ( map-equiv
                ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ)
                ( x))))
        ( λ z → pr1 (pr1 z) ＝ x)
    compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
      x p = {!!}

    compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕ :
      (y : fiber f (inl (inr star))) →
      pr1 y ＝
      map-inv-equiv
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ)
        ( inl y)
    compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕ
      y = {!!}

    compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
      (x : X) →
      (inr star ＝ f x) →
      Σ ( Σ ( fiber f (inr star))
            ( λ y →
              inr y ＝
              ( map-equiv
                ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ)
                ( x))))
        ( λ z → pr1 (pr1 z) ＝ x)
    compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
      x p = {!!}

    compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕ :
      (y : fiber f (inr star)) →
      pr1 y ＝
      map-inv-equiv
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ)
        ( inr y)
    compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕ
      y = {!!}

    map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
      binary-coproduct-Decomposition l1 l1 X
    pr1 (map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ) = {!!}
    pr1 (pr2 (map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ)) = {!!}
    pr2 (pr2 (map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ)) = {!!}

  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    ( left-summand-binary-coproduct-Decomposition d +
      right-summand-binary-coproduct-Decomposition d) →
    Fin 2
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    d (inl _) = {!!}
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    d (inr _) = {!!}

  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    X → Fin 2
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d x = {!!}

  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (t :
      ( left-summand-binary-coproduct-Decomposition d) +
      ( right-summand-binary-coproduct-Decomposition d)) →
    ( inl (inr star) ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
        ( d)
        ( t)) →
    Σ ( left-summand-binary-coproduct-Decomposition d)
      ( λ a → inl a ＝ t)
  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    d (inl y) x = {!!}

  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (x : X) →
    ( inl (inr star) ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d x) →
    Σ ( left-summand-binary-coproduct-Decomposition d)
      ( λ a →
        inl a ＝
        map-equiv (matching-correspondence-binary-coproduct-Decomposition d) x)
  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d x p = {!!}

  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (t :
      ( left-summand-binary-coproduct-Decomposition d) +
      ( right-summand-binary-coproduct-Decomposition d)) →
    ( inr star ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
        ( d)
        ( t)) →
    Σ ( right-summand-binary-coproduct-Decomposition d)
      ( λ a → inr a ＝ t)
  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    d (inr y) x = {!!}

  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (x : X) →
    ( inr star ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d x) →
    Σ ( right-summand-binary-coproduct-Decomposition d)
      ( λ a →
        inr a ＝
        map-equiv (matching-correspondence-binary-coproduct-Decomposition d) x)
  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d x p = {!!}

  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper :
    (f : X → Fin 2) →
    (x : X) →
    (v : (inl (inr star) ＝ f x) + (inr star ＝ f x)) →
    ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
        ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ f) x ＝
      f x)
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    f x (inl y) = {!!}
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    f x (inr y) = {!!}

  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ ∘
      map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ) ~
    id
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    f = {!!}

  equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    left-summand-binary-coproduct-Decomposition
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d)) ≃
    left-summand-binary-coproduct-Decomposition d
  equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d = {!!}

  equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    right-summand-binary-coproduct-Decomposition
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d)) ≃
    right-summand-binary-coproduct-Decomposition d
  equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d = {!!}

  compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( inl ∘
      ( map-equiv
        ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
          ( d)))) ~
    ( ( map-equiv
        ( matching-correspondence-binary-coproduct-Decomposition d)) ∘ pr1)
  compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d (x , p) = {!!}

  compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( inr ∘
      ( map-equiv
        ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
          ( d)))) ~
    ( map-equiv
      ( matching-correspondence-binary-coproduct-Decomposition d) ∘ pr1)
  compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d (x , p) = {!!}

  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( x : X) →
    ( ( inl (inr star) ＝
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
          ( d)
          ( x))) +
      ( inr star ＝
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
          ( d)
          ( x)))) →
    ( map-coprod
        ( map-equiv
          ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
            ( d)))
        ( map-equiv
          ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
            ( d))) ∘
      map-equiv
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
          ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d)))
      ( x) ＝
    map-equiv (matching-correspondence-binary-coproduct-Decomposition d) x
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    d x (inl p) = {!!}
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helper
    d x (inr p) = {!!}

  value-map-into-Fin-Two-ℕ-eq-zero-or-one-helper :
    (y : Fin 2) → (inl (inr star) ＝ y) + (inr star ＝ y)
  value-map-into-Fin-Two-ℕ-eq-zero-or-one-helper (inl x) = {!!}
  value-map-into-Fin-Two-ℕ-eq-zero-or-one-helper (inr x) = {!!}

  value-map-into-Fin-Two-ℕ-eq-zero-or-one :
    (f : X → Fin 2) →
    (x : X) →
    (inl (inr star) ＝ f x) + (inr star ＝ f x)
  value-map-into-Fin-Two-ℕ-eq-zero-or-one f x = {!!}

  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( map-coprod
        ( map-equiv
          ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
            ( d)))
        ( map-equiv
          ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
            ( d))) ∘
      map-equiv
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
          (map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
            ( d)))) ~
    map-equiv (matching-correspondence-binary-coproduct-Decomposition d)
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
    d x = {!!}

  is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ ∘
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ) ~
    id
  is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ d = {!!}

  is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    is-equiv map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ
  is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ = {!!}

  equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ :
    (X → Fin 2) ≃ binary-coproduct-Decomposition l1 l1 X
  pr1 equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ = {!!}
  pr2 equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ = {!!}
```
