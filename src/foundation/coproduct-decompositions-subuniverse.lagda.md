# Coproduct decompositions in a subuniverse

```agda
module foundation.coproduct-decompositions-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Let `P` be a subuniverse and `X` a type in `P`. A binary coproduct decomposition
of `X` is defined to be two types `A` and `B` in `P` and an equivalence from `X`
to `A+B`.

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  binary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  binary-coproduct-Decomposition-subuniverse = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (d : binary-coproduct-Decomposition-subuniverse P X)
  where

  left-summand-binary-coproduct-Decomposition-subuniverse : type-subuniverse P
  left-summand-binary-coproduct-Decomposition-subuniverse = {!!}

  type-left-summand-binary-coproduct-Decomposition-subuniverse : UU l1
  type-left-summand-binary-coproduct-Decomposition-subuniverse = {!!}

  right-summand-binary-coproduct-Decomposition-subuniverse : type-subuniverse P
  right-summand-binary-coproduct-Decomposition-subuniverse = {!!}

  type-right-summand-binary-coproduct-Decomposition-subuniverse : UU l1
  type-right-summand-binary-coproduct-Decomposition-subuniverse = {!!}

  matching-correspondence-binary-coproduct-Decomposition-subuniverse :
    inclusion-subuniverse P X ≃
    ( type-left-summand-binary-coproduct-Decomposition-subuniverse +
      type-right-summand-binary-coproduct-Decomposition-subuniverse)
  matching-correspondence-binary-coproduct-Decomposition-subuniverse = {!!}
```

### Iterated binary coproduct decompositions

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  left-iterated-binary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  left-iterated-binary-coproduct-Decomposition-subuniverse = {!!}

  right-iterated-binary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  right-iterated-binary-coproduct-Decomposition-subuniverse = {!!}
```

### Ternary coproduct Decomposition-subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  ternary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  ternary-coproduct-Decomposition-subuniverse = {!!}

  module _
    (d : ternary-coproduct-Decomposition-subuniverse)
    where

    types-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P × (type-subuniverse P × type-subuniverse P)
    types-ternary-coproduct-Decomposition-subuniverse = {!!}

    first-summand-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P
    first-summand-ternary-coproduct-Decomposition-subuniverse = {!!}

    second-summand-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P
    second-summand-ternary-coproduct-Decomposition-subuniverse = {!!}

    third-summand-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P
    third-summand-ternary-coproduct-Decomposition-subuniverse = {!!}

    matching-correspondence-ternary-coproductuct-Decomposition-subuniverse :
      ( inclusion-subuniverse P X) ≃
      ( ( inclusion-subuniverse P
          first-summand-ternary-coproduct-Decomposition-subuniverse) +
        ( ( inclusion-subuniverse P
            second-summand-ternary-coproduct-Decomposition-subuniverse) +
          ( inclusion-subuniverse P
            third-summand-ternary-coproduct-Decomposition-subuniverse)))
    matching-correspondence-ternary-coproductuct-Decomposition-subuniverse = {!!}
```

## Propositions

### Characterization of equality of binary coproduct Decomposition of subuniverse

```agda
equiv-binary-coproduct-Decomposition-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (X : binary-coproduct-Decomposition-subuniverse P A)
  (Y : binary-coproduct-Decomposition-subuniverse P A) →
  UU (l1)
equiv-binary-coproduct-Decomposition-subuniverse = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (X : binary-coproduct-Decomposition-subuniverse P A)
  (Y : binary-coproduct-Decomposition-subuniverse P A)
  (e : equiv-binary-coproduct-Decomposition-subuniverse P A X Y)
  where

  equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A X ≃
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A Y
  equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse = {!!}

  map-equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A X →
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A Y
  map-equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse = {!!}

  equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A X ≃
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A Y
  equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse = {!!}

  map-equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A X →
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A Y
  map-equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (X : binary-coproduct-Decomposition-subuniverse P A)
  where

  id-equiv-binary-coproduct-Decomposition-subuniverse :
    equiv-binary-coproduct-Decomposition-subuniverse P A X X
  id-equiv-binary-coproduct-Decomposition-subuniverse = {!!}

  is-torsorial-equiv-binary-coproduct-Decomposition-subuniverse :
    is-torsorial (equiv-binary-coproduct-Decomposition-subuniverse P A X)
  is-torsorial-equiv-binary-coproduct-Decomposition-subuniverse = {!!}

  equiv-eq-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) → (X ＝ Y) →
    equiv-binary-coproduct-Decomposition-subuniverse P A X Y
  equiv-eq-binary-coproduct-Decomposition-subuniverse = {!!}

  is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) →
    is-equiv (equiv-eq-binary-coproduct-Decomposition-subuniverse Y)
  is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverse = {!!}

  extensionality-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) →
    (X ＝ Y) ≃ equiv-binary-coproduct-Decomposition-subuniverse P A X Y
  extensionality-binary-coproduct-Decomposition-subuniverse = {!!}

  eq-equiv-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) →
    equiv-binary-coproduct-Decomposition-subuniverse P A X Y → (X ＝ Y)
  eq-equiv-binary-coproduct-Decomposition-subuniverse = {!!}
```

### Equivalence between binary coproduct Decomposition-subuniverse induce by commutativiy of coproduct

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  equiv-commutative-binary-coproduct-Decomposition-subuniverse :
    binary-coproduct-Decomposition-subuniverse P X ≃
    binary-coproduct-Decomposition-subuniverse P X
  equiv-commutative-binary-coproduct-Decomposition-subuniverse = {!!}
```

### Equivalence between iterated coproduct and ternary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-closed-under-coproducts-subuniverse P)
  where

  private
    map-reassociate-left-iterated-coproduct-Decomposition-subuniverse :
      left-iterated-binary-coproduct-Decomposition-subuniverse P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  ( inclusion-subuniverse P A) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x))))
    map-reassociate-left-iterated-coproduct-Decomposition-subuniverse
      ( (A , B , e) , C , D , f) = {!!}

    map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverse :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x)))) →
      left-iterated-binary-coproduct-Decomposition-subuniverse P X
    map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverse
      ( (B , C , D) , (A , f) , e) = {!!}

    equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverse :
      left-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x))))
    equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverse = {!!}

  equiv-ternary-left-iterated-coproduct-Decomposition-subuniverse :
    left-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
    ternary-coproduct-Decomposition-subuniverse P X
  equiv-ternary-left-iterated-coproduct-Decomposition-subuniverse = {!!}

  private
    map-reassociate-right-iterated-coproduct-Decomposition-subuniverse :
      right-iterated-binary-coproduct-Decomposition-subuniverse P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  ( inclusion-subuniverse P B) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B))))
    map-reassociate-right-iterated-coproduct-Decomposition-subuniverse
      ( (A , B , e) , C , D , f) = {!!}

    map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverse :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  ( inclusion-subuniverse P B) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B)))) →
      right-iterated-binary-coproduct-Decomposition-subuniverse P X
    map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverse
      ( (A , C , D) , (B , f) , e) = {!!}

    equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverse :
      right-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  ( inclusion-subuniverse P B) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B))))
    equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverse = {!!}

  equiv-ternary-right-iterated-coproduct-Decomposition-subuniverse :
    right-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
    ternary-coproduct-Decomposition-subuniverse P X
  equiv-ternary-right-iterated-coproduct-Decomposition-subuniverse = {!!}
```

### Coproduct-decomposition with empty right summand

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-in-subuniverse P (raise-empty l1))
  where

  equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverse :
    Σ ( binary-coproduct-Decomposition-subuniverse P X)
      ( λ d →
        is-empty
          ( inclusion-subuniverse P
            ( right-summand-binary-coproduct-Decomposition-subuniverse
              P X d))) ≃
    Σ ( type-subuniverse P)
      ( λ Y → inclusion-subuniverse P X ≃ pr1 Y)
  equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverse = {!!}
```
