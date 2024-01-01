# Cauchy exponentials of species of types in a subuniverse

```agda
module species.cauchy-exponentials-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
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
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types-in-subuniverses
open import species.cauchy-exponentials-species-of-types
open import species.cauchy-products-species-of-types-in-subuniverses
open import species.coproducts-species-of-types
open import species.coproducts-species-of-types-in-subuniverses
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The **Cauchy exponential** of a species `S : P → Q` of types in subuniverse is
defined by

```text
  X ↦ Σ ((U , V , e) : Σ-Decomposition-subuniverse P X),  Π (u : U) → S (V u).
```

If `Q` is a global subuniverse, and if the previous definition is in `Q`, then
the Cauchy exponential is also a species of types in subuniverse from `P` to
`Q`.

## Definition

### The underlying type of the Cauchy exponential of species in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l))
  where

  type-cauchy-exponential-species-subuniverse :
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  type-cauchy-exponential-species-subuniverse S X = {!!}
```

### Subuniverses closed under the Cauchy exponential of a species in a subuniverse

```agda
is-closed-under-cauchy-exponential-species-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l)) →
  UUω
is-closed-under-cauchy-exponential-species-subuniverse {l1} {l2} P Q = {!!}
```

### The Cauchy exponential of a species of types in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-exponential-species-subuniverse P Q)
  where

  cauchy-exponential-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l3) →
    species-subuniverse P (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
  pr1 (cauchy-exponential-species-subuniverse S X) = {!!}
```

## Propositions

### The Cauchy exponential in term of composition

```agda
module _
  {l1 l2 l3 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-exponential-species-subuniverse P Q)
  (C2 : is-in-subuniverse (subuniverse-global-subuniverse Q lzero) unit)
  (C3 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C4 : is-closed-under-Σ-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (X : type-subuniverse P)
  where

  equiv-cauchy-exponential-composition-unit-species-subuniverse :
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ lzero ⊔ l3))
      ( cauchy-composition-species-subuniverse
        P Q C3 C4 (λ _ → unit , C2) S X) ≃
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-exponential-species-subuniverse P Q C1 S X)
  equiv-cauchy-exponential-composition-unit-species-subuniverse = {!!}
```

### Equivalence form with species of types

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-exponential-species-subuniverse P Q)
  ( C2 :
    ( U : UU l1) →
    ( V : U → UU l1) →
    ( (u : U) → is-in-subuniverse P (V u)) →
    is-in-subuniverse P (Σ U V) → is-in-subuniverse P U)
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  ( X : type-subuniverse P)
  where

  private
    reassociate :
      Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
        ( cauchy-exponential-species-subuniverse P Q C1 S)
        ( inclusion-subuniverse P X) ≃
      Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P X))
        ( λ (U , V , e) →
          Σ ( ( is-in-subuniverse P U × ((u : U) → is-in-subuniverse P (V u))) ×
              is-in-subuniverse P (inclusion-subuniverse P X))
            ( λ p → (u : U) → pr1 (S (V u , (pr2 (pr1 p)) u))))
    pr1 reassociate (pX , ((U , pU) , V , e) , s) = {!!}

    reassociate' :
      Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P X))
        ( λ d →
          Σ ( ( u : (indexing-type-Relaxed-Σ-Decomposition d)) →
              is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition d u))
            ( λ p →
              ( ( u : indexing-type-Relaxed-Σ-Decomposition d) →
                inclusion-subuniverse
                  ( subuniverse-global-subuniverse Q l3)
                  ( S (cotype-Relaxed-Σ-Decomposition d u , p u)))))
        ≃
        cauchy-exponential-species-types
          ( Σ-extension-species-subuniverse
              ( P)
              ( subuniverse-global-subuniverse Q l3)
              ( S))
        ( inclusion-subuniverse P X)
    pr1 reassociate' (d , pV , s) = {!!}

  equiv-cauchy-exponential-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-exponential-species-subuniverse P Q C1 S)
      ( inclusion-subuniverse P X) ≃
    cauchy-exponential-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( inclusion-subuniverse P X)
  equiv-cauchy-exponential-Σ-extension-species-subuniverse = {!!}
```

### The Cauchy exponential of the sum of a species is equivalent to the Cauchy product of the exponential of the two species

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2)
  ( Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-exponential-species-subuniverse P Q)
  ( C2 : is-closed-under-coproduct-species-subuniverse P Q)
  ( C3 : is-closed-under-cauchy-product-species-subuniverse P Q)
  ( C4 :
    ( U : UU l1) →
    ( V : U → UU l1) →
    ( (u : U) → is-in-subuniverse P (V u)) →
      ( is-in-subuniverse P (Σ U V)) →
      ( is-in-subuniverse P U))
  ( C5 : is-closed-under-coproducts-subuniverse P)
  ( C6 :
    ( A B : UU l1) →
    is-in-subuniverse P (A + B) →
    is-in-subuniverse P A × is-in-subuniverse P B)
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  ( T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  ( X : type-subuniverse P)
  where

  equiv-cauchy-exponential-sum-species-subuniverse :
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-exponential-species-subuniverse P Q C1
        ( coproduct-species-subuniverse P Q C2 S T) X) ≃
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-product-species-subuniverse P Q C3
        ( cauchy-exponential-species-subuniverse P Q C1 S)
        ( cauchy-exponential-species-subuniverse P Q C1 T)
        ( X))
  equiv-cauchy-exponential-sum-species-subuniverse = {!!}
```
