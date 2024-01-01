# Dirichlet exponentials of a species of types

```agda
module species.dirichlet-exponentials-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.arithmetic-law-product-and-pi-decompositions
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.dependent-binomial-theorem
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pi-decompositions
open import foundation.product-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import species.coproducts-species-of-types
open import species.dirichlet-products-species-of-types
open import species.equivalences-species-of-types
open import species.species-of-types
```

</details>

## Idea

The **Dirichlet exponential** of a species of types `S` is defined as follows:

```text
  X ↦ Σ ((U , V , e) : Π-Decomposition X),  Π (u : U) → S (V u).
```

## Definition

```agda
dirichlet-exponential-species-types :
  {l1 l2 : Level} → species-types l1 l2 → species-types l1 (lsuc l1 ⊔ l2)
dirichlet-exponential-species-types {l1} {l2} S X = {!!}
```

## Properties

### The Dirichlet exponential of the sum of a species is equivalent to the Dirichlet product of the exponential of the two species

```agda
module _
  {l1 l2 l3 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  where

  private
    reassociate :
      ( X : UU l1) →
      Σ ( Σ ( binary-product-Decomposition l1 l1 X)
            ( λ d →
              ( Π-Decomposition l1 l1
                ( left-summand-binary-product-Decomposition d)) ×
              ( Π-Decomposition l1 l1
                ( right-summand-binary-product-Decomposition d))))
        ( λ D →
          ( ( b : indexing-type-Π-Decomposition (pr1 (pr2 D))) →
            S ( cotype-Π-Decomposition (pr1 (pr2 D)) b)) ×
          ( ( b : indexing-type-Π-Decomposition (pr2 (pr2 D))) →
            T ( cotype-Π-Decomposition (pr2 (pr2 D)) b))) ≃
      dirichlet-product-species-types
        ( dirichlet-exponential-species-types S)
        ( dirichlet-exponential-species-types T)
        ( X)
    pr1 (reassociate X) ((d , dl , dr) , s , t) = {!!}

  equiv-dirichlet-exponential-sum-species-types :
    equiv-species-types
      ( dirichlet-exponential-species-types (coproduct-species-types S T))
      ( dirichlet-product-species-types
        ( dirichlet-exponential-species-types S)
        ( dirichlet-exponential-species-types T))
  equiv-dirichlet-exponential-sum-species-types X = {!!}
```
