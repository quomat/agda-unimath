# Products of Dirichlet series of species of types

```agda
module species.products-dirichlet-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.homotopies
open import foundation.postcomposition-functions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universal-property-cartesian-product-types
open import foundation.universe-levels

open import species.dirichlet-products-species-of-types
open import species.dirichlet-series-species-of-types
open import species.species-of-types
```

</details>

## Idea

The product of two Dirichlet series is the pointwise product.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (H : species-types l1 l2)
  (C1 : preserves-product-species-types H)
  (S : species-types l1 l3)
  (T : species-types l1 l4)
  (X : UU l5)
  where

  product-dirichlet-series-species-types : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  product-dirichlet-series-species-types = {!!}
```

## Properties

### The Dirichlet series associated to the Dirichlet product of `S` and `T` is equal to the product of theirs Dirichlet series

```agda
module _
  {l1 l2 l3 l4 : Level}
  (H : species-types l1 l2)
  (C1 : preserves-product-species-types H)
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  (X : UU l4)
  where

  private
    reassociate :
      dirichlet-series-species-types
        ( H)
        ( C1)
        ( dirichlet-product-species-types S T) X ≃
      Σ ( UU l1)
        ( λ A →
          Σ ( UU l1)
            ( λ B →
              Σ ( Σ ( UU l1) (λ F → F ≃ (A × B)))
                ( λ F → ((S A) × (T B)) × (X → H (pr1 F)))))
    reassociate = {!!}

    reassociate' :
      Σ ( UU l1)
        ( λ A → Σ (UU l1) (λ B → (S A × T B) × ((X → H A) × (X → H B)))) ≃
      product-dirichlet-series-species-types H C1 S T X
    reassociate' = {!!}

  equiv-dirichlet-series-dirichlet-product-species-types :
    dirichlet-series-species-types
      ( H)
      ( C1)
      ( dirichlet-product-species-types S T)
      ( X) ≃
    product-dirichlet-series-species-types H C1 S T X
  equiv-dirichlet-series-dirichlet-product-species-types = {!!}
```
