# Arithmetic law for product decomposition and Π-decomposition

```agda
module foundation.arithmetic-law-product-and-pi-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-decompositions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.pi-decompositions
open import foundation.product-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Let `X` be a type, we have the following equivalence :

```text
  Σ ( (U , V , e) : Π-Decomposition X)
    ( binary-product-Decomposition U) ≃
  Σ ( (A , B , e) : binary-product-Decomposition X)
    ( Π-Decomposition A ×
      Π-Decomposition B )
```

We also show a computational rule to simplify the use of this equivalence.

## Propositions

### Product decompositions of the indexing type of a Π-decomposition are equivalent to Π-decomposition of the left and right summand of a product decomposition

```agda
module _
  {l : Level} {X : UU l}
  where

  private
    reassociate :
      Σ (Π-Decomposition l l X)
        ( λ d → binary-coproduct-Decomposition l l
          ( indexing-type-Π-Decomposition d)) ≃
        Σ ( UU l)
          ( λ A →
            Σ ( UU l)
              ( λ B →
                Σ ( Σ ( UU l) λ U → ( U ≃ (A + B)))
                  ( λ U → Σ (pr1 U → UU l) (λ Y → X ≃ Π (pr1 U) Y))))
    reassociate = {!!}

    reassociate' :
      Σ ( UU l)
        ( λ A →
          Σ ( UU l)
            ( λ B →
              Σ ( (A → UU l) × (B → UU l))
                ( λ (YA , YB) →
                  Σ ( Σ (UU l) (λ A' → A' ≃ Π A YA))
                    ( λ A' →
                      Σ ( Σ (UU l) (λ B' → B' ≃ Π B YB))
                        ( λ B' → X ≃ (pr1 A' × pr1 B')))))) ≃
      Σ ( binary-product-Decomposition l l X)
      ( λ d →
        Π-Decomposition l l
          ( left-summand-binary-product-Decomposition d) ×
        Π-Decomposition l l
          ( right-summand-binary-product-Decomposition d))
    reassociate' = {!!}

  equiv-binary-product-Decomposition-Π-Decomposition :
    Σ ( Π-Decomposition l l X)
      ( λ d →
        binary-coproduct-Decomposition l l (indexing-type-Π-Decomposition d)) ≃
    Σ ( binary-product-Decomposition l l X)
      ( λ d →
        Π-Decomposition l l
          ( left-summand-binary-product-Decomposition d) ×
        Π-Decomposition l l
          ( right-summand-binary-product-Decomposition d))

  equiv-binary-product-Decomposition-Π-Decomposition = {!!}

  module _
    ( D : Σ ( Π-Decomposition l l X)
            ( λ D →
              binary-coproduct-Decomposition
                l l
                ( indexing-type-Π-Decomposition D)))
    where

    private
      tr-total-equiv :
        {l1 l3 l4 : Level} {X Y : UU l1} (e : Y ≃ X) →
        (h : Id {A = Σ (UU l1) λ Y → Y ≃ X} (X , id-equiv) (Y , e)) →
        {C : (X : UU l1) → (X → UU l3) → UU l4} →
        {f : Σ (Y → UU l3) (λ Z → C Y Z)} →
        (x : X) →
        pr1
          ( tr
            ( λ Y →
              ( Σ ( pr1 Y → UU l3)
                  ( λ Z → C (pr1 Y) Z) →
                Σ ( X → UU l3)
                  ( λ Z → C X Z)))
            ( h)
            ( id)
            ( f))
          ( x) ＝
        pr1 f (map-inv-equiv e x)
      tr-total-equiv = {!!}

    compute-left-equiv-binary-product-Decomposition-Π-Decomposition :
      ( a : left-summand-binary-coproduct-Decomposition (pr2 D)) →
      cotype-Π-Decomposition
        ( pr1
          ( pr2
            ( map-equiv equiv-binary-product-Decomposition-Π-Decomposition
              ( D))))
        ( a) ＝
      cotype-Π-Decomposition
        ( pr1 D)
        ( map-inv-equiv
          ( matching-correspondence-binary-coproduct-Decomposition (pr2 D))
          ( inl a))
    compute-left-equiv-binary-product-Decomposition-Π-Decomposition = {!!}

    compute-right-equiv-binary-product-Decomposition-Π-Decomposition :
      ( b : right-summand-binary-coproduct-Decomposition (pr2 D)) →
      cotype-Π-Decomposition
        ( pr2
          ( pr2
            ( map-equiv equiv-binary-product-Decomposition-Π-Decomposition
              ( D))))
        ( b) ＝
      cotype-Π-Decomposition (pr1 D)
        ( map-inv-equiv
          ( matching-correspondence-binary-coproduct-Decomposition (pr2 D))
          ( inr b))
    compute-right-equiv-binary-product-Decomposition-Π-Decomposition = {!!}
```
