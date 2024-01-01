# Uniqueness of the truncations

```agda
module foundation.uniqueness-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

The universal property of `n`-truncations implies that `n`-truncations are
determined uniquely up to a unique equivalence.

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B)
  (C : Truncated-Type l3 k) (g : A → type-Truncated-Type C)
  {h : type-hom-Truncated-Type k B C} (H : (h ∘ f) ~ g)
  where

{-

  abstract
    is-equiv-is-truncation-is-truncation :
      is-truncation B f → is-truncation C g → is-equiv h
    is-equiv-is-truncation-is-truncation = {!!}

      is-equiv-is-invertible
        ( pr1 (center K))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Ug C)
            { h ∘ k}
            { id}
            ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
              ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
                ( ( eq-htpy-reflecting-map-equivalence-relation R C
                    ( precomp-Set-Quotient R B f C h) g H) ∙
                  ( inv (precomp-id-Set-Quotient R C g)))))))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Uf B)
            { k ∘ h}
            { id}
            ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
              ( ( ap
                  ( λ t → precomp-Set-Quotient R C t B k)
                  ( eq-htpy-reflecting-map-equivalence-relation R C
                    ( precomp-Set-Quotient R B f C h) g H)) ∙
                ( ( α) ∙
                  ( inv (precomp-id-Set-Quotient R B f)))))))
      where
      K : is-contr
            ( Σ ( type-hom-Set C B)
                ( λ h →
                  ( h ∘ map-reflecting-map-equivalence-relation R g) ~
                  ( map-reflecting-map-equivalence-relation R f)))
      K = {!!}
```

### Uniqueness of set truncations

```agda
{-
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C) {h : type-hom-Set B C}
  (H : (h ∘ f) ~ g)
  where

  abstract
    is-equiv-is-set-truncation-is-set-truncation :
      ({l : Level} → is-set-truncation l B f) →
      ({l : Level} → is-set-truncation l C g) →
      is-equiv h
    is-equiv-is-set-truncation-is-set-truncation = {!!}

  abstract
    is-set-truncation-is-equiv-is-set-truncation :
      ({l : Level} → is-set-truncation l C g) → is-equiv h →
      {l : Level} → is-set-truncation l B f
    is-set-truncation-is-equiv-is-set-truncation = {!!}

  abstract
    is-set-truncation-is-set-truncation-is-equiv :
      is-equiv h → ({l : Level} → is-set-truncation l B f) →
      {l : Level} → is-set-truncation l C g
    is-set-truncation-is-set-truncation-is-equiv = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C)
  (Sf : {l : Level} → is-set-truncation l B f)
  (Sg : {l : Level} → is-set-truncation l C g)
  where

  abstract
    uniqueness-set-truncation :
      is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ f) ~ g))
    uniqueness-set-truncation = {!!}

  equiv-uniqueness-set-truncation : type-Set B ≃ type-Set C
  equiv-uniqueness-set-truncation = {!!}

  map-equiv-uniqueness-set-truncation : type-Set B → type-Set C
  map-equiv-uniqueness-set-truncation = {!!}

  triangle-uniqueness-set-truncation :
    (map-equiv-uniqueness-set-truncation ∘ f) ~ g
  triangle-uniqueness-set-truncation = {!!}
-}
```
