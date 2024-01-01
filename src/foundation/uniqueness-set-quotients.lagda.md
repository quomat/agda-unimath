# The uniqueness of set quotients

```agda
module foundation.uniqueness-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.precomposition-functions
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The universal property of set quotients implies that set quotients are uniquely
unique.

## Properties

### Uniqueness of set quotients

```agda
precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (C : Set l4) (g : hom-Set B C)
  (D : Set l5) (h : hom-Set C D) →
  ( precomp-Set-Quotient R B f D (h ∘ g)) ＝
  ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C))
  {h : type-Set B → type-Set C}
  (H :
    (h ∘ map-reflecting-map-equivalence-relation R f) ~
    map-reflecting-map-equivalence-relation R g)
  where

  map-inv-is-equiv-is-set-quotient-is-set-quotient :
    is-set-quotient R B f →
    is-set-quotient R C g →
    type-Set C → type-Set B
  map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug = {!!}

  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ( Uf : is-set-quotient R B f) →
    ( Ug : is-set-quotient R C g) →
    ( h ∘ map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug) ~ id
  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug = {!!}

  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ( Uf : is-set-quotient R B f) →
    ( Ug : is-set-quotient R C g) →
    ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug ∘ h) ~ id
  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug = {!!}

  is-equiv-is-set-quotient-is-set-quotient :
    is-set-quotient R B f →
    is-set-quotient R C g →
    is-equiv h
  is-equiv-is-set-quotient-is-set-quotient Uf Ug = {!!}

  is-set-quotient-is-set-quotient-is-equiv :
    is-equiv h → is-set-quotient R B f → is-set-quotient R C g
  is-set-quotient-is-set-quotient-is-equiv E Uf {l} X = {!!}

  is-set-quotient-is-equiv-is-set-quotient :
    is-set-quotient R C g → is-equiv h → is-set-quotient R B f
  is-set-quotient-is-equiv-is-set-quotient Ug E {l} X = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (Uf : is-set-quotient R B f)
  (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C))
  (Ug : is-set-quotient R C g)
  where

  uniqueness-set-quotient :
    is-contr
      ( Σ ( type-Set B ≃ type-Set C)
          ( λ e →
            ( map-equiv e ∘ map-reflecting-map-equivalence-relation R f) ~
            ( map-reflecting-map-equivalence-relation R g)))
  uniqueness-set-quotient = {!!}

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient = {!!}

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient = {!!}

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘
      map-reflecting-map-equivalence-relation R f) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-uniqueness-set-quotient = {!!}
```
