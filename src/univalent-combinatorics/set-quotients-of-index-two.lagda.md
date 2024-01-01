# Set quotients of index `2`

```agda
{-# OPTIONS --lossy-unification #-}

module univalent-combinatorics.set-quotients-of-index-two where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (f : reflecting-map-equivalence-relation R (type-Set QR))
  (Uf : is-set-quotient R QR f)
  (eA : type-Set QR ≃ Fin 2) (h : A → A)
  (H : {x y : A} →
    sim-equivalence-relation R x y ↔ sim-equivalence-relation R (h x) (h y))
  (h' : type-Set QR → type-Set QR)
  (x : A)
  (P :
    h' (map-reflecting-map-equivalence-relation R f x) ＝
    map-reflecting-map-equivalence-relation R f (h x))
  where

  cases-coherence-square-maps-eq-one-value-emb-is-set-quotient :
    is-emb h' →
    (y : A) (k k' k'' : Fin 2) →
    map-equiv eA (h' (map-reflecting-map-equivalence-relation R f x)) ＝ k →
    map-equiv eA (h' (map-reflecting-map-equivalence-relation R f y)) ＝ k' →
    map-equiv eA (map-reflecting-map-equivalence-relation R f (h y)) ＝ k'' →
    h' (map-reflecting-map-equivalence-relation R f y) ＝
    map-reflecting-map-equivalence-relation R f (h y)
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotient H' y
    ( inl (inr _)) (inl (inr _)) k'' p q r = {!!}

  coherence-square-maps-eq-one-value-emb-is-set-quotient :
    is-emb h' →
    coherence-square-maps
      ( h)
      ( map-reflecting-map-equivalence-relation R f)
      ( map-reflecting-map-equivalence-relation R f)
      ( h')
  coherence-square-maps-eq-one-value-emb-is-set-quotient H' y = {!!}

  eq-equiv-eq-one-value-equiv-is-set-quotient :
    (P : is-equiv h) (Q : is-equiv h') →
    pair h' Q ＝ equiv-is-set-quotient R QR f R QR f Uf Uf ((h , P) , H)
  eq-equiv-eq-one-value-equiv-is-set-quotient P Q = {!!}
```
