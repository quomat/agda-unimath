# Ethane

```agda
module organic-chemistry.ethane where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import finite-group-theory.tetrahedra-in-3-space

open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs
open import graph-theory.walks-undirected-graphs

open import organic-chemistry.alkanes
open import organic-chemistry.hydrocarbons

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**Ethane** is the unique alkane with two carbons.

## Definition

```agda
module _
  (t : tetrahedron-in-3-space) (v : vertex-tetrahedron-in-3-space t)
  where

  vertex-ethane-𝔽 : 𝔽 lzero
  vertex-ethane-𝔽 = {!!}

  vertex-ethane : UU lzero
  vertex-ethane = {!!}

  edge-ethane-Prop : unordered-pair vertex-ethane → Prop lzero
  edge-ethane-Prop = {!!}

  edge-ethane : unordered-pair vertex-ethane → UU lzero
  edge-ethane = {!!}

  abstract
    is-prop-edge-ethane :
      (p : unordered-pair vertex-ethane) → is-prop (edge-ethane p)
    is-prop-edge-ethane = {!!}

  standard-edge-ethane-Prop : (c c' : vertex-ethane) → Prop lzero
  standard-edge-ethane-Prop = {!!}

  standard-edge-ethane : (c c' : vertex-ethane) → UU lzero
  standard-edge-ethane = {!!}

  abstract
    is-prop-standard-edge-ethane :
      (c c' : vertex-ethane) → is-prop (standard-edge-ethane c c')
    is-prop-standard-edge-ethane = {!!}

  abstract
    is-decidable-edge-ethane-eq-Fin-two :
      (p : unordered-pair vertex-ethane) →
      type-unordered-pair p ＝ Fin 2 →
      is-decidable (edge-ethane p)
    is-decidable-edge-ethane-eq-Fin-two p refl with
      is-zero-or-one-Fin-two-ℕ (element-unordered-pair p (zero-Fin 1)) |
      is-zero-or-one-Fin-two-ℕ (element-unordered-pair p (one-Fin 1))
    ... | inl is-zero | inl is-zero' = {!!}
    ... | inl is-zero | inr is-one' = {!!}
    ... | inr is-one | inl is-zero' = {!!}
    ... | inr is-one | inr is-one' = {!!}

  is-decidable-standard-edge-ethane :
    (c c' : vertex-ethane) → is-decidable (standard-edge-ethane c c')
  is-decidable-standard-edge-ethane = {!!}

  abstract
    is-finite-edge-ethane :
      (p : unordered-pair vertex-ethane) → is-finite (edge-ethane p)
    is-finite-edge-ethane = {!!}

  edge-ethane-𝔽 : unordered-pair vertex-ethane → 𝔽 lzero
  edge-ethane-𝔽 = {!!}

  finite-graph-ethane : Undirected-Graph-𝔽 lzero lzero
  finite-graph-ethane = {!!}

  bonding-ethane :
    (c : vertex-ethane) →
    Σ (vertex-ethane) (λ c' → standard-edge-ethane c c') →
    vertex-tetrahedron-in-3-space t
  bonding-ethane = {!!}

  abstract
    is-torsorial-standard-edge-ethane :
      (c : vertex-ethane) → is-torsorial (λ c' → standard-edge-ethane c c')
    is-torsorial-standard-edge-ethane = {!!}

  abstract
    is-emb-bonding-ethane : (c : vertex-ethane) → is-emb (bonding-ethane c)
    is-emb-bonding-ethane = {!!}

  emb-bonding-ethane :
    (c : vertex-ethane) →
    Σ (vertex-ethane) (λ c' → standard-edge-ethane c c') ↪
    vertex-tetrahedron-in-3-space t
  emb-bonding-ethane = {!!}

  count-standard-edge-ethane :
    (c c' : vertex-ethane) → count (standard-edge-ethane c c')
  count-standard-edge-ethane = {!!}

  abstract
    number-of-elements-count-standard-edge-ethane-leq-3 :
      (c c' : vertex-ethane) →
      number-of-elements-count (count-standard-edge-ethane c c') ≤-ℕ 3
    number-of-elements-count-standard-edge-ethane-leq-3 = {!!}
    number-of-elements-count-standard-edge-ethane-leq-3
      (inl (inr _)) (inr _) = {!!}
    number-of-elements-count-standard-edge-ethane-leq-3
      (inr _) (inl (inr _)) = {!!}
    number-of-elements-count-standard-edge-ethane-leq-3
      (inr _) (inr _) = {!!}

  ethane : hydrocarbon lzero lzero
  ethane = {!!}

  is-alkane-ethane : is-alkane-hydrocarbon ethane
  is-alkane-ethane = {!!}
```
