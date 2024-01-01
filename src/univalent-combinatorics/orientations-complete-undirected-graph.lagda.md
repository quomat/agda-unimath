# Orientations of the complete undirected graph

```agda
{-# OPTIONS --lossy-unification #-}

module univalent-combinatorics.orientations-complete-undirected-graph where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.transpositions

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equivalence-relations
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.intersections-subtypes
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.symmetric-difference
```

</details>

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  orientation-Complete-Undirected-Graph : UU (lsuc l)
  orientation-Complete-Undirected-Graph = {!!}

  is-set-orientation-Complete-Undirected-Graph :
    is-set orientation-Complete-Undirected-Graph
  is-set-orientation-Complete-Undirected-Graph = {!!}

  2-Element-Decidable-Subtype-subtype-pointwise-difference :
    orientation-Complete-Undirected-Graph →
    orientation-Complete-Undirected-Graph →
    2-Element-Decidable-Subtype l (type-UU-Fin n X) → Decidable-Prop l
  pr1 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y) = {!!}
module _
  {l : Level} (n : ℕ)
  where
  map-orientation-complete-undirected-graph-equiv :
    (X X' : UU-Fin l n) →
    (type-UU-Fin n X ≃ type-UU-Fin n X') →
    orientation-Complete-Undirected-Graph n X →
    orientation-Complete-Undirected-Graph n X'
  pr1 (map-orientation-complete-undirected-graph-equiv X X' e d Y) = {!!}
```

</details>

```agda
module _
  {l : Level} {X : UU l}
  (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  cases-orientation-aut-count :
    (e : X ≃ X)
    ( Y : 2-Element-Decidable-Subtype l X)
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y →
          Σ (x ≠ y)
          ( λ np →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))
              ( Y))))) →
    is-decidable
      ( Id (map-equiv e (pr1 two-elements)) (pr1 two-elements)) →
    is-decidable
      ( Id (map-equiv e (pr1 (pr2 two-elements))) (pr1 (pr2 two-elements))) →
    Σ X (λ z → type-Decidable-Prop (pr1 Y z))
  cases-orientation-aut-count
    e Y (pair x (pair y (pair np P))) (inl q) r = {!!}

  orientation-aut-count :
    X ≃ X →
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  orientation-aut-count e Y = {!!}

  cases-orientation-two-elements-count :
    ( i j : X)
    ( Y : 2-Element-Decidable-Subtype l X)
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y →
          Σ (x ≠ y)
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    Σ X (λ z → type-Decidable-Prop (pr1 Y z))
  cases-orientation-two-elements-count
    i j Y (pair x (pair y (pair np' P))) (inl q) r s = {!!}

  orientation-two-elements-count :
    (i j : X) → i ≠ j →
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  orientation-two-elements-count i j np Y = {!!}

  first-element-count : X
  first-element-count = {!!}

  second-element-count : X
  second-element-count = {!!}

  abstract
    distinct-two-elements-count :
      first-element-count ≠ second-element-count
    distinct-two-elements-count p = {!!}

  canonical-2-Element-Decidable-Subtype-count :
    2-Element-Decidable-Subtype l X
  canonical-2-Element-Decidable-Subtype-count = {!!}

  canonical-orientation-count :
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  canonical-orientation-count = {!!}

  transitive-canonical-orientation-count :
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  transitive-canonical-orientation-count = {!!}

  abstract
    cases-inward-edge-left-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) i)) +
      ( ( Id (pr1 (two-elements-transposition eX Y)) i) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    cases-inward-edge-left-two-elements-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) = {!!}

    inward-edge-left-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y i)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    inward-edge-left-two-elements-orientation-count i j np Y x p1 p2 nq nr = {!!}

    cases-inward-edge-left-transposition-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) i)) +
      ( ( Id (pr1 (two-elements-transposition eX Y)) i) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    cases-inward-edge-left-transposition-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) = {!!}

        { y = {!!}
    cases-inward-edge-left-transposition-orientation-count
      i j np Y x nq nr (inr (pair r1 r2)) = {!!}

    inward-edge-left-transposition-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y i)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    inward-edge-left-transposition-orientation-count i j np Y x p1 p2 nq nr = {!!}

    cases-inward-edge-right-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) j)) +
      ( ( Id (pr1 (two-elements-transposition eX Y)) j) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    cases-inward-edge-right-two-elements-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) = {!!}

    inward-edge-right-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y j)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    inward-edge-right-two-elements-orientation-count i j np Y x p1 p2 nq nr = {!!}

    cases-inward-edge-right-transposition-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) j)) +
      ( ( Id (pr1 (two-elements-transposition eX Y)) j) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    cases-inward-edge-right-transposition-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) = {!!}

    inward-edge-right-transposition-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y j)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    inward-edge-right-transposition-orientation-count i j np Y x p1 p2 nq nr = {!!}

    cases-eq-orientation-two-elements-count :
      ( i j : X)
      ( np : i ≠ j)
      ( two-elements : Σ X
        ( λ x → Σ X
          ( λ y → Σ (x ≠ y)
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))))) →
      (q : is-decidable (Id (pr1 two-elements) i)) →
      (r : is-decidable (Id (pr1 two-elements) j)) →
      (s : is-decidable (Id (pr1 (pr2 two-elements)) i)) →
      (t : is-decidable (Id (pr1 (pr2 two-elements)) j)) →
      Id
        ( pr1
          ( cases-orientation-two-elements-count i j
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))
            ( two-elements)
            ( q)
            ( r)
            ( s)))
        ( j)
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inl q) r s (inl t) = {!!}

    eq-orientation-two-elements-count :
      (i j : X) (np : i ≠ j) →
      Id
        ( pr1
          ( orientation-two-elements-count i j np
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( j)
    eq-orientation-two-elements-count i j np = {!!}

  cases-eq-orientation-aut-orientation-two-elements-count-left :
    ( i j : X) (np : i ≠ j) →
    ( Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( j)) →
    ( Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (x ≠ y)
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    Id (two-elements-transposition eX Y) two-elements →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    is-decidable (Id (pr1 (pr2 two-elements)) j) →
    Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y)))
      ( pr1 (orientation-two-elements-count i j np Y))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inl t) = {!!}

  cases-eq-orientation-aut-orientation-two-elements-count-right :
    ( i j : X) (np : i ≠ j) →
    ( Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( i)) →
    ( Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (x ≠ y)
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    Id (two-elements-transposition eX Y) two-elements →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    is-decidable (Id (pr1 (pr2 two-elements)) j) →
    Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y)))
      ( pr1 (orientation-two-elements-count j i (np ∘ inv) Y))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inl t) = {!!}

  cases-eq-orientation-aut-orientation-two-elements-count :
    ( i j : X) (np : i ≠ j) →
    is-decidable
      ( Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( j)) →
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count i j np)) +
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count j i (np ∘ inv)))
  cases-eq-orientation-aut-orientation-two-elements-count i j np (inl q) = {!!}

  eq-orientation-aut-orientation-two-elements-count :
    ( i j : X) (np : i ≠ j) →
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
              ( np))))
      ( orientation-two-elements-count i j np)) +
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count j i (np ∘ inv)))
  eq-orientation-aut-orientation-two-elements-count i j np = {!!}

  cases-eq-map-orientation-transposition-orientation-two-elements-count :
    ( i j : X) (np : i ≠ j)
    ( Y : 2-Element-Decidable-Subtype l X)
    ( two-elements :
      Σ X
        ( λ x → Σ X
          ( λ y → Σ (x ≠ y)
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( Y))))) →
    Id (two-elements-transposition eX Y) two-elements →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    is-decidable (Id (pr1 (pr2 two-elements)) j) →
    Id
      ( pr1
        ( map-orientation-complete-undirected-graph-equiv
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( orientation-two-elements-count i j np)
          ( Y)))
      ( pr1 ( orientation-two-elements-count j i (np ∘ inv) Y))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inl q) r s (inl t) = {!!}

  eq-map-orientation-transposition-orientation-two-elements-count :
    ( i j : X) (np : i ≠ j) →
    Id
      ( map-orientation-complete-undirected-graph-equiv
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np)))
        ( orientation-two-elements-count i j np))
      ( orientation-two-elements-count j i (np ∘ inv))
  eq-map-orientation-transposition-orientation-two-elements-count i j np = {!!}

  equiv-fin-1-difference-orientation-two-elements-count :
    ( i j : X) (np : i ≠ j) →
    Fin 1 ≃
    Σ ( 2-Element-Decidable-Subtype l X)
      ( λ Y → type-Decidable-Prop
        ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( orientation-two-elements-count i j np)
          ( orientation-two-elements-count j i (np ∘ inv))
          ( Y)))
  pr1 (pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np) x) = {!!}

  eq-orientation-pointwise-difference-two-elements-count :
    (i j : X) (np : i ≠ j) →
    Id
      ( 1)
      ( number-of-elements-is-finite
        ( is-finite-subtype-pointwise-difference
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( orientation-two-elements-count i j np)
          ( orientation-two-elements-count j i (np ∘ inv))))
  eq-orientation-pointwise-difference-two-elements-count i j np = {!!}

  cases-not-even-difference-orientation-aut-transposition-count :
    ( i j : X) (np : i ≠ j) →
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count i j np)) +
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count j i (np ∘ inv))) →
    ¬ ( sim-equivalence-relation
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( map-orientation-complete-undirected-graph-equiv
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( transposition (standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np)))
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))))
  cases-not-even-difference-orientation-aut-transposition-count
    i j np (inl pl) = {!!}

  not-even-difference-orientation-aut-transposition-count :
    ( Y : 2-Element-Decidable-Subtype l X) →
    ¬ ( sim-equivalence-relation
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( orientation-aut-count (transposition Y))
      ( map-orientation-complete-undirected-graph-equiv
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( transposition Y)
        ( orientation-aut-count (transposition Y))))
  not-even-difference-orientation-aut-transposition-count Y = {!!}

  inv-orientation :
    ( T :
      quotient-sign
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
    is-decidable
      ( is-in-equivalence-class
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( canonical-orientation-count)) →
    Fin 2
  inv-orientation T (inl P) = {!!}

  equiv-fin-2-quotient-sign-count :
    Fin 2 ≃
    ( quotient-sign
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX))))
  pr1 equiv-fin-2-quotient-sign-count (inl (inr star)) = {!!}

module _
  {l : Level} (n : ℕ) (X : UU-Fin l n) (ineq : leq-ℕ 2 n)
  where

  equiv-fin-2-quotient-sign-equiv-Fin :
    (h : Fin n ≃ type-UU-Fin n X) → Fin 2 ≃ quotient-sign n X
  equiv-fin-2-quotient-sign-equiv-Fin h = {!!}
```
