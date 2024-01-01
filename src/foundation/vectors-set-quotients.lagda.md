# Vectors of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.vectors-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-products-set-quotients
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.multivariable-operations
open import foundation.products-equivalence-relations
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`. Then, the set quotient of a vector with these types is the vector
of the set quotients of each `Ai`.

## Definition

### The induced relation on the vector of types

```agda
all-sim-equivalence-relation :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  ( equivalence-relation l2 (multivariable-input n A))
all-sim-equivalence-relation = {!!}
all-sim-equivalence-relation (succ-ℕ n) A R = {!!}
```

### The set quotient of a vector of types

```agda
set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  UU (l1 ⊔ l2)
set-quotient-vector = {!!}

is-set-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  is-set (set-quotient-vector n A R)
is-set-set-quotient-vector = {!!}
is-set-set-quotient-vector (succ-ℕ n) A R = {!!}

set-quotient-vector-Set :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  Set (l1 ⊔ l2)
set-quotient-vector-Set = {!!}
pr2 (set-quotient-vector-Set n A R) = {!!}

quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  multivariable-input n A →
  set-quotient-vector n A R
quotient-vector-map = {!!}
pr1 (quotient-vector-map (succ-ℕ n) A R (a0 , a)) = {!!}
pr2 (quotient-vector-map (succ-ℕ n) A R a) = {!!}

reflects-quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  reflects-equivalence-relation
    ( all-sim-equivalence-relation n A R)
    ( quotient-vector-map n A R)
reflects-quotient-vector-map = {!!}
reflects-quotient-vector-map (succ-ℕ n) A R (p , p') = {!!}

reflecting-map-quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  reflecting-map-equivalence-relation
    ( all-sim-equivalence-relation n A R)
    ( set-quotient-vector n A R)
reflecting-map-quotient-vector-map = {!!}
pr2 (reflecting-map-quotient-vector-map n A R) = {!!}

equiv-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  set-quotient-vector n A R ≃ set-quotient (all-sim-equivalence-relation n A R)
equiv-set-quotient-vector = {!!}
pr1 (pr1 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = {!!}
pr2 (pr1 (pr2 (equiv-set-quotient-vector {l1} {l2} zero-ℕ A R))) = {!!}
pr1 (pr2 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = {!!}
pr2 (pr2 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) (map-raise star) = {!!}
equiv-set-quotient-vector (succ-ℕ n) A R = {!!}

map-equiv-equiv-set-quotient-vector-quotient-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  ( map-equiv (equiv-set-quotient-vector n A R) ∘
    ( quotient-vector-map n A R)) ~
  ( quotient-map (all-sim-equivalence-relation n A R))
map-equiv-equiv-set-quotient-vector-quotient-map = {!!}
map-equiv-equiv-set-quotient-vector-quotient-map (succ-ℕ n) A R (a0 , a) = {!!}

inv-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  (X : Set l) →
  reflecting-map-equivalence-relation
    ( all-sim-equivalence-relation n A R)
    ( type-Set X) →
  ((set-quotient-vector n A R) → type-Set X)
inv-precomp-vector-set-quotient = {!!}
inv-precomp-vector-set-quotient (succ-ℕ n) A R X f (qa0 , qa) = {!!}

abstract
  is-section-inv-precomp-vector-set-quotient :
    { l l1 l2 : Level}
    ( n : ℕ)
    ( A : functional-vec (UU l1) n)
    ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
    ( X : Set l) →
    ( precomp-Set-Quotient
      ( all-sim-equivalence-relation n A R)
      ( set-quotient-vector-Set n A R)
      ( reflecting-map-quotient-vector-map n A R)
      ( X)) ∘
    ( inv-precomp-vector-set-quotient n A R X) ~
    ( id)
  is-section-inv-precomp-vector-set-quotient = {!!}

section-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  ( X : Set l) →
  ( section
    ( precomp-Set-Quotient
      ( all-sim-equivalence-relation n A R)
      ( set-quotient-vector-Set n A R)
      ( reflecting-map-quotient-vector-map n A R)
      ( X)))
section-precomp-vector-set-quotient = {!!}
pr2 (section-precomp-vector-set-quotient n A R X) = {!!}

abstract
  is-retraction-inv-precomp-vector-set-quotient :
    { l l1 l2 : Level}
    ( n : ℕ)
    ( A : functional-vec (UU l1) n)
    ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
    ( X : Set l) →
    ( retraction
      ( precomp-Set-Quotient
        ( all-sim-equivalence-relation n A R)
        ( set-quotient-vector-Set n A R)
        ( reflecting-map-quotient-vector-map n A R)
        ( X)))
  is-retraction-inv-precomp-vector-set-quotient = {!!}

    set-quotient-vector-prod-set-quotient :
      ( set-quotient-vector (succ-ℕ n) A R) →
      ( prod-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
    set-quotient-vector-prod-set-quotient = {!!}

    map-inv-equiv-f :
      ( prod-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))) →
      ( type-Set X)
    map-inv-equiv-f = {!!}

    lemma-f : (map-inv-equiv-f ∘ set-quotient-vector-prod-set-quotient) ＝ f
    lemma-f = {!!}

    is-retraction-inv-precomp-f :
      ( inv-precomp-set-quotient-prod-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))
        ( X)
        ( precomp-Set-Quotient
          ( prod-equivalence-relation (R (inr star))
          ( all-sim-equivalence-relation n
            ( tail-functional-vec n A)
            ( λ x → R (inl x))))
          ( prod-set-quotient-Set
            ( R (inr star))
            ( all-sim-equivalence-relation n
              ( tail-functional-vec n A)
              ( λ x → R (inl x))))
            ( reflecting-map-prod-quotient-map (R (inr star))
            ( all-sim-equivalence-relation n
              ( tail-functional-vec n A)
              ( λ x → R (inl x))))
            ( X)
            ( map-inv-equiv-f))) ＝
      map-inv-equiv-f
    is-retraction-inv-precomp-f = {!!}

    is-inv-map-inv-equiv-f :
      ( inv-precomp-set-quotient-prod-set-quotient
      ( R (inr star))
      ( all-sim-equivalence-relation n
        ( tail-functional-vec n A)
        ( λ x → R (inl x)))
        ( X)
        ( precomp-f)) ＝
        map-inv-equiv-f
    is-inv-map-inv-equiv-f = {!!}

is-set-quotient-vector-set-quotient :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  is-set-quotient
    ( all-sim-equivalence-relation n A R)
    ( set-quotient-vector-Set n A R)
    ( reflecting-map-quotient-vector-map n A R)
is-set-quotient-vector-set-quotient = {!!}
pr2 (is-set-quotient-vector-set-quotient n A R X) = {!!}
```
