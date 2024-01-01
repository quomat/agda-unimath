# Orbits of permutations

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.orbits-permutations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import finite-group-theory.transpositions

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-equivalence-relations
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterating-functions
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.repetitions-of-values
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The orbit of a point `x` for a permutation `f` is the set of point obtained by
iterating `f` on `x`.

## Definition

### The groupoid of iterative orbits of an automorphism on a finite set

```agda
module _
  {l : Level} (X : 𝔽 l) (e : type-𝔽 X ≃ type-𝔽 X)
  where

  iso-iterative-groupoid-automorphism-𝔽 : (x y : type-𝔽 X) → UU l
  iso-iterative-groupoid-automorphism-𝔽 x y = {!!}

  natural-isomorphism-iterative-groupoid-automorphism-𝔽 :
    (x y : type-𝔽 X) (f : iso-iterative-groupoid-automorphism-𝔽 x y) → ℕ
  natural-isomorphism-iterative-groupoid-automorphism-𝔽 = {!!}

  id-iso-iterative-groupoid-automorphism-𝔽 :
    (x : type-𝔽 X) → iso-iterative-groupoid-automorphism-𝔽 x x
  id-iso-iterative-groupoid-automorphism-𝔽 = {!!}

  comp-iso-iterative-groupoid-automorphism-𝔽 :
    {x y z : type-𝔽 X} →
    iso-iterative-groupoid-automorphism-𝔽 y z →
    iso-iterative-groupoid-automorphism-𝔽 x y →
    iso-iterative-groupoid-automorphism-𝔽 x z
  comp-iso-iterative-groupoid-automorphism-𝔽 = {!!}
  pr2 (comp-iso-iterative-groupoid-automorphism-𝔽 (pair n q) (pair m p)) = {!!}
```

## Properties

### For types equipped with a counting, orbits of permutations are finite

The map `i ↦ eⁱ a` repeats itself.

```agda
module _
  {l : Level} (X : UU l) (eX : count X) (f : Aut X) (a : X)
  where

  repetition-iterate-automorphism-Fin :
    repetition-of-values
      ( λ (k : Fin (succ-ℕ (number-of-elements-count eX))) →
        iterate
          ( nat-Fin (succ-ℕ (number-of-elements-count eX)) k)
          ( map-equiv f)
          ( a))
  repetition-iterate-automorphism-Fin = {!!}

  point1-iterate-ℕ : ℕ
  point1-iterate-ℕ = {!!}

  point2-iterate-ℕ : ℕ
  point2-iterate-ℕ = {!!}

  neq-points-iterate-ℕ : point1-iterate-ℕ ≠ point2-iterate-ℕ
  neq-points-iterate-ℕ p = {!!}

  two-points-iterate-ordered-ℕ :
    ( point1-iterate-ℕ ≤-ℕ point2-iterate-ℕ) +
    ( point2-iterate-ℕ ≤-ℕ point1-iterate-ℕ) →
    Σ ( ℕ)
      ( λ n →
        Σ ( ℕ)
          ( λ m →
            ( le-ℕ m n) ×
            ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
  two-points-iterate-ordered-ℕ = {!!}

  leq-greater-point-number-elements :
    ( p :
      ( point1-iterate-ℕ ≤-ℕ point2-iterate-ℕ) +
      ( point2-iterate-ℕ ≤-ℕ point1-iterate-ℕ)) →
    pr1 (two-points-iterate-ordered-ℕ p) ≤-ℕ number-of-elements-count eX
  leq-greater-point-number-elements = {!!}
  leq-greater-point-number-elements (inr p) = {!!}

  abstract
    min-repeating :
      minimal-element-ℕ
        ( λ n →
          Σ ( ℕ)
            ( λ m →
              ( le-ℕ m n) ×
              ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
    min-repeating = {!!}

    first-point-min-repeating : ℕ
    first-point-min-repeating = {!!}

    second-point-min-repeating : ℕ
    second-point-min-repeating = {!!}

    le-min-reporting : le-ℕ second-point-min-repeating first-point-min-repeating
    le-min-reporting = {!!}

    is-lower-bound-min-reporting :
      is-lower-bound-ℕ
        ( λ n →
          Σ ( ℕ)
            ( λ m →
              ( le-ℕ m n) ×
              ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
        ( first-point-min-repeating)
    is-lower-bound-min-reporting = {!!}

    same-image-iterate-min-reporting :
      Id ( iterate first-point-min-repeating (map-equiv f) a)
        ( iterate second-point-min-repeating (map-equiv f) a)
    same-image-iterate-min-reporting = {!!}

  leq-first-point-min-reporting-succ-number-elements :
    first-point-min-repeating ≤-ℕ (number-of-elements-count eX)
  leq-first-point-min-reporting-succ-number-elements = {!!}

  abstract
    not-not-eq-second-point-zero-min-reporting :
      ¬¬ (Id second-point-min-repeating zero-ℕ)
    not-not-eq-second-point-zero-min-reporting = {!!}

  has-finite-orbits-permutation' :
    is-decidable (Id second-point-min-repeating zero-ℕ) →
    Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  has-finite-orbits-permutation' = {!!}

  has-finite-orbits-permutation :
    Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  has-finite-orbits-permutation = {!!}

  leq-has-finite-orbits-permutation-number-elements :
    ( pr1 has-finite-orbits-permutation) ≤-ℕ (number-of-elements-count eX)
  leq-has-finite-orbits-permutation-number-elements = {!!}

  mult-has-finite-orbits-permutation :
    (k : ℕ) →
    Id (iterate (k *ℕ (pr1 has-finite-orbits-permutation)) (map-equiv f) a) a
  mult-has-finite-orbits-permutation = {!!}
```

### For finite types, the number of orbits-permutation of a permutation is finite

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n) (f : Aut (type-UU-Fin n X))
  where

  same-orbits-permutation : equivalence-relation l (type-UU-Fin n X)
  (pr1 same-orbits-permutation) a b = {!!}
  pr1 (pr2 same-orbits-permutation) _ = {!!}

  abstract
    is-decidable-same-orbits-permutation :
      ( a b : type-UU-Fin n X) →
      is-decidable (sim-equivalence-relation same-orbits-permutation a b)
    is-decidable-same-orbits-permutation = {!!}

  abstract
    is-decidable-is-in-equivalence-class-same-orbits-permutation :
      (T : equivalence-class same-orbits-permutation) →
      (a : type-UU-Fin n X) →
      is-decidable (is-in-equivalence-class same-orbits-permutation T a)
    is-decidable-is-in-equivalence-class-same-orbits-permutation = {!!}

  abstract
    has-finite-number-orbits-permutation :
      is-finite (equivalence-class same-orbits-permutation)
    has-finite-number-orbits-permutation = {!!}

  number-of-orbits-permutation : ℕ
  number-of-orbits-permutation = {!!}

  sign-permutation-orbit : Fin 2
  sign-permutation-orbit = {!!}
```

```agda
module _
  {l1 : Level} (X : UU l1) (eX : count X) (a b : X) (np : a ≠ b)
  where

  composition-transposition-a-b : (X ≃ X) → (X ≃ X)
  composition-transposition-a-b g = {!!}

  composition-transposition-a-b-involution :
    ( g : X ≃ X) →
    htpy-equiv
      ( composition-transposition-a-b (composition-transposition-a-b g))
      ( g)
  composition-transposition-a-b-involution = {!!}

  same-orbits-permutation-count : (X ≃ X) → equivalence-relation l1 X
  same-orbits-permutation-count = {!!}

  abstract
    minimal-element-iterate :
      (g : X ≃ X) (x y : X) → Σ ℕ (λ k → Id (iterate k (map-equiv g) x) y) →
      minimal-element-ℕ (λ k → Id (iterate k (map-equiv g) x) y)
    minimal-element-iterate = {!!}

  abstract
    minimal-element-iterate-nonzero :
      (g : X ≃ X) (x y : X) →
      Σ ℕ (λ k → is-nonzero-ℕ k × Id (iterate k (map-equiv g) x) y) →
      minimal-element-ℕ
        ( λ k → is-nonzero-ℕ k × Id (iterate k (map-equiv g) x) y)
    minimal-element-iterate-nonzero = {!!}

  abstract
    minimal-element-iterate-2 :
      (g : X ≃ X) (x y z : X) →
      Σ ( ℕ)
        ( λ k →
          ( Id (iterate k (map-equiv g) x) y) +
          ( Id (iterate k (map-equiv g) x) z)) →
      minimal-element-ℕ
        ( λ k →
          ( Id (iterate k (map-equiv g) x) y) +
          ( Id (iterate k (map-equiv g) x) z))
    minimal-element-iterate-2 = {!!}

  abstract
    equal-iterate-transposition :
      {l2 : Level} (x : X) (g : X ≃ X) (C : ℕ → UU l2)
      ( F :
        (k : ℕ) → C k →
        ( iterate k (map-equiv g) x ≠ a) ×
        ( iterate k (map-equiv g) x ≠ b))
      ( Ind :
        (n : ℕ) → C (succ-ℕ n) → is-nonzero-ℕ n → C n) →
      (k : ℕ) → (is-zero-ℕ k + C k) →
      Id
        ( iterate k (map-equiv (composition-transposition-a-b g)) x)
        ( iterate k (map-equiv g) x)
    equal-iterate-transposition = {!!}

  abstract
    conserves-other-orbits-transposition :
      (g : X ≃ X) (x y : X) →
      ¬ (sim-equivalence-relation (same-orbits-permutation-count g) x a) →
      ¬ (sim-equivalence-relation (same-orbits-permutation-count g) x b) →
      ( ( sim-equivalence-relation (same-orbits-permutation-count g) x y) ≃
        ( sim-equivalence-relation
          ( same-orbits-permutation-count (composition-transposition-a-b g))
          ( x)
          ( y)))
    conserves-other-orbits-transposition = {!!}

  conserves-other-orbits-transposition-quotient :
    (g : X ≃ X)
    (T : equivalence-class (same-orbits-permutation-count g)) →
    ¬ (is-in-equivalence-class (same-orbits-permutation-count g) T a) →
    ¬ (is-in-equivalence-class (same-orbits-permutation-count g) T b) →
    equivalence-class
      ( same-orbits-permutation-count (composition-transposition-a-b g))
  conserves-other-orbits-transposition-quotient = {!!}

  abstract
    not-same-orbits-transposition-same-orbits :
      ( g : X ≃ X)
      ( P :
        ( sim-equivalence-relation
          ( same-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( g))
          ( a)
          ( b))) →
      ¬ ( sim-equivalence-relation
          ( same-orbits-permutation-count (composition-transposition-a-b g))
          ( a)
          ( b))
    not-same-orbits-transposition-same-orbits = {!!}

  coprod-sim-equivalence-relation-a-b-Prop :
    ( g : X ≃ X) →
    ( P :
      sim-equivalence-relation
        ( same-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))
        ( a)
        ( b))
    (x : X) → Prop l1
  coprod-sim-equivalence-relation-a-b-Prop = {!!}

  abstract
    split-orbits-a-b-transposition :
      (g : X ≃ X) →
      (P :
        sim-equivalence-relation
          ( same-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( g))
          ( a)
          ( b))
      (x : X) →
      ( ( sim-equivalence-relation (same-orbits-permutation-count g) x a) ≃
        ( ( sim-equivalence-relation
            ( same-orbits-permutation-count (composition-transposition-a-b g))
            ( x)
            ( a)) +
          ( sim-equivalence-relation
            ( same-orbits-permutation-count
              ( composition-transposition-a-b g))
            ( x)
            ( b))))
    split-orbits-a-b-transposition = {!!}

  private
    module _
      ( g : X ≃ X)
      ( P :
        sim-equivalence-relation
          ( same-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( g))
          ( a)
          ( b))
      ( h :
        count
          ( equivalence-class
            ( same-orbits-permutation
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX)))
              ( g))))
      where

      h'-inl :
        ( k : Fin (number-of-elements-count h))
        ( T : equivalence-class (same-orbits-permutation-count g)) →
        Id (map-equiv-count h k) T →
        is-decidable
          ( is-in-equivalence-class (same-orbits-permutation-count g) T a) →
        is-decidable
          ( is-in-equivalence-class (same-orbits-permutation-count g) T b) →
        equivalence-class
          ( same-orbits-permutation-count (composition-transposition-a-b g))
      h'-inl = {!!}
      h'-inl k T p (inr nq) (inl r) = {!!}
      h'-inl k T p (inr nq) (inr nr) = {!!}
      h' :
        Fin (succ-ℕ (number-of-elements-count h)) →
        equivalence-class
          ( same-orbits-permutation-count (composition-transposition-a-b g))

      h' (inl k) = {!!}
      h' (inr k) = {!!}

      cases-inv-h' :
        ( T :
          equivalence-class
          ( same-orbits-permutation-count (composition-transposition-a-b g))) →
        is-decidable
          ( is-in-equivalence-class
            ( same-orbits-permutation-count (composition-transposition-a-b g))
            ( T)
            ( a)) →
        is-decidable
          ( is-in-equivalence-class
            ( same-orbits-permutation-count (composition-transposition-a-b g))
            ( T)
            ( b)) →
        Fin (succ-ℕ (number-of-elements-count h))
      cases-inv-h' = {!!}
      cases-inv-h' T (inr NQ) (inl R) = {!!}

      inv-h' :
        ( T :
          equivalence-class
            ( same-orbits-permutation-count
              ( composition-transposition-a-b g))) →
        Fin (succ-ℕ (number-of-elements-count h))
      inv-h' = {!!}
      H-conserves :
        ( T :
          equivalence-class
            ( same-orbits-permutation-count (composition-transposition-a-b g)))
        ( NQ :
          ¬ ( is-in-equivalence-class
              ( same-orbits-permutation-count (composition-transposition-a-b g))
              ( T)
              ( a)))
        ( NR :
          ¬ ( is-in-equivalence-class
              ( same-orbits-permutation-count (composition-transposition-a-b g))
              ( T)
              ( b))) →
        is-equivalence-class (same-orbits-permutation-count g) (pr1 T)
      H-conserves = {!!}

      retraction-h'-inr-inr :
        ( T :
          equivalence-class
            ( same-orbits-permutation-count (composition-transposition-a-b g)))
        ( NQ :
          ¬ ( is-in-equivalence-class
              ( same-orbits-permutation-count (composition-transposition-a-b g))
              ( T)
              ( a)))
        ( NR :
          ¬ ( is-in-equivalence-class
              ( same-orbits-permutation-count (composition-transposition-a-b g))
              ( T)
              ( b))) →
        is-decidable
          ( is-in-equivalence-class
            ( same-orbits-permutation-count g)
            ( pair (pr1 T) (H-conserves T NQ NR))
            ( a)) →
        is-decidable
          ( is-in-equivalence-class
            ( same-orbits-permutation-count g)
            ( pair (pr1 T) (H-conserves T NQ NR))
            ( b)) →
        Id
          ( h' (inl (map-inv-equiv-count h
            ( pair
              ( pr1 T)
              ( tr
                ( λ f →
                  is-equivalence-class
                    ( same-orbits-permutation-count f)
                    ( pr1 T))
                { x = {!!}
                {y = g}
                ( eq-htpy-equiv (composition-transposition-a-b-involution g))
                ( pr2
                  ( conserves-other-orbits-transposition-quotient
                    (composition-transposition-a-b g) T NQ NR)))))))
          ( T)
      retraction-h'-inr-inr T NQ NR (inl Q') R' = {!!}

  transf-same-orbits-count :
    ( g : X ≃ X)
    ( P :
      sim-equivalence-relation
        ( same-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))
        ( a)
        ( b)) →
    count
      ( equivalence-class
        ( same-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))) →
      count
        ( equivalence-class
          ( same-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( composition-transposition-a-b g)))
  transf-same-orbits-count = {!!}

  abstract
    number-orbits-composition-transposition :
      ( g : X ≃ X)
      ( P :
        sim-equivalence-relation
          ( same-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( g))
          ( a)
          ( b)) →
      Id
        ( succ-ℕ
          ( number-of-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( g)))
        ( number-of-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( composition-transposition-a-b g))
    number-orbits-composition-transposition = {!!}

  abstract
    same-orbits-transposition-not-same-orbits :
      ( g : X ≃ X)
      ( NP :
        ¬ (sim-equivalence-relation (same-orbits-permutation-count g) a b)) →
        sim-equivalence-relation
          ( same-orbits-permutation-count (composition-transposition-a-b g))
          ( a)
          ( b)
    same-orbits-transposition-not-same-orbits = {!!}

  abstract
    number-orbits-composition-transposition' :
      ( g : X ≃ X)
      (NP :
        ¬ ( sim-equivalence-relation
            ( same-orbits-permutation
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX)))
              ( g))
            ( a)
            ( b))) →
      Id
        ( number-of-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))
        ( succ-ℕ
          ( number-of-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( composition-transposition-a-b g)))
    number-orbits-composition-transposition' = {!!}

  abstract
    opposite-sign-composition-transposition-count :
      (g : X ≃ X) →
      Id
        ( sign-permutation-orbit
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))
        ( succ-Fin
          ( 2)
          ( sign-permutation-orbit
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( composition-transposition-a-b g)))
    opposite-sign-composition-transposition-count = {!!}

module _
  {l : Level} (X : UU l) (eX : count X)
  where

  abstract
    sign-list-transpositions-count :
      ( li :
        list
          ( Σ ( X → Decidable-Prop l)
              ( λ P →
                has-cardinality 2 (Σ X (type-Decidable-Prop ∘ P))))) →
      Id
        ( iterate
          ( length-list li)
          ( succ-Fin 2)
          ( sign-permutation-orbit
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( id-equiv)))
        ( sign-permutation-orbit
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( permutation-list-transpositions li))
    sign-list-transpositions-count = {!!}
```
