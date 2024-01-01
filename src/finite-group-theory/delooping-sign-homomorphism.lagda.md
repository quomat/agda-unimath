# Deloopings of the sign homomorphism

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.delooping-sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.action-on-equivalences-type-families-over-subuniverses
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-induction
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.uniqueness-set-quotients
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.generating-sets-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-generated-subgroups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.symmetric-groups

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.set-quotients-of-index-two
open import univalent-combinatorics.standard-finite-types
```

</details>

## Ideas

The delooping of a group homomorphism `f : G → H` is a pointed map
`Bf : BG → BH` equiped with an homotopy witnessing that the following square
commutes :

```text
        f
  G --------> H
  |           |
 ≅|           |≅
  |           |
  v           v
  BG ------> BH
       ΩBf
```

In this file, we study the delooping of the sign homomorphism, and, more
precisely, how to detect that a pointed map between `BSn` and `BS2` is a
delooping of the sign homomorphism.

## Definition

### Construction of the delooping of the sign homomorphism with quotients (Corollary 25)

```agda
module _
  { l1 l2 l3 : Level}
  ( D : (n : ℕ) (X : UU-Fin l1 n) → UU l2)
  ( R : (n : ℕ) (X : UU-Fin l1 n) → equivalence-relation l3 (D n X))
  ( is-decidable-R :
    (n : ℕ) → leq-ℕ 2 n → (X : UU-Fin l1 n)
    (a b : D n X) → is-decidable (sim-equivalence-relation (R n X) a b))
  ( equiv-D/R-fin-2-equiv :
    (n : ℕ) (X : UU-Fin l1 n) →
    leq-ℕ 2 n → Fin n ≃ type-UU-Fin n X →
    Fin 2 ≃ equivalence-class (R n X))
  ( quotient-aut-succ-succ-Fin : (n : ℕ) →
    ( raise-Fin l1 (n +ℕ 2) ≃ raise-Fin l1 (n +ℕ 2)) →
    D ( n +ℕ 2)
      ( raise-Fin l1 (n +ℕ 2) ,
        unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2))))
  ( not-R-transposition-fin-succ-succ : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l1 (raise-Fin l1 (n +ℕ 2))) →
    ¬ ( sim-equivalence-relation
      ( R
        ( n +ℕ 2)
        ( raise-Fin l1 (n +ℕ 2) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2))))
      ( quotient-aut-succ-succ-Fin n (transposition Y))
      ( map-equiv
        ( action-equiv-family-over-subuniverse
          ( mere-equiv-Prop (Fin (n +ℕ 2)))
          ( D (n +ℕ 2))
          ( raise l1 (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
          ( raise l1 (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
          ( transposition Y))
        ( quotient-aut-succ-succ-Fin n (transposition Y)))))
  where

  private
    l4 : Level
    l4 = {!!}

    eq-counting-equivalence-class-R :
      (n : ℕ) →
      equivalence-class (R (n +ℕ 2) (Fin-UU-Fin l1 (n +ℕ 2))) ＝
      raise (l2 ⊔ lsuc l3) (Fin 2)
    eq-counting-equivalence-class-R = {!!}

    invertible-action-D-equiv :
      (n : ℕ) (X X' : UU-Fin l1 n) →
      type-UU-Fin n X ≃ type-UU-Fin n X' → D n X ≃ D n X'
    invertible-action-D-equiv = {!!}

    preserves-id-equiv-invertible-action-D-equiv :
      (n : ℕ) (X : UU-Fin l1 n) →
      Id (invertible-action-D-equiv n X X id-equiv) id-equiv
    preserves-id-equiv-invertible-action-D-equiv = {!!}

    abstract
      preserves-R-invertible-action-D-equiv :
        ( n : ℕ) →
        ( X X' : UU-Fin l1 n)
        ( e : type-UU-Fin n X ≃ type-UU-Fin n X') →
        ( a a' : D n X) →
        ( sim-equivalence-relation (R n X) a a' ↔
          sim-equivalence-relation
            ( R n X')
            ( map-equiv (invertible-action-D-equiv n X X' e) a)
            ( map-equiv (invertible-action-D-equiv n X X' e) a'))
      preserves-R-invertible-action-D-equiv = {!!}

    raise-UU-Fin-Fin : (n : ℕ) → UU-Fin l1 n
    raise-UU-Fin-Fin = {!!}

    that-thing :
      (n : ℕ) →
      Fin 2 ≃ equivalence-class (R (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)))
    that-thing = {!!}

    quotient-loop-Fin :
      (n : ℕ) → type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) →
      ( D (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)) ≃
        D (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)))
    quotient-loop-Fin = {!!}

    map-quotient-loop-Fin :
      (n : ℕ) → type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) →
      D (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)) →
      D (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2))
    map-quotient-loop-Fin = {!!}

    quotient-set-Fin : (n : ℕ) → Set l4
    quotient-set-Fin = {!!}

    quotient-map-quotient-Fin :
      (n : ℕ) → D n (raise-UU-Fin-Fin n) → type-Set (quotient-set-Fin n)
    quotient-map-quotient-Fin = {!!}

    quotient-reflecting-map-quotient-Fin :
      (n : ℕ) →
      reflecting-map-equivalence-relation
        ( R n (raise-UU-Fin-Fin n))
        ( type-Set (quotient-set-Fin n))
    quotient-reflecting-map-quotient-Fin = {!!}

  mere-equiv-D/R-fin-2 :
    (n : ℕ) (X : UU-Fin l1 n) →
    leq-ℕ 2 n → mere-equiv (Fin 2) (equivalence-class (R n X))
  mere-equiv-D/R-fin-2 = {!!}

  map-quotient-delooping-sign :
    (n : ℕ) →
    classifying-type-Concrete-Group (UU-Fin-Group l1 n) →
    classifying-type-Concrete-Group (UU-Fin-Group l4 2)
  map-quotient-delooping-sign = {!!}

  quotient-delooping-sign :
    (n : ℕ) → hom-Concrete-Group (UU-Fin-Group l1 n) (UU-Fin-Group l4 2)
  quotient-delooping-sign = {!!}

  map-quotient-delooping-sign-loop :
    ( n : ℕ)
    ( X Y : UU l1) →
    ( eX : mere-equiv (Fin (n +ℕ 2)) X) →
    ( eY : mere-equiv (Fin (n +ℕ 2)) Y) →
    Id X Y →
    Id
      ( equivalence-class (R (n +ℕ 2) (X , eX)))
      ( equivalence-class (R (n +ℕ 2) (Y , eY)))
  map-quotient-delooping-sign-loop = {!!}

  private
    map-quotient-delooping-sign-loop-Fin :
      ( n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) →
      type-Group (loop-group-Set (quotient-set-Fin (n +ℕ 2)))
    map-quotient-delooping-sign-loop-Fin = {!!}

  quotient-delooping-sign-loop :
    ( n : ℕ) →
    hom-Group
      ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
      ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
  quotient-delooping-sign-loop = {!!}

  abstract
    coherence-square-map-quotient-delooping-sign-loop-Set :
      ( n : ℕ)
      ( X Y : UU l1)
      ( eX : mere-equiv (Fin (n +ℕ 2)) X)
      ( eY : mere-equiv (Fin (n +ℕ 2)) Y)
      ( p : Id X Y) →
      ( Id (tr (mere-equiv (Fin (n +ℕ 2))) p eX) eY) →
      ( sX : is-set X)
      ( sY : is-set Y) →
      coherence-square-maps
        ( map-equiv
          ( invertible-action-D-equiv
            ( n +ℕ 2)
            ( Y , eY)
            ( X , eX)
            ( map-hom-symmetric-group-loop-group-Set (X , sX) (Y , sY) (p))))
        ( class (R (n +ℕ 2) (Y , eY)))
        ( class (R (n +ℕ 2) (X , eX)))
        ( map-equiv
          ( map-hom-symmetric-group-loop-group-Set
            ( equivalence-class-Set (R (n +ℕ 2) (X , eX)))
            ( equivalence-class-Set (R (n +ℕ 2) (Y , eY)))
            ( map-quotient-delooping-sign-loop n X Y eX eY p)))
    coherence-square-map-quotient-delooping-sign-loop-Set = {!!}

  coherence-square-map-quotient-delooping-sign-loop-Fin :
    (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
    coherence-square-maps
      ( map-quotient-loop-Fin n p)
      ( quotient-map-quotient-Fin (n +ℕ 2))
      ( quotient-map-quotient-Fin (n +ℕ 2))
      ( map-equiv
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-set-Fin (n +ℕ 2))
          ( quotient-set-Fin (n +ℕ 2))
          ( map-quotient-delooping-sign-loop-Fin n p)))
  coherence-square-map-quotient-delooping-sign-loop-Fin = {!!}

  private
    is-contr-equiv-quotient :
      ( n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
      is-contr
        ( Σ ( type-Group (symmetric-Group (quotient-set-Fin (n +ℕ 2))))
            ( λ h' →
              coherence-square-maps
                ( map-quotient-loop-Fin n p)
                ( quotient-map-quotient-Fin (n +ℕ 2))
                ( map-reflecting-map-equivalence-relation
                  ( R (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)))
                  ( quotient-reflecting-map-quotient-Fin (n +ℕ 2)))
                ( map-equiv h')))
    is-contr-equiv-quotient = {!!}

  abstract
    eq-quotient-delooping-sign-loop-equiv-is-set-quotient :
      (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
      Id
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-set-Fin (n +ℕ 2))
          ( quotient-set-Fin (n +ℕ 2))
          ( map-quotient-delooping-sign-loop-Fin n p))
        ( pr1 (center (is-contr-equiv-quotient n p)))
    eq-quotient-delooping-sign-loop-equiv-is-set-quotient = {!!}

  cases-map-quotient-aut-Fin :
    ( n : ℕ) →
    ( h : type-Group (symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))) →
    ( is-decidable
      ( sim-equivalence-relation
        ( R (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)))
        ( quotient-aut-succ-succ-Fin n h)
        ( map-equiv
          ( invertible-action-D-equiv
            (n +ℕ 2)
            ( raise-UU-Fin-Fin (n +ℕ 2))
            ( raise-UU-Fin-Fin (n +ℕ 2))
            ( h))
          ( quotient-aut-succ-succ-Fin n h)))) →
    type-Group (symmetric-Group (quotient-set-Fin (n +ℕ 2)))
  cases-map-quotient-aut-Fin = {!!}

  map-quotient-aut-Fin :
    (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set l1 (n +ℕ 2))) →
    type-Group (symmetric-Group (quotient-set-Fin (n +ℕ 2)))
  map-quotient-aut-Fin = {!!}

  eq-map-quotient-aut-fin-transposition :
    (n : ℕ) (Y : 2-Element-Decidable-Subtype l1 (raise l1 (Fin (n +ℕ 2)))) →
    Id
      ( map-quotient-aut-Fin n (transposition Y))
      ( that-thing n ∘e (equiv-succ-Fin 2 ∘e (inv-equiv (that-thing n))))
  eq-map-quotient-aut-fin-transposition = {!!}

  private
    this-third-thing :
      (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
      D ( n +ℕ 2)
        ( raise-Fin l1 (n +ℕ 2) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
    this-third-thing = {!!}

  cases-eq-map-quotient-aut-Fin :
    ( n : ℕ)
    ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))))
    ( D : is-decidable
      ( sim-equivalence-relation
        ( R (n +ℕ 2) (raise-UU-Fin-Fin (n +ℕ 2)))
        ( this-third-thing n p)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))) →
    ( k k' : Fin 2) →
    Id
      ( map-inv-equiv
        ( that-thing n)
        ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
      ( k) →
    Id
      ( map-inv-equiv
        ( that-thing n)
        ( quotient-map-quotient-Fin (n +ℕ 2)
          ( map-quotient-loop-Fin n p (this-third-thing n p))))
      ( k') →
    Id
      ( map-equiv
        ( cases-map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p))
          ( D))
        ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
      ( quotient-map-quotient-Fin (n +ℕ 2)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))
  cases-eq-map-quotient-aut-Fin = {!!}

  eq-map-quotient-aut-Fin :
    (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
    Id
      ( map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p)))
        ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
      ( quotient-map-quotient-Fin (n +ℕ 2)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))
  eq-map-quotient-aut-Fin = {!!}

  eq-map-quotient-aut-loop-equiv-is-set-quotient :
    (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
    Id
      ( map-quotient-aut-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( p)))
      ( pr1 (center (is-contr-equiv-quotient n p)))
  eq-map-quotient-aut-loop-equiv-is-set-quotient = {!!}

  eq-quotient-delooping-sign-loop-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( quotient-delooping-sign-loop n)
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
          ( comp-hom-Group
            ( symmetric-Group (Fin-Set 2))
            ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
            ( hom-inv-symmetric-group-loop-group-Set
              ( quotient-set-Fin (n +ℕ 2)))
            ( hom-symmetric-group-equiv-Set
              ( Fin-Set 2)
              ( quotient-set-Fin (n +ℕ 2))
              ( that-thing n)))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( compute-raise-Fin l1 (n +ℕ 2))))
  eq-quotient-delooping-sign-loop-sign-homomorphism = {!!}

  eq-quotient-delooping-loop-UU-Fin-Group :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group l4 2))
        ( hom-iso-Group
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group l4 2))
          ( comp-iso-Group
            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
            ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
            ( group-Concrete-Group (UU-Fin-Group l4 2))
            ( inv-iso-Group
              ( group-Concrete-Group (UU-Fin-Group l4 2))
              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
              ( iso-loop-group-fin-UU-Fin-Group l4 2))
            ( iso-loop-group-equiv-Set
              ( quotient-set-Fin (n +ℕ 2))
              ( raise-Set l4 (Fin-Set 2))
              ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n)))))
        ( quotient-delooping-sign-loop n))
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group l4 2))
        ( hom-group-hom-Concrete-Group
          ( UU-Fin-Group l1 (n +ℕ 2))
          ( UU-Fin-Group l4 2)
          ( quotient-delooping-sign (n +ℕ 2)))
        ( hom-iso-Group
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
          ( inv-iso-Group
            ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
            ( iso-loop-group-fin-UU-Fin-Group l1 (n +ℕ 2)))))
  eq-quotient-delooping-loop-UU-Fin-Group = {!!}

  symmetric-abstract-UU-fin-group-quotient-hom :
    (n : ℕ) →
    hom-Group
      ( symmetric-Group (Fin-Set 2))
      ( group-Concrete-Group (UU-Fin-Group l4 2))
  symmetric-abstract-UU-fin-group-quotient-hom = {!!}

  eq-quotient-delooping-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group l4 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group l4 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l1 (n +ℕ 2))
            ( UU-Fin-Group l4 2)
            ( quotient-delooping-sign (n +ℕ 2)))
          ( hom-inv-iso-Group
            ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
            ( iso-loop-group-fin-UU-Fin-Group l1 (n +ℕ 2))))
        ( hom-inv-symmetric-group-loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group l4 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( group-Concrete-Group (UU-Fin-Group l4 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom n)
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( compute-raise-Fin l1 (n +ℕ 2))))
  eq-quotient-delooping-sign-homomorphism = {!!}
```

### General case for the construction of the delooping of sign homomorphism (Proposition 22)

```agda
module _
  { l1 l2 : Level}
  ( Q : (n : ℕ) → UU-Fin l1 n → UU-Fin l2 2)
  ( equiv-Q-fin-fin-2 :
    (n : ℕ) →
    leq-ℕ 2 n →
    Fin 2 ≃
    ( type-UU-Fin 2
      ( Q n (raise l1 (Fin n) , unit-trunc-Prop (compute-raise-Fin l1 n)))))
  ( Q-transposition-swap : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l1 (raise-Fin l1 (n +ℕ 2))) →
    ( x : type-UU-Fin 2
      ( Q ( n +ℕ 2)
          ( raise l1 (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2))))) →
    ( x) ≠
    ( map-equiv
      ( action-equiv-family-over-subuniverse
        ( mere-equiv-Prop (Fin (n +ℕ 2)))
        ( type-UU-Fin 2 ∘ Q (n +ℕ 2))
        ( raise l1 (Fin (n +ℕ 2)) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
        ( raise l1 (Fin (n +ℕ 2)) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
        ( transposition Y))
      ( x)))
  where

  private
    equiv-Q-equivalence-class :
      (n : ℕ) (X : UU-Fin l1 n) →
      type-UU-Fin 2 (Q n X) ≃
      equivalence-class (Id-equivalence-relation (set-UU-Fin 2 (Q n X)))
    equiv-Q-equivalence-class = {!!}

    equiv-fin-2-equivalence-class :
      (n : ℕ) (X : UU-Fin l1 n) → leq-ℕ 2 n →
      Fin n ≃ type-UU-Fin n X →
      Fin 2 ≃ equivalence-class (Id-equivalence-relation (set-UU-Fin 2 (Q n X)))
    equiv-fin-2-equivalence-class = {!!}

  delooping-sign :
    (n : ℕ) → hom-Concrete-Group (UU-Fin-Group l1 n) (UU-Fin-Group (lsuc l2) 2)
  delooping-sign = {!!}

  eq-delooping-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group (lsuc l2) 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group (lsuc l2) 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l1 (n +ℕ 2))
            ( UU-Fin-Group (lsuc l2) 2)
            ( delooping-sign (n +ℕ 2)))
          ( hom-inv-iso-Group
            ( group-Concrete-Group (UU-Fin-Group l1 (n +ℕ 2)))
            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
            ( iso-loop-group-fin-UU-Fin-Group l1 (n +ℕ 2))))
        ( hom-inv-symmetric-group-loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group (lsuc l2) 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( group-Concrete-Group (UU-Fin-Group (lsuc l2) 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom
            ( λ n X → type-UU-Fin 2 (Q n X))
            ( λ n X → Id-equivalence-relation (set-UU-Fin 2 (Q n X)))
            ( λ n _ X → has-decidable-equality-has-cardinality 2 (pr2 (Q n X)))
            ( equiv-fin-2-equivalence-class)
            ( λ n _ → pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1))
            ( λ n Y →
              Q-transposition-swap n Y
                ( pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1)))
            ( n))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( compute-raise-Fin l1 (n +ℕ 2))))
  eq-delooping-sign-homomorphism = {!!}
```

## See also

- Definition of the delooping of the sign homomorphism based on Cartier
  [`finite-group-theory.cartier-delooping-sign-homomorphism`](finite-group-theory.cartier-delooping-sign-homomorphism.md).
- Definition of the delooping of the sign homomorphism based on Simpson
  [`finite-group-theory.simpson-delooping-sign-homomorphism`](finite-group-theory.simpson-delooping-sign-homomorphism.md).

## References

- Mangel É. and Rijke E.
  ["Delooping the sign homomorphism in univalent mathematics"](https://arxiv.org/abs/2301.10011).
