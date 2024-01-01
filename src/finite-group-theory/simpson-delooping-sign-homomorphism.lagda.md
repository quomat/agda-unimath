# Simpson's delooping of the sign homomorphism

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.simpson-delooping-sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.delooping-sign-homomorphism
open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.action-on-equivalences-type-families-over-subuniverses
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equivalence-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.symmetric-groups

open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Ideas

We give a definition of the delooping of the sign homomorphism based on a
suggestion by Alex Simpson.

## Definitions

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  sign-comp-equivalence-relation :
    equivalence-relation lzero (Fin n ≃ type-UU-Fin n X)
  sign-comp-equivalence-relation = {!!}

  is-decidable-sign-comp-equivalence-relation :
    (f g : Fin n ≃ type-UU-Fin n X) →
    is-decidable (sim-equivalence-relation sign-comp-equivalence-relation f g)
  is-decidable-sign-comp-equivalence-relation = {!!}

  quotient-sign-comp : UU (lsuc lzero ⊔ l)
  quotient-sign-comp = {!!}

  quotient-sign-comp-Set : Set (lsuc lzero ⊔ l)
  quotient-sign-comp-Set = {!!}

module _
  {l : Level} {X : UU l}
  (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  private
    transposition-eX : Fin (pr1 eX) ≃ Fin (pr1 eX)
    transposition-eX = {!!}

  private abstract
    lemma :
      Id
        ( inr star)
        ( sign-homomorphism-Fin-two
          ( number-of-elements-count eX)
          ( Fin-UU-Fin' (number-of-elements-count eX))
          ( inv-equiv (equiv-count eX) ∘e (equiv-count eX ∘e transposition-eX)))
    lemma = {!!}

  not-sign-comp-transposition-count :
    ( Y : 2-Element-Decidable-Subtype l X) →
    ¬ ( sim-equivalence-relation
      ( sign-comp-equivalence-relation
        ( number-of-elements-count eX)
        ( X , unit-trunc-Prop (equiv-count eX)))
      ( transposition Y ∘e equiv-count eX)
      ( transposition Y ∘e (transposition Y ∘e equiv-count eX)))
  not-sign-comp-transposition-count = {!!}

  inv-Fin-2-quotient-sign-comp-count :
    ( T : quotient-sign-comp
      ( number-of-elements-count eX)
      ( X , unit-trunc-Prop (equiv-count eX))) →
    is-decidable
      ( is-in-equivalence-class
        ( sign-comp-equivalence-relation
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX)))
        ( T)
        ( equiv-count eX)) →
    Fin 2
  inv-Fin-2-quotient-sign-comp-count = {!!}

  equiv-Fin-2-quotient-sign-comp-count :
    Fin 2 ≃
    quotient-sign-comp
      ( number-of-elements-count eX)
      ( X , unit-trunc-Prop (equiv-count eX))
  equiv-Fin-2-quotient-sign-comp-count = {!!}

module _
  {l : Level} (n : ℕ) (X : UU-Fin l n) (ineq : leq-ℕ 2 n)
  where

  equiv-fin-2-quotient-sign-comp-equiv-Fin :
    (Fin n ≃ type-UU-Fin n X) → (Fin 2 ≃ quotient-sign-comp n X)
  equiv-fin-2-quotient-sign-comp-equiv-Fin = {!!}
```

```agda
module _
  {l : Level} (n : ℕ)
  where

  map-simpson-comp-equiv :
    (X X' : UU-Fin l n) →
    (type-UU-Fin n X ≃ type-UU-Fin n X') →
    (Fin n ≃ type-UU-Fin n X) → (Fin n ≃ type-UU-Fin n X')
  map-simpson-comp-equiv = {!!}

  simpson-comp-equiv :
    (X X' : UU-Fin l n) →
    (type-UU-Fin n X ≃ type-UU-Fin n X') →
    (Fin n ≃ type-UU-Fin n X) ≃ (Fin n ≃ type-UU-Fin n X')
  simpson-comp-equiv = {!!}

  abstract
    preserves-id-equiv-simpson-comp-equiv :
      (X : UU-Fin l n) → Id (simpson-comp-equiv X X id-equiv) id-equiv
    preserves-id-equiv-simpson-comp-equiv = {!!}

    preserves-comp-simpson-comp-equiv :
      ( X Y Z : UU-Fin l n)
      ( e : type-UU-Fin n X ≃ type-UU-Fin n Y) →
      ( f : type-UU-Fin n Y ≃ type-UU-Fin n Z) →
      Id
        ( simpson-comp-equiv X Z (f ∘e e))
        ( simpson-comp-equiv Y Z f ∘e simpson-comp-equiv X Y e)
    preserves-comp-simpson-comp-equiv = {!!}

  private
    lemma-sign-comp :
      ( X X' : UU-Fin l n)
      ( e : type-UU-Fin n X ≃ type-UU-Fin n X') →
      ( f f' : Fin n ≃ type-UU-Fin n X) →
      Id
        ( sign-homomorphism-Fin-two n (Fin-UU-Fin' n) (inv-equiv f ∘e f'))
        ( sign-homomorphism-Fin-two n (Fin-UU-Fin' n)
          ( inv-equiv ( map-simpson-comp-equiv X X' e f) ∘e
            map-simpson-comp-equiv X X' e f'))
    lemma-sign-comp = {!!}

  preserves-sign-comp-simpson-comp-equiv :
    ( X X' : UU-Fin l n)
    ( e : type-UU-Fin n X ≃ type-UU-Fin n X') →
    ( f f' : Fin n ≃ type-UU-Fin n X) →
    ( sim-equivalence-relation (sign-comp-equivalence-relation n X) f f' ↔
      sim-equivalence-relation
        ( sign-comp-equivalence-relation n X')
        ( map-simpson-comp-equiv X X' e f)
        ( map-simpson-comp-equiv X X' e f'))
  preserves-sign-comp-simpson-comp-equiv = {!!}
```

```agda
module _
  {l : Level}
  where

  sign-comp-aut-succ-succ-Fin :
    (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set l (n +ℕ 2))) →
    Fin (n +ℕ 2) ≃ raise l (Fin (n +ℕ 2))
  sign-comp-aut-succ-succ-Fin = {!!}

  not-action-equiv-family-on-subuniverse-transposition :
    ( n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l
      ( raise-Fin l (n +ℕ 2))) →
    ¬ ( sim-equivalence-relation
      ( sign-comp-equivalence-relation (n +ℕ 2)
        ( raise-Fin l (n +ℕ 2) ,
          unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2))))
      ( sign-comp-aut-succ-succ-Fin n (transposition Y))
      ( map-equiv
        ( action-equiv-family-over-subuniverse
          ( mere-equiv-Prop (Fin (n +ℕ 2)))
          ( λ X → Fin (n +ℕ 2) ≃ pr1 X)
          ( raise l (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2)))
          ( raise l (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2)))
          ( transposition Y))
        ( sign-comp-aut-succ-succ-Fin n (transposition Y))))
  not-action-equiv-family-on-subuniverse-transposition = {!!}

  simpson-delooping-sign :
    (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l n) (UU-Fin-Group (lsuc lzero ⊔ l) 2)
  simpson-delooping-sign = {!!}

  eq-simpson-delooping-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group l (n +ℕ 2)))
          ( group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l (n +ℕ 2))
            ( UU-Fin-Group (lsuc lzero ⊔ l) 2)
            ( simpson-delooping-sign (n +ℕ 2)))
          ( hom-inv-iso-Group
            ( group-Concrete-Group (UU-Fin-Group l (n +ℕ 2)))
            ( loop-group-Set (raise-Fin-Set l (n +ℕ 2)))
            ( iso-loop-group-fin-UU-Fin-Group l (n +ℕ 2))))
        ( hom-inv-symmetric-group-loop-group-Set (raise-Fin-Set l (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom
            ( λ n X → Fin n ≃ type-UU-Fin n X)
            ( sign-comp-equivalence-relation)
            ( λ n H → is-decidable-sign-comp-equivalence-relation n)
            ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
            ( sign-comp-aut-succ-succ-Fin)
            ( not-action-equiv-family-on-subuniverse-transposition)
            ( n))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l (n +ℕ 2))
          ( compute-raise l (Fin (n +ℕ 2)))))
  eq-simpson-delooping-sign-homomorphism = {!!}
```

## References

- Mangel É. and Rijke E.
  ["Delooping the sign homomorphism in univalent mathematics"](https://arxiv.org/abs/2301.10011).
