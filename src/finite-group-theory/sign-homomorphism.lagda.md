# The sign homomorphism

```agda
module finite-group-theory.sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations
open import finite-group-theory.transpositions

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.symmetric-groups

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sign of a permutation is defined as the parity of the length of the
decomposition of the permutation into transpositions. We show that each such
decomposition as the same parity, so the sign map is well defined. We then show
that the sign map is a group homomorphism.

## Definitions

### The sign homomorphism into ℤ/2

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  sign-homomorphism-Fin-two : Aut (type-UU-Fin n X) → Fin 2
  sign-homomorphism-Fin-two f = {!!}

  preserves-add-sign-homomorphism-Fin-two :
    (f g : (type-UU-Fin n X) ≃ (type-UU-Fin n X)) →
    Id
      ( sign-homomorphism-Fin-two (f ∘e g))
      ( add-Fin 2 (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g))
  preserves-add-sign-homomorphism-Fin-two = {!!}

  eq-sign-homomorphism-Fin-two-transposition :
    ( Y : 2-Element-Decidable-Subtype l (type-UU-Fin n X)) →
    Id
      ( sign-homomorphism-Fin-two (transposition Y))
      ( inr star)
  eq-sign-homomorphism-Fin-two-transposition = {!!}

module _
  {l l' : Level} (n : ℕ) (X : UU-Fin l n) (Y : UU-Fin l' n)
  where

  preserves-conjugation-sign-homomorphism-Fin-two :
    (f : (type-UU-Fin n X) ≃ (type-UU-Fin n X)) →
    (g : (type-UU-Fin n X) ≃ (type-UU-Fin n Y)) →
    Id
      ( sign-homomorphism-Fin-two n Y (g ∘e (f ∘e inv-equiv g)))
      ( sign-homomorphism-Fin-two n X f)
  preserves-conjugation-sign-homomorphism-Fin-two = {!!}
```

### The sign homomorphism into the symmetric group S₂

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  map-sign-homomorphism : Aut (type-UU-Fin n X) → Aut (Fin 2)
  map-sign-homomorphism f = {!!}

  preserves-comp-map-sign-homomorphism :
    preserves-mul _∘e_ _∘e_ map-sign-homomorphism
  preserves-comp-map-sign-homomorphism = {!!}

  sign-homomorphism :
    hom-Group
      ( symmetric-Group (set-UU-Fin n X))
      ( symmetric-Group (Fin-Set 2))
  sign-homomorphism = {!!}

  eq-sign-homomorphism-transposition :
    ( Y : 2-Element-Decidable-Subtype l (type-UU-Fin n X)) →
    Id
      ( map-hom-Group
        ( symmetric-Group (set-UU-Fin n X))
        ( symmetric-Group (Fin-Set 2))
        ( sign-homomorphism)
        ( transposition Y))
      ( equiv-succ-Fin 2)
  eq-sign-homomorphism-transposition = {!!}
```
