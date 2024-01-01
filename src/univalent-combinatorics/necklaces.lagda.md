# Necklaces

```agda
module univalent-combinatorics.necklaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms

open import univalent-combinatorics.cyclic-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **necklace** is an arrangement of coloured beads, i.e., it consists of a
[cyclic finite type](univalent-combinatorics.cyclic-finite-types.md) equipped
with a coloring of the elements. Two necklaces are considered the same if one
can be obtained from the other by rotating.

## Definition

### Necklaces

```agda
necklace : (l : Level) → ℕ → ℕ → UU (lsuc l)
necklace l m n = {!!}

module _
  {l : Level} (m : ℕ) (n : ℕ) (N : necklace l m n)
  where

  cyclic-necklace : Cyclic-Type l m
  cyclic-necklace = {!!}

  endo-necklace : Type-With-Endomorphism l
  endo-necklace = {!!}

  type-necklace : UU l
  type-necklace = {!!}

  endomorphism-necklace : type-necklace → type-necklace
  endomorphism-necklace = {!!}

  is-cyclic-endo-necklace : is-cyclic-Type-With-Endomorphism m endo-necklace
  is-cyclic-endo-necklace = {!!}

  colouring-necklace : type-necklace → Fin n
  colouring-necklace = {!!}
```

### Necklace patterns

```agda
necklace-pattern : (l : Level) → ℕ → ℕ → UU (lsuc l)
necklace-pattern l m n = {!!}
```

## Properties

### Characterization of the identity type

```agda
module _
  {l1 l2 : Level} (m n : ℕ)
  where

  equiv-necklace :
    (N1 : necklace l1 m n) (N2 : necklace l2 m n) → UU (l1 ⊔ l2)
  equiv-necklace N1 N2 = {!!}

module _
  {l : Level} (m n : ℕ)
  where

  id-equiv-necklace :
    (N : necklace l m n) → equiv-necklace m n N N
  pr1 (id-equiv-necklace N) = {!!}

module _
  {l : Level} (m n : ℕ)
  where

  extensionality-necklace :
    (N1 N2 : necklace l m n) → Id N1 N2 ≃ equiv-necklace m n N1 N2
  extensionality-necklace N1 = {!!}

  refl-extensionality-necklace :
    (N : necklace l m n) →
    Id (map-equiv (extensionality-necklace N N) refl) (id-equiv-necklace m n N)
  refl-extensionality-necklace N = {!!}
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
