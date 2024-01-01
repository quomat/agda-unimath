# Morphisms of towers of types

```agda
module foundation.morphisms-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.dependent-towers
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **morphism of towers** `A → B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |       |       |        |
  ⋯        |         |       ⋯       |        |
           v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

## Definitions

### Morphisms of towers

```agda
naturality-hom-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  (h : (n : ℕ) → type-tower A n → type-tower B n) (n : ℕ) → UU (l1 ⊔ l2)
naturality-hom-tower = {!!}

hom-tower : {l1 l2 : Level} (A : tower l1) (B : tower l2) → UU (l1 ⊔ l2)
hom-tower = {!!}

module _
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  where

  map-hom-tower : hom-tower A B → (n : ℕ) → type-tower A n → type-tower B n
  map-hom-tower = {!!}

  naturality-map-hom-tower :
    (f : hom-tower A B) (n : ℕ) → naturality-hom-tower A B (map-hom-tower f) n
  naturality-map-hom-tower = {!!}
```

### Identity map on towers

```agda
id-hom-tower :
  {l : Level} (A : tower l) → hom-tower A A
id-hom-tower = {!!}
```

### Composition of map of towers

```agda
map-comp-hom-tower :
  {l : Level} (A B C : tower l) → hom-tower B C → hom-tower A B →
  (n : ℕ) → type-tower A n → type-tower C n
map-comp-hom-tower = {!!}

naturality-comp-hom-tower :
  {l : Level} (A B C : tower l) (g : hom-tower B C) (f : hom-tower A B)
  (n : ℕ) → naturality-hom-tower A C (map-comp-hom-tower A B C g f) n
naturality-comp-hom-tower = {!!}

comp-hom-tower :
  {l : Level} (A B C : tower l) → hom-tower B C → hom-tower A B → hom-tower A C
comp-hom-tower = {!!}
```

## Properties

### Characterization of equality of maps of towers

```agda
module _
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  where

  coherence-htpy-hom-tower :
    (f g : hom-tower A B) →
    ((n : ℕ) → map-hom-tower A B f n ~ map-hom-tower A B g n) →
    (n : ℕ) → UU (l1 ⊔ l2)
  coherence-htpy-hom-tower = {!!}

  htpy-hom-tower :
    (f g : hom-tower A B) → UU (l1 ⊔ l2)
  htpy-hom-tower = {!!}

  refl-htpy-hom-tower : (f : hom-tower A B) → htpy-hom-tower f f
  refl-htpy-hom-tower = {!!}

  htpy-eq-hom-tower : (f g : hom-tower A B) → f ＝ g → htpy-hom-tower f g
  htpy-eq-hom-tower = {!!}

  is-torsorial-htpy-hom-tower :
    (f : hom-tower A B) → is-torsorial (htpy-hom-tower f)
  is-torsorial-htpy-hom-tower = {!!}

  is-equiv-htpy-eq-hom-tower :
    (f g : hom-tower A B) → is-equiv (htpy-eq-hom-tower f g)
  is-equiv-htpy-eq-hom-tower = {!!}

  extensionality-hom-tower :
    (f g : hom-tower A B) → (f ＝ g) ≃ htpy-hom-tower f g
  extensionality-hom-tower = {!!}

  eq-htpy-hom-tower : (f g : hom-tower A B) → htpy-hom-tower f g → f ＝ g
  eq-htpy-hom-tower = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
