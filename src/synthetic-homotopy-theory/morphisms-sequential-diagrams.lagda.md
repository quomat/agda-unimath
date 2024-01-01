# Morphisms of sequential diagrams

```agda
module synthetic-homotopy-theory.morphisms-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A **morphism between
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md)**
`f : (A, a) → (B, b)` is a [sequence](foundation.dependent-sequences.md) of maps
`fₙ : Aₙ → Bₙ` satisfying the naturality condition that all squares of the form

```text
        aₙ
    Aₙ ---> Aₙ₊₁
    |       |
 fₙ |       | fₙ₊₁
    v       v
    Bₙ ---> Bₙ₊₁
        bₙ
```

[commute](foundation.commuting-squares-of-maps.md).

## Definitions

### Morphisms of sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  naturality-hom-sequential-diagram :
    ( h :
      ( n : ℕ) →
      family-sequential-diagram A n → family-sequential-diagram B n) →
    UU (l1 ⊔ l2)
  naturality-hom-sequential-diagram = {!!}

  hom-sequential-diagram : UU (l1 ⊔ l2)
  hom-sequential-diagram = {!!}
```

### Components of morphisms of sequential diagrams

_Implementation note:_ Ideally we would have both the domain and codomain of a
morphism of sequential diagrams inferred by Agda. Unfortunately that's not the
case with the current implementation, and the codomain needs to be provided
explicitly. This arises also in
[equivalences of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( h : hom-sequential-diagram A B)
  where

  map-hom-sequential-diagram :
    ( n : ℕ) → family-sequential-diagram A n → family-sequential-diagram B n
  map-hom-sequential-diagram = {!!}

  naturality-map-hom-sequential-diagram :
    naturality-hom-sequential-diagram A B map-hom-sequential-diagram
  naturality-map-hom-sequential-diagram = {!!}
```

### The identity morphism of sequential diagrams

All sequential diagrams have an **identity morphism** constructed from the
identity function on the underlying types.

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  id-hom-sequential-diagram : hom-sequential-diagram A A
  id-hom-sequential-diagram = {!!}
```

### Composition of morphisms of sequential diagrams

**Composition of morphisms** is induced by composition of the underlying maps
and by pasting diagrams.

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  ( C : sequential-diagram l3)
  where

  comp-hom-sequential-diagram :
    hom-sequential-diagram B C →
    hom-sequential-diagram A B →
    hom-sequential-diagram A C
  comp-hom-sequential-diagram = {!!}
```

### Homotopies between morphisms of sequential diagrams

A **homotopy** between morphisms `f, g : (A, a) → (B, b)` consists of a
[sequence](foundation.dependent-sequences.md) of
[homotopies](foundation.homotopies.md) `Hₙ : fₙ ~ gₙ` and a coherence datum
filling the cylinders

```text
              aₙ
      Aₙ ----------> Aₙ₊₁
      / \            / \
     / Hₙ\          /Hₙ₊₁\
 fₙ |  = {!!}
```

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( f g : hom-sequential-diagram A B)
  where

  coherence-htpy-hom-sequential-diagram :
    ( H :
      ( n : ℕ) →
      ( map-hom-sequential-diagram B f n) ~
      ( map-hom-sequential-diagram B g n)) →
    UU (l1 ⊔ l2)
  coherence-htpy-hom-sequential-diagram = {!!}

  htpy-hom-sequential-diagram : UU (l1 ⊔ l2)
  htpy-hom-sequential-diagram = {!!}
```

### Components of homotopies between morphisms of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  { f g : hom-sequential-diagram A B}
  ( H : htpy-hom-sequential-diagram B f g)
  where

  htpy-htpy-hom-sequential-diagram :
    ( n : ℕ) →
    ( map-hom-sequential-diagram B f n) ~
    ( map-hom-sequential-diagram B g n)
  htpy-htpy-hom-sequential-diagram = {!!}

  coherence-htpy-htpy-hom-sequential-diagram :
    coherence-htpy-hom-sequential-diagram B f g htpy-htpy-hom-sequential-diagram
  coherence-htpy-htpy-hom-sequential-diagram = {!!}
```

## Properties

### Characterization of equality of morphisms of sequential diagrams

[Equality](foundation.identity-types.md) of morphisms of sequential diagrams is
captured by a homotopy between them.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  reflexive-htpy-hom-sequential-diagram :
    ( f : hom-sequential-diagram A B) → htpy-hom-sequential-diagram B f f
  reflexive-htpy-hom-sequential-diagram = {!!}

  htpy-eq-sequential-diagram :
    ( f f' : hom-sequential-diagram A B) →
    ( f ＝ f') → htpy-hom-sequential-diagram B f f'
  htpy-eq-sequential-diagram = {!!}

  abstract
    is-torsorial-htpy-sequential-diagram :
      ( f : hom-sequential-diagram A B) →
      is-torsorial (htpy-hom-sequential-diagram B f)
    is-torsorial-htpy-sequential-diagram = {!!}

    is-equiv-htpy-eq-sequential-diagram :
      ( f f' : hom-sequential-diagram A B) →
      is-equiv (htpy-eq-sequential-diagram f f')
    is-equiv-htpy-eq-sequential-diagram = {!!}

  extensionality-hom-sequential-diagram :
    ( f f' : hom-sequential-diagram A B) →
    ( f ＝ f') ≃ htpy-hom-sequential-diagram B f f'
  extensionality-hom-sequential-diagram = {!!}

  eq-htpy-sequential-diagram :
    ( f f' : hom-sequential-diagram A B) →
    htpy-hom-sequential-diagram B f f' → (f ＝ f')
  eq-htpy-sequential-diagram = {!!}
```
