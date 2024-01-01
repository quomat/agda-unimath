# Equivalences of sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

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
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

An **equivalence of sequential diagrams** `(A, a)` and `(B, b)` is a
[sequence](foundation.dependent-sequences.md) of
[equivalences](foundation.equivalences.md) `eₙ : Aₙ ≃ Bₙ` such that their
underlying maps form a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md).

Specifically, the underlying maps need to satisfy the same naturality condition.

## Definitions

### Equivalences of sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  equiv-sequential-diagram : UU (l1 ⊔ l2)
  equiv-sequential-diagram = {!!}
```

### Components of equivalences of sequential diagrams

_Implementation note:_ As mentioned in
[`morphisms-sequential-diagrams`](synthetic-homotopy-theory.morphisms-sequential-diagrams.md),
Agda can't infer both the domain and the codomain when we use accessors for the
equivalences, and the codomain needs to be provided explicitly.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  equiv-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram A n ≃ family-sequential-diagram B n
  equiv-equiv-sequential-diagram = {!!}

  map-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram A n → family-sequential-diagram B n
  map-equiv-sequential-diagram = {!!}

  naturality-equiv-sequential-diagram :
    naturality-hom-sequential-diagram A B map-equiv-sequential-diagram
  naturality-equiv-sequential-diagram = {!!}

  hom-equiv-sequential-diagram : hom-sequential-diagram A B
  hom-equiv-sequential-diagram = {!!}

  is-equiv-map-equiv-sequential-diagram :
    ( n : ℕ) →
    is-equiv (map-equiv-sequential-diagram n)
  is-equiv-map-equiv-sequential-diagram = {!!}
```

### The identity equivalence of sequential diagrams

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  id-equiv-sequential-diagram : equiv-sequential-diagram A A
  id-equiv-sequential-diagram = {!!}
```

### Composition of equivalences of sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  ( C : sequential-diagram l3)
  where

  comp-equiv-sequential-diagram :
    equiv-sequential-diagram B C →
    equiv-sequential-diagram A B →
    equiv-sequential-diagram A C
  comp-equiv-sequential-diagram = {!!}
```

### Inverses of equivalences of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  inv-equiv-sequential-diagram : equiv-sequential-diagram B A
  inv-equiv-sequential-diagram = {!!}

  map-inv-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram B n → family-sequential-diagram A n
  map-inv-equiv-sequential-diagram = {!!}

  hom-inv-equiv-sequential-diagram : hom-sequential-diagram B A
  hom-inv-equiv-sequential-diagram = {!!}
```

## Properties

### Characterization of equality of sequential diagrams

[Equality](foundation.identity-types.md) of sequential diagrams is captured by
an equivalence between them.

```agda
equiv-eq-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  A ＝ B → equiv-sequential-diagram A B
equiv-eq-sequential-diagram = {!!}

abstract
  is-torsorial-equiv-sequential-diagram :
    { l1 : Level} (A : sequential-diagram l1) →
    is-torsorial (equiv-sequential-diagram {l2 = l1} A)
  is-torsorial-equiv-sequential-diagram = {!!}

  is-equiv-equiv-eq-sequential-diagram :
    { l1 : Level} (A B : sequential-diagram l1) →
    is-equiv (equiv-eq-sequential-diagram A B)
  is-equiv-equiv-eq-sequential-diagram = {!!}

extensionality-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  ( A ＝ B) ≃ equiv-sequential-diagram A B
extensionality-sequential-diagram = {!!}

eq-equiv-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  equiv-sequential-diagram A B → (A ＝ B)
eq-equiv-sequential-diagram = {!!}
```

### Inverses of equivalences are inverses with respect to composition of morphisms of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  is-section-inv-equiv-sequential-diagram :
    htpy-hom-sequential-diagram B
      ( comp-hom-sequential-diagram B A B
        ( hom-equiv-sequential-diagram B e)
        ( hom-inv-equiv-sequential-diagram B e))
      ( id-hom-sequential-diagram B)
  is-section-inv-equiv-sequential-diagram = {!!}

  is-retraction-inv-equiv-sequential-diagram :
    htpy-hom-sequential-diagram A
      ( comp-hom-sequential-diagram A B A
        ( hom-inv-equiv-sequential-diagram B e)
        ( hom-equiv-sequential-diagram B e))
      ( id-hom-sequential-diagram A)
  is-retraction-inv-equiv-sequential-diagram = {!!}
```
