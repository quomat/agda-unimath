# Relaxed Σ-decompositions of types

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.relaxed-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A relaxed Σ-decomposition is just a Σ-Decomposition where the condition that the
cotype must be inhabited is relaxed.

## Definitions

### General Σ-decompositions

```agda
Relaxed-Σ-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Relaxed-Σ-Decomposition l2 l3 A = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Relaxed-Σ-Decomposition l2 l3 A)
  where

  indexing-type-Relaxed-Σ-Decomposition : UU l2
  indexing-type-Relaxed-Σ-Decomposition = {!!}

  cotype-Relaxed-Σ-Decomposition : indexing-type-Relaxed-Σ-Decomposition → UU l3
  cotype-Relaxed-Σ-Decomposition = {!!}

  matching-correspondence-Relaxed-Σ-Decomposition :
    A ≃ Σ indexing-type-Relaxed-Σ-Decomposition cotype-Relaxed-Σ-Decomposition
  matching-correspondence-Relaxed-Σ-Decomposition = {!!}

  map-matching-correspondence-Relaxed-Σ-Decomposition :
    A → Σ indexing-type-Relaxed-Σ-Decomposition cotype-Relaxed-Σ-Decomposition
  map-matching-correspondence-Relaxed-Σ-Decomposition = {!!}
```

### Fibered relaxed Σ-decompositions

```agda
fibered-Relaxed-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-Relaxed-Σ-Decomposition : Relaxed-Σ-Decomposition l2 l3 A
  fst-fibered-Relaxed-Σ-Decomposition = {!!}

  indexing-type-fst-fibered-Relaxed-Σ-Decomposition : UU l2
  indexing-type-fst-fibered-Relaxed-Σ-Decomposition = {!!}

  cotype-fst-fibered-Relaxed-Σ-Decomposition :
    indexing-type-fst-fibered-Relaxed-Σ-Decomposition → UU l3
  cotype-fst-fibered-Relaxed-Σ-Decomposition = {!!}

  matching-correspondence-fst-fibered-Relaxed-Σ-Decomposition :
    A ≃
    Σ ( indexing-type-Relaxed-Σ-Decomposition
        ( fst-fibered-Relaxed-Σ-Decomposition))
      ( cotype-Relaxed-Σ-Decomposition fst-fibered-Relaxed-Σ-Decomposition)
  matching-correspondence-fst-fibered-Relaxed-Σ-Decomposition = {!!}

  map-matching-correspondence-fst-fibered-Relaxed-Σ-Decomposition :
    A →
    Σ ( indexing-type-Relaxed-Σ-Decomposition
        ( fst-fibered-Relaxed-Σ-Decomposition))
      ( cotype-Relaxed-Σ-Decomposition fst-fibered-Relaxed-Σ-Decomposition)
  map-matching-correspondence-fst-fibered-Relaxed-Σ-Decomposition = {!!}

  snd-fibered-Relaxed-Σ-Decomposition :
      Relaxed-Σ-Decomposition l4 l5
        ( indexing-type-fst-fibered-Relaxed-Σ-Decomposition)
  snd-fibered-Relaxed-Σ-Decomposition = {!!}

  indexing-type-snd-fibered-Relaxed-Σ-Decomposition : UU l4
  indexing-type-snd-fibered-Relaxed-Σ-Decomposition = {!!}

  cotype-snd-fibered-Relaxed-Σ-Decomposition :
    indexing-type-snd-fibered-Relaxed-Σ-Decomposition → UU l5
  cotype-snd-fibered-Relaxed-Σ-Decomposition = {!!}

  matching-correspondence-snd-fibered-Relaxed-Σ-Decomposition :
    indexing-type-fst-fibered-Relaxed-Σ-Decomposition ≃
    Σ ( indexing-type-Relaxed-Σ-Decomposition
        ( snd-fibered-Relaxed-Σ-Decomposition))
      ( cotype-Relaxed-Σ-Decomposition snd-fibered-Relaxed-Σ-Decomposition)
  matching-correspondence-snd-fibered-Relaxed-Σ-Decomposition = {!!}

  map-matching-correspondence-snd-fibered-Relaxed-Σ-Decomposition :
    indexing-type-fst-fibered-Relaxed-Σ-Decomposition →
    Σ ( indexing-type-Relaxed-Σ-Decomposition
        ( snd-fibered-Relaxed-Σ-Decomposition))
      ( cotype-Relaxed-Σ-Decomposition snd-fibered-Relaxed-Σ-Decomposition)
  map-matching-correspondence-snd-fibered-Relaxed-Σ-Decomposition = {!!}
```

#### Displayed double Σ-decompositions

```agda
displayed-Relaxed-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-displayed-Relaxed-Σ-Decomposition : Relaxed-Σ-Decomposition l2 l3 A
  fst-displayed-Relaxed-Σ-Decomposition = {!!}

  indexing-type-fst-displayed-Relaxed-Σ-Decomposition : UU l2
  indexing-type-fst-displayed-Relaxed-Σ-Decomposition = {!!}

  cotype-fst-displayed-Relaxed-Σ-Decomposition :
    indexing-type-fst-displayed-Relaxed-Σ-Decomposition → UU l3
  cotype-fst-displayed-Relaxed-Σ-Decomposition = {!!}

  matching-correspondence-fst-displayed-Relaxed-Σ-Decomposition :
    A ≃
    Σ ( indexing-type-Relaxed-Σ-Decomposition
        fst-displayed-Relaxed-Σ-Decomposition)
      ( cotype-Relaxed-Σ-Decomposition fst-displayed-Relaxed-Σ-Decomposition)
  matching-correspondence-fst-displayed-Relaxed-Σ-Decomposition = {!!}

  map-matching-correspondence-fst-displayed-Relaxed-Σ-Decomposition :
    A →
    Σ ( indexing-type-Relaxed-Σ-Decomposition
        fst-displayed-Relaxed-Σ-Decomposition)
      ( cotype-Relaxed-Σ-Decomposition fst-displayed-Relaxed-Σ-Decomposition)
  map-matching-correspondence-fst-displayed-Relaxed-Σ-Decomposition = {!!}

  snd-displayed-Relaxed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Relaxed-Σ-Decomposition) →
    Relaxed-Σ-Decomposition l4 l5
      ( cotype-fst-displayed-Relaxed-Σ-Decomposition x)
  snd-displayed-Relaxed-Σ-Decomposition = {!!}

  indexing-type-snd-displayed-Relaxed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Relaxed-Σ-Decomposition) →
    UU l4
  indexing-type-snd-displayed-Relaxed-Σ-Decomposition x = {!!}

  cotype-snd-displayed-Relaxed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Relaxed-Σ-Decomposition) →
    indexing-type-snd-displayed-Relaxed-Σ-Decomposition x →
    UU l5
  cotype-snd-displayed-Relaxed-Σ-Decomposition x = {!!}

  matching-correspondence-snd-displayed-Relaxed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Relaxed-Σ-Decomposition) →
    ( cotype-fst-displayed-Relaxed-Σ-Decomposition x ≃
      Σ ( indexing-type-snd-displayed-Relaxed-Σ-Decomposition x)
        ( cotype-snd-displayed-Relaxed-Σ-Decomposition x))
  matching-correspondence-snd-displayed-Relaxed-Σ-Decomposition x = {!!}

  map-matching-correspondence-snd-displayed-Relaxed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Relaxed-Σ-Decomposition) →
    cotype-fst-displayed-Relaxed-Σ-Decomposition x →
    Σ ( indexing-type-snd-displayed-Relaxed-Σ-Decomposition x)
      ( cotype-snd-displayed-Relaxed-Σ-Decomposition x)
  map-matching-correspondence-snd-displayed-Relaxed-Σ-Decomposition x = {!!}
```

## Properties

### Characterization of equality of relaxed-Σ-decompositions

```agda
equiv-Relaxed-Σ-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Relaxed-Σ-Decomposition l2 l3 A)
  (Y : Relaxed-Σ-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Relaxed-Σ-Decomposition X Y = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Relaxed-Σ-Decomposition l2 l3 A) (Y : Relaxed-Σ-Decomposition l4 l5 A)
  (e : equiv-Relaxed-Σ-Decomposition X Y)
  where

  equiv-indexing-type-equiv-Relaxed-Σ-Decomposition :
    indexing-type-Relaxed-Σ-Decomposition X ≃
    indexing-type-Relaxed-Σ-Decomposition Y
  equiv-indexing-type-equiv-Relaxed-Σ-Decomposition = {!!}

  map-equiv-indexing-type-equiv-Relaxed-Σ-Decomposition :
    indexing-type-Relaxed-Σ-Decomposition X →
    indexing-type-Relaxed-Σ-Decomposition Y
  map-equiv-indexing-type-equiv-Relaxed-Σ-Decomposition = {!!}

  equiv-cotype-equiv-Relaxed-Σ-Decomposition :
    (x : indexing-type-Relaxed-Σ-Decomposition X) →
    cotype-Relaxed-Σ-Decomposition X x ≃
    cotype-Relaxed-Σ-Decomposition Y
      ( map-equiv-indexing-type-equiv-Relaxed-Σ-Decomposition x)
  equiv-cotype-equiv-Relaxed-Σ-Decomposition = {!!}

  map-equiv-cotype-equiv-Relaxed-Σ-Decomposition :
    (x : indexing-type-Relaxed-Σ-Decomposition X) →
    cotype-Relaxed-Σ-Decomposition X x →
    cotype-Relaxed-Σ-Decomposition Y
      ( map-equiv-indexing-type-equiv-Relaxed-Σ-Decomposition x)
  map-equiv-cotype-equiv-Relaxed-Σ-Decomposition x = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : Relaxed-Σ-Decomposition l2 l3 A)
  where

  id-equiv-Relaxed-Σ-Decomposition : equiv-Relaxed-Σ-Decomposition X X
  pr1 id-equiv-Relaxed-Σ-Decomposition = {!!}

  is-torsorial-equiv-Relaxed-Σ-Decomposition :
    is-torsorial (equiv-Relaxed-Σ-Decomposition X)
  is-torsorial-equiv-Relaxed-Σ-Decomposition = {!!}

  equiv-eq-Relaxed-Σ-Decomposition :
    (Y : Relaxed-Σ-Decomposition l2 l3 A) →
    (X ＝ Y) → equiv-Relaxed-Σ-Decomposition X Y
  equiv-eq-Relaxed-Σ-Decomposition .X refl = {!!}

  is-equiv-equiv-eq-Relaxed-Σ-Decomposition :
    (Y : Relaxed-Σ-Decomposition l2 l3 A) →
    is-equiv (equiv-eq-Relaxed-Σ-Decomposition Y)
  is-equiv-equiv-eq-Relaxed-Σ-Decomposition = {!!}

  extensionality-Relaxed-Σ-Decomposition :
    (Y : Relaxed-Σ-Decomposition l2 l3 A) →
    (X ＝ Y) ≃ equiv-Relaxed-Σ-Decomposition X Y
  pr1 (extensionality-Relaxed-Σ-Decomposition Y) = {!!}

  eq-equiv-Relaxed-Σ-Decomposition :
    (Y : Relaxed-Σ-Decomposition l2 l3 A) →
    equiv-Relaxed-Σ-Decomposition X Y → (X ＝ Y)
  eq-equiv-Relaxed-Σ-Decomposition Y = {!!}
```

### Invariance of Σ-decompositions under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  equiv-tr-Relaxed-Σ-Decomposition :
    {l3 l4 : Level} →
    Relaxed-Σ-Decomposition l3 l4 A ≃ Relaxed-Σ-Decomposition l3 l4 B
  equiv-tr-Relaxed-Σ-Decomposition = {!!}

  map-equiv-tr-Relaxed-Σ-Decomposition :
    {l3 l4 : Level} →
    Relaxed-Σ-Decomposition l3 l4 A → Relaxed-Σ-Decomposition l3 l4 B
  map-equiv-tr-Relaxed-Σ-Decomposition = {!!}
```

### Iterated Σ-decompositions

#### Characterization of identity type for fibered double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : fibered-Relaxed-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-fibered-Relaxed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-fibered-Relaxed-Σ-Decomposition = {!!}

  equiv-snd-fibered-Relaxed-Σ-Decomposition :
    (e : equiv-fst-fibered-Relaxed-Σ-Decomposition) →
    UU (l4 ⊔ l5 ⊔ l6 ⊔ l8 ⊔ l9)
  equiv-snd-fibered-Relaxed-Σ-Decomposition e = {!!}

  equiv-fibered-Relaxed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-fibered-Relaxed-Σ-Decomposition = {!!}

  fst-equiv-fibered-Relaxed-Σ-Decomposition :
    (e : equiv-fibered-Relaxed-Σ-Decomposition) →
    equiv-fst-fibered-Relaxed-Σ-Decomposition
  fst-equiv-fibered-Relaxed-Σ-Decomposition = {!!}

  snd-equiv-fibered-Relaxed-Σ-Decomposition :
    (e : equiv-fibered-Relaxed-Σ-Decomposition) →
    equiv-snd-fibered-Relaxed-Σ-Decomposition
      (fst-equiv-fibered-Relaxed-Σ-Decomposition e)
  snd-equiv-fibered-Relaxed-Σ-Decomposition = {!!}

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( D : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = {!!}

  is-torsorial-equiv-fibered-Relaxed-Σ-Decomposition :
    is-torsorial (equiv-fibered-Relaxed-Σ-Decomposition D)
  is-torsorial-equiv-fibered-Relaxed-Σ-Decomposition = {!!}

  id-equiv-fibered-Relaxed-Σ-Decomposition :
    equiv-fibered-Relaxed-Σ-Decomposition D D
  pr1 id-equiv-fibered-Relaxed-Σ-Decomposition = {!!}

  equiv-eq-fibered-Relaxed-Σ-Decomposition :
    (D' : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') → equiv-fibered-Relaxed-Σ-Decomposition D D'
  equiv-eq-fibered-Relaxed-Σ-Decomposition .D refl = {!!}

  is-equiv-equiv-eq-fibered-Relaxed-Σ-Decomposition :
    (D' : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-fibered-Relaxed-Σ-Decomposition D')
  is-equiv-equiv-eq-fibered-Relaxed-Σ-Decomposition = {!!}

  extensionality-fibered-Relaxed-Σ-Decomposition :
    (D' : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') ≃ equiv-fibered-Relaxed-Σ-Decomposition D D'
  pr1 (extensionality-fibered-Relaxed-Σ-Decomposition D') = {!!}

  eq-equiv-fibered-Relaxed-Σ-Decomposition :
    (D' : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    (equiv-fibered-Relaxed-Σ-Decomposition D D') → (D ＝ D')
  eq-equiv-fibered-Relaxed-Σ-Decomposition D' = {!!}
```

#### Characterization of identity type for displayed double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : displayed-Relaxed-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-displayed-Relaxed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-displayed-Relaxed-Σ-Decomposition = {!!}

  equiv-snd-displayed-Relaxed-Σ-Decomposition :
    (e : equiv-fst-displayed-Relaxed-Σ-Decomposition) →
    UU (l2 ⊔ l4 ⊔ l5 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-snd-displayed-Relaxed-Σ-Decomposition e = {!!}

  equiv-displayed-Relaxed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-displayed-Relaxed-Σ-Decomposition = {!!}

  fst-equiv-displayed-Relaxed-Σ-Decomposition :
    (e : equiv-displayed-Relaxed-Σ-Decomposition) →
    equiv-fst-displayed-Relaxed-Σ-Decomposition
  fst-equiv-displayed-Relaxed-Σ-Decomposition = {!!}

  snd-equiv-displayed-Relaxed-Σ-Decomposition :
    (e : equiv-displayed-Relaxed-Σ-Decomposition) →
    equiv-snd-displayed-Relaxed-Σ-Decomposition
      ( fst-equiv-displayed-Relaxed-Σ-Decomposition e)
  snd-equiv-displayed-Relaxed-Σ-Decomposition = {!!}

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( disp-D : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = {!!}

  is-torsorial-equiv-displayed-Relaxed-Σ-Decomposition :
    is-torsorial (equiv-displayed-Relaxed-Σ-Decomposition disp-D)
  is-torsorial-equiv-displayed-Relaxed-Σ-Decomposition = {!!}

  id-equiv-displayed-Relaxed-Σ-Decomposition :
    equiv-displayed-Relaxed-Σ-Decomposition disp-D disp-D
  pr1 id-equiv-displayed-Relaxed-Σ-Decomposition = {!!}

  equiv-eq-displayed-Relaxed-Σ-Decomposition :
    (disp-D' : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') → equiv-displayed-Relaxed-Σ-Decomposition disp-D disp-D'
  equiv-eq-displayed-Relaxed-Σ-Decomposition .disp-D refl = {!!}

  is-equiv-equiv-eq-displayed-Relaxed-Σ-Decomposition :
    (disp-D' : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-displayed-Relaxed-Σ-Decomposition disp-D')
  is-equiv-equiv-eq-displayed-Relaxed-Σ-Decomposition = {!!}

  extensionality-displayed-Relaxed-Σ-Decomposition :
    (disp-D' : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') ≃ equiv-displayed-Relaxed-Σ-Decomposition disp-D disp-D'
  pr1 (extensionality-displayed-Relaxed-Σ-Decomposition D) = {!!}

  eq-equiv-displayed-Relaxed-Σ-Decomposition :
    (disp-D' : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A) →
    (equiv-displayed-Relaxed-Σ-Decomposition disp-D disp-D') →
    (disp-D ＝ disp-D')
  eq-equiv-displayed-Relaxed-Σ-Decomposition D = {!!}
```

#### Equivalence between fibered double relaxed Σ-recompositions and displayed double relaxed Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (fib-D : fibered-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = {!!}

  matching-correspondence-displayed-fibered-Relaxed-Σ-Decomposition :
    A ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
  matching-correspondence-displayed-fibered-Relaxed-Σ-Decomposition = {!!}

  map-displayed-fibered-Relaxed-Σ-Decomposition :
    displayed-Relaxed-Σ-Decomposition l4 (l3 ⊔ l5) l5 l3 A
  pr1 (pr1 map-displayed-fibered-Relaxed-Σ-Decomposition) = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (disp-D : displayed-Relaxed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    M = {!!}

  matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decomposition :
    A ≃ Σ (Σ M P) (λ (m , p) → Q m p)
  matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decomposition = {!!}

  map-inv-displayed-fibered-Relaxed-Σ-Decomposition :
    fibered-Relaxed-Σ-Decomposition (l2 ⊔ l4) l5 l2 l4 A
  pr1 (pr1 map-inv-displayed-fibered-Relaxed-Σ-Decomposition) = {!!}

module _
  {l1 l : Level} {A : UU l1}
  (fib-D : fibered-Relaxed-Σ-Decomposition l l l l A)
  where

  private
    X = {!!}

    htpy-matching-correspondence :
      map-equiv
        ( equiv-Σ Y (inv-equiv f) (λ _ → id-equiv) ∘e
          matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decomposition
            ( disp-D)) ~
      ( map-equiv e)
    htpy-matching-correspondence a = {!!}

  is-retraction-map-inv-displayed-fibered-Relaxed-Σ-Decomposition :
    map-inv-displayed-fibered-Relaxed-Σ-Decomposition
      ( map-displayed-fibered-Relaxed-Σ-Decomposition fib-D) ＝ fib-D
  is-retraction-map-inv-displayed-fibered-Relaxed-Σ-Decomposition = {!!}

module _
  {l1 l : Level} {A : UU l1}
  (disp-D : displayed-Relaxed-Σ-Decomposition l l l l A)
  where

  private
    M = {!!}

    htpy-matching-correspondence :
      map-equiv
        ( equiv-Σ N id-equiv (inv-equiv ∘ t) ∘e
          matching-correspondence-displayed-fibered-Relaxed-Σ-Decomposition
          (fib-D)) ~
      map-equiv s
    htpy-matching-correspondence x = {!!}

  is-section-map-inv-displayed-fibered-Relaxed-Σ-Decomposition :
    ( map-displayed-fibered-Relaxed-Σ-Decomposition
      {l1} {l} {l} {l} {l} {A} fib-D) ＝
    disp-D
  is-section-map-inv-displayed-fibered-Relaxed-Σ-Decomposition = {!!}

is-equiv-map-displayed-fibered-Relaxed-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  is-equiv
    ( map-displayed-fibered-Relaxed-Σ-Decomposition {l1} {l} {l} {l} {l} {A})
is-equiv-map-displayed-fibered-Relaxed-Σ-Decomposition = {!!}

equiv-displayed-fibered-Relaxed-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  fibered-Relaxed-Σ-Decomposition l l l l A ≃
  displayed-Relaxed-Σ-Decomposition l l l l A
pr1 equiv-displayed-fibered-Relaxed-Σ-Decomposition = {!!}
pr2 equiv-displayed-fibered-Relaxed-Σ-Decomposition = {!!}
```
