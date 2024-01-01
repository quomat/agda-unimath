# Σ-decompositions of types

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.sets
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

A **Σ-decomposition** of a type `A` consists of a type `X` and a family of
inhabited types `Y x` indexed by `x : A` equipped with an equivalence
`A ≃ Σ X Y`. The type `X` is called the indexing type of the Σ-decomposition,
the elements of `Y x` are called the cotypes of the Σ-decomposition, and the
equivalence `A ≃ Σ X Y` is the matching correspondence of the Σ-decomposition.

Note that types may have many Σ-decompositions. The type of Σ-decompositions of
the unit type, for instance, is equivalent to the type of all pointed connected
types. Alternatively, we may think of the type of Σ-decompositions of the unit
type as the type of higher groupoid structures on a point, i.e., the type of
higher group structures.

We may restrict to Σ-decompositions where the indexing type is in a given
subuniverse, such as the subuniverse of sets or the subuniverse of finite sets.
For instance, the type of set-indexed Σ-decompositions of a type `A` is
equivalent to the type of equivalence relations on `A`.

## Definitions

### General Σ-decompositions

```agda
Σ-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Σ-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Σ-Decomposition l2 l3 A)
  where

  indexing-type-Σ-Decomposition : UU l2
  indexing-type-Σ-Decomposition = {!!}

  inhabited-cotype-Σ-Decomposition :
    Fam-Inhabited-Types l3 indexing-type-Σ-Decomposition
  inhabited-cotype-Σ-Decomposition = {!!}

  cotype-Σ-Decomposition : indexing-type-Σ-Decomposition → UU l3
  cotype-Σ-Decomposition = {!!}

  is-inhabited-cotype-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition) →
    is-inhabited (cotype-Σ-Decomposition x)
  is-inhabited-cotype-Σ-Decomposition = {!!}

  matching-correspondence-Σ-Decomposition :
    A ≃ Σ indexing-type-Σ-Decomposition cotype-Σ-Decomposition
  matching-correspondence-Σ-Decomposition = {!!}

  map-matching-correspondence-Σ-Decomposition :
    A → Σ indexing-type-Σ-Decomposition cotype-Σ-Decomposition
  map-matching-correspondence-Σ-Decomposition = {!!}

  is-inhabited-indexing-type-inhabited-Σ-Decomposition :
    (p : is-inhabited A) → (is-inhabited (indexing-type-Σ-Decomposition))
  is-inhabited-indexing-type-inhabited-Σ-Decomposition = {!!}

  inhabited-indexing-type-inhabited-Σ-Decomposition :
    (p : is-inhabited A) → (Inhabited-Type l2)
  inhabited-indexing-type-inhabited-Σ-Decomposition = {!!}

  is-inhabited-base-is-inhabited-indexing-type-Σ-Decomposition :
    (is-inhabited (indexing-type-Σ-Decomposition)) → (is-inhabited A)
  is-inhabited-base-is-inhabited-indexing-type-Σ-Decomposition = {!!}
```

### Set-indexed Σ-decompositions

```agda
Set-Indexed-Σ-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Set-Indexed-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Set-Indexed-Σ-Decomposition l2 l3 A)
  where

  indexing-set-Set-Indexed-Σ-Decomposition : Set l2
  indexing-set-Set-Indexed-Σ-Decomposition = {!!}

  indexing-type-Set-Indexed-Σ-Decomposition : UU l2
  indexing-type-Set-Indexed-Σ-Decomposition = {!!}

  inhabited-cotype-Set-Indexed-Σ-Decomposition :
    indexing-type-Set-Indexed-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-Set-Indexed-Σ-Decomposition = {!!}

  cotype-Set-Indexed-Σ-Decomposition :
    indexing-type-Set-Indexed-Σ-Decomposition → UU l3
  cotype-Set-Indexed-Σ-Decomposition = {!!}

  is-inhabited-cotype-Set-Indexed-Σ-Decomposition :
    (x : indexing-type-Set-Indexed-Σ-Decomposition) →
    is-inhabited (cotype-Set-Indexed-Σ-Decomposition x)
  is-inhabited-cotype-Set-Indexed-Σ-Decomposition = {!!}

  matching-correspondence-Set-Indexed-Σ-Decomposition :
    A ≃
    Σ indexing-type-Set-Indexed-Σ-Decomposition
      cotype-Set-Indexed-Σ-Decomposition
  matching-correspondence-Set-Indexed-Σ-Decomposition = {!!}

  map-matching-correspondence-Set-Indexed-Σ-Decomposition :
    A →
    Σ indexing-type-Set-Indexed-Σ-Decomposition
      cotype-Set-Indexed-Σ-Decomposition
  map-matching-correspondence-Set-Indexed-Σ-Decomposition = {!!}

  index-Set-Indexed-Σ-Decomposition :
    A → indexing-type-Set-Indexed-Σ-Decomposition
  index-Set-Indexed-Σ-Decomposition = {!!}
```

### Fibered double Σ-decompositions

```agda
fibered-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-Σ-Decomposition : Σ-Decomposition l2 l3 A
  fst-fibered-Σ-Decomposition = {!!}

  indexing-type-fst-fibered-Σ-Decomposition : UU l2
  indexing-type-fst-fibered-Σ-Decomposition = {!!}

  inhabited-cotype-fst-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-fibered-Σ-Decomposition = {!!}

  cotype-fst-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition → UU l3
  cotype-fst-fibered-Σ-Decomposition = {!!}

  matching-correspondence-fst-fibered-Σ-Decomposition :
    A ≃
    Σ (indexing-type-Σ-Decomposition fst-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-fibered-Σ-Decomposition)
  matching-correspondence-fst-fibered-Σ-Decomposition = {!!}

  map-matching-correspondence-fst-fibered-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-fibered-Σ-Decomposition)
  map-matching-correspondence-fst-fibered-Σ-Decomposition = {!!}

  snd-fibered-Σ-Decomposition :
      Σ-Decomposition l4 l5 indexing-type-fst-fibered-Σ-Decomposition
  snd-fibered-Σ-Decomposition = {!!}

  indexing-type-snd-fibered-Σ-Decomposition : UU l4
  indexing-type-snd-fibered-Σ-Decomposition = {!!}

  inhabited-cotype-snd-fibered-Σ-Decomposition :
    indexing-type-snd-fibered-Σ-Decomposition → Inhabited-Type l5
  inhabited-cotype-snd-fibered-Σ-Decomposition = {!!}

  cotype-snd-fibered-Σ-Decomposition :
    indexing-type-snd-fibered-Σ-Decomposition → UU l5
  cotype-snd-fibered-Σ-Decomposition = {!!}

  matching-correspondence-snd-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition ≃
    Σ (indexing-type-Σ-Decomposition snd-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition snd-fibered-Σ-Decomposition)
  matching-correspondence-snd-fibered-Σ-Decomposition = {!!}

  map-matching-correspondence-snd-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition →
    Σ (indexing-type-Σ-Decomposition snd-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition snd-fibered-Σ-Decomposition)
  map-matching-correspondence-snd-fibered-Σ-Decomposition = {!!}
```

#### Displayed double Σ-decompositions

```agda
displayed-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-displayed-Σ-Decomposition : Σ-Decomposition l2 l3 A
  fst-displayed-Σ-Decomposition = {!!}

  indexing-type-fst-displayed-Σ-Decomposition : UU l2
  indexing-type-fst-displayed-Σ-Decomposition = {!!}

  inhabited-cotype-fst-displayed-Σ-Decomposition :
    indexing-type-fst-displayed-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-displayed-Σ-Decomposition = {!!}

  cotype-fst-displayed-Σ-Decomposition :
    indexing-type-fst-displayed-Σ-Decomposition → UU l3
  cotype-fst-displayed-Σ-Decomposition = {!!}

  matching-correspondence-fst-displayed-Σ-Decomposition :
    A ≃
    Σ (indexing-type-Σ-Decomposition fst-displayed-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-displayed-Σ-Decomposition)
  matching-correspondence-fst-displayed-Σ-Decomposition = {!!}

  map-matching-correspondence-fst-displayed-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-displayed-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-displayed-Σ-Decomposition)
  map-matching-correspondence-fst-displayed-Σ-Decomposition = {!!}

  snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    Σ-Decomposition l4 l5 (cotype-fst-displayed-Σ-Decomposition x)
  snd-displayed-Σ-Decomposition = {!!}

  indexing-type-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    UU l4
  indexing-type-snd-displayed-Σ-Decomposition = {!!}

  inhabited-cotype-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    indexing-type-snd-displayed-Σ-Decomposition x → Inhabited-Type l5
  inhabited-cotype-snd-displayed-Σ-Decomposition = {!!}

  cotype-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    indexing-type-snd-displayed-Σ-Decomposition x →
    UU l5
  cotype-snd-displayed-Σ-Decomposition = {!!}

  matching-correspondence-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    ( cotype-fst-displayed-Σ-Decomposition x ≃
      Σ ( indexing-type-snd-displayed-Σ-Decomposition x)
        ( cotype-snd-displayed-Σ-Decomposition x))
  matching-correspondence-snd-displayed-Σ-Decomposition = {!!}

  map-matching-correspondence-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    cotype-fst-displayed-Σ-Decomposition x →
    Σ ( indexing-type-snd-displayed-Σ-Decomposition x)
      ( cotype-snd-displayed-Σ-Decomposition x)
  map-matching-correspondence-snd-displayed-Σ-Decomposition = {!!}
```

## Properties

### Characterization of equality of Σ-decompositions

```agda
equiv-Σ-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Σ-Decomposition l2 l3 A) (Y : Σ-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Σ-Decomposition l2 l3 A) (Y : Σ-Decomposition l4 l5 A)
  (e : equiv-Σ-Decomposition X Y)
  where

  equiv-indexing-type-equiv-Σ-Decomposition :
    indexing-type-Σ-Decomposition X ≃ indexing-type-Σ-Decomposition Y
  equiv-indexing-type-equiv-Σ-Decomposition = {!!}

  map-equiv-indexing-type-equiv-Σ-Decomposition :
    indexing-type-Σ-Decomposition X → indexing-type-Σ-Decomposition Y
  map-equiv-indexing-type-equiv-Σ-Decomposition = {!!}

  equiv-cotype-equiv-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition X) →
    cotype-Σ-Decomposition X x ≃
    cotype-Σ-Decomposition Y (map-equiv-indexing-type-equiv-Σ-Decomposition x)
  equiv-cotype-equiv-Σ-Decomposition = {!!}

  map-equiv-cotype-equiv-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition X) →
    cotype-Σ-Decomposition X x →
    cotype-Σ-Decomposition Y (map-equiv-indexing-type-equiv-Σ-Decomposition x)
  map-equiv-cotype-equiv-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : Σ-Decomposition l2 l3 A)
  where

  id-equiv-Σ-Decomposition : equiv-Σ-Decomposition X X
  id-equiv-Σ-Decomposition = {!!}

  is-torsorial-equiv-Σ-Decomposition :
    is-torsorial (equiv-Σ-Decomposition X)
  is-torsorial-equiv-Σ-Decomposition = {!!}

  equiv-eq-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → (X ＝ Y) → equiv-Σ-Decomposition X Y
  equiv-eq-Σ-Decomposition = {!!}

  is-equiv-equiv-eq-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → is-equiv (equiv-eq-Σ-Decomposition Y)
  is-equiv-equiv-eq-Σ-Decomposition = {!!}

  extensionality-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → (X ＝ Y) ≃ equiv-Σ-Decomposition X Y
  extensionality-Σ-Decomposition = {!!}

  eq-equiv-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → equiv-Σ-Decomposition X Y → (X ＝ Y)
  eq-equiv-Σ-Decomposition = {!!}
```

### Invariance of Σ-decompositions under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  equiv-tr-Σ-Decomposition :
    {l3 l4 : Level} → Σ-Decomposition l3 l4 A ≃ Σ-Decomposition l3 l4 B
  equiv-tr-Σ-Decomposition = {!!}

  map-equiv-tr-Σ-Decomposition :
    {l3 l4 : Level} → Σ-Decomposition l3 l4 A → Σ-Decomposition l3 l4 B
  map-equiv-tr-Σ-Decomposition = {!!}
```

### Characterization of equality of set-indexed Σ-decompositions

```agda
equiv-Set-Indexed-Σ-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Set-Indexed-Σ-Decomposition l2 l3 A)
  (Y : Set-Indexed-Σ-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Set-Indexed-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : Set-Indexed-Σ-Decomposition l2 l3 A)
  where

  id-equiv-Set-Indexed-Σ-Decomposition : equiv-Set-Indexed-Σ-Decomposition X X
  id-equiv-Set-Indexed-Σ-Decomposition = {!!}

  is-torsorial-equiv-Set-Indexed-Σ-Decomposition :
    is-torsorial (equiv-Set-Indexed-Σ-Decomposition X)
  is-torsorial-equiv-Set-Indexed-Σ-Decomposition = {!!}

  equiv-eq-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    (X ＝ Y) → equiv-Set-Indexed-Σ-Decomposition X Y
  equiv-eq-Set-Indexed-Σ-Decomposition = {!!}

  is-equiv-equiv-eq-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    is-equiv (equiv-eq-Set-Indexed-Σ-Decomposition Y)
  is-equiv-equiv-eq-Set-Indexed-Σ-Decomposition = {!!}

  extensionality-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    (X ＝ Y) ≃ equiv-Set-Indexed-Σ-Decomposition X Y
  extensionality-Set-Indexed-Σ-Decomposition = {!!}

  eq-equiv-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    equiv-Set-Indexed-Σ-Decomposition X Y → (X ＝ Y)
  eq-equiv-Set-Indexed-Σ-Decomposition = {!!}
```

### Iterated Σ-decompositions

#### Characterization of identity type for fibered double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : fibered-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-fibered-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-fibered-Σ-Decomposition = {!!}

  equiv-snd-fibered-Σ-Decomposition :
    (e : equiv-fst-fibered-Σ-Decomposition) →
    UU (l4 ⊔ l5 ⊔ l6 ⊔ l8 ⊔ l9)
  equiv-snd-fibered-Σ-Decomposition = {!!}

  equiv-fibered-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-fibered-Σ-Decomposition = {!!}

  fst-equiv-fibered-Σ-Decomposition :
    (e : equiv-fibered-Σ-Decomposition) →
    equiv-fst-fibered-Σ-Decomposition
  fst-equiv-fibered-Σ-Decomposition = {!!}

  snd-equiv-fibered-Σ-Decomposition :
    (e : equiv-fibered-Σ-Decomposition) →
    equiv-snd-fibered-Σ-Decomposition
      (fst-equiv-fibered-Σ-Decomposition e)
  snd-equiv-fibered-Σ-Decomposition = {!!}

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( D : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = {!!}

  is-torsorial-equiv-fibered-Σ-Decomposition :
    is-torsorial (equiv-fibered-Σ-Decomposition D)
  is-torsorial-equiv-fibered-Σ-Decomposition = {!!}

  id-equiv-fibered-Σ-Decomposition :
    equiv-fibered-Σ-Decomposition D D
  id-equiv-fibered-Σ-Decomposition = {!!}

  equiv-eq-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') → equiv-fibered-Σ-Decomposition D D'
  equiv-eq-fibered-Σ-Decomposition = {!!}

  is-equiv-equiv-eq-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-fibered-Σ-Decomposition D')
  is-equiv-equiv-eq-fibered-Σ-Decomposition = {!!}

  extensionality-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') ≃ equiv-fibered-Σ-Decomposition D D'
  extensionality-fibered-Σ-Decomposition = {!!}

  eq-equiv-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    (equiv-fibered-Σ-Decomposition D D') → (D ＝ D')
  eq-equiv-fibered-Σ-Decomposition = {!!}
```

#### Characterization of identity type for displayed double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : displayed-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-displayed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-displayed-Σ-Decomposition = {!!}

  equiv-snd-displayed-Σ-Decomposition :
    (e : equiv-fst-displayed-Σ-Decomposition) →
    UU (l2 ⊔ l4 ⊔ l5 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-snd-displayed-Σ-Decomposition = {!!}

  equiv-displayed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-displayed-Σ-Decomposition = {!!}

  fst-equiv-displayed-Σ-Decomposition :
    (e : equiv-displayed-Σ-Decomposition) →
    equiv-fst-displayed-Σ-Decomposition
  fst-equiv-displayed-Σ-Decomposition = {!!}

  snd-equiv-displayed-Σ-Decomposition :
    (e : equiv-displayed-Σ-Decomposition) →
    equiv-snd-displayed-Σ-Decomposition
      ( fst-equiv-displayed-Σ-Decomposition e)
  snd-equiv-displayed-Σ-Decomposition = {!!}

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( disp-D : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = {!!}

  is-torsorial-equiv-displayed-Σ-Decomposition :
    is-torsorial (equiv-displayed-Σ-Decomposition disp-D)
  is-torsorial-equiv-displayed-Σ-Decomposition = {!!}

  id-equiv-displayed-Σ-Decomposition :
    equiv-displayed-Σ-Decomposition disp-D disp-D
  id-equiv-displayed-Σ-Decomposition = {!!}

  equiv-eq-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') → equiv-displayed-Σ-Decomposition disp-D disp-D'
  equiv-eq-displayed-Σ-Decomposition = {!!}

  is-equiv-equiv-eq-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-displayed-Σ-Decomposition disp-D')
  is-equiv-equiv-eq-displayed-Σ-Decomposition = {!!}

  extensionality-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') ≃ equiv-displayed-Σ-Decomposition disp-D disp-D'
  extensionality-displayed-Σ-Decomposition = {!!}

  eq-equiv-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    (equiv-displayed-Σ-Decomposition disp-D disp-D') → (disp-D ＝ disp-D')
  eq-equiv-displayed-Σ-Decomposition = {!!}
```

#### Equivalence between fibered double Σ-decompositions and displayed double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (fib-D : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = {!!}

  matching-correspondence-displayed-fibered-Σ-Decomposition :
    A ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
  matching-correspondence-displayed-fibered-Σ-Decomposition = {!!}

  map-displayed-fibered-Σ-Decomposition :
    displayed-Σ-Decomposition l4 (l3 ⊔ l5) l5 l3 A
  pr1 (pr1 map-displayed-fibered-Σ-Decomposition) = {!!}

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (disp-D : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    M = {!!}

  matching-correspondence-inv-displayed-fibered-Σ-Decomposition :
    A ≃ Σ (Σ M P) (λ (m , p) → Q m p)
  matching-correspondence-inv-displayed-fibered-Σ-Decomposition = {!!}

  map-inv-displayed-fibered-Σ-Decomposition :
    fibered-Σ-Decomposition (l2 ⊔ l4) l5 l2 l4 A
  pr1 (pr1 map-inv-displayed-fibered-Σ-Decomposition) = {!!}

module _
  {l1 l : Level} {A : UU l1}
  (fib-D : fibered-Σ-Decomposition l l l l A)
  where

  private
    X = {!!}

    htpy-matching-correspondence :
      ( map-equiv
        ( ( equiv-Σ Y (inv-equiv f) (λ (m , p) → id-equiv)) ∘e
          ( matching-correspondence-inv-displayed-fibered-Σ-Decomposition
            ( disp-D)))) ~
      ( map-equiv e)
    htpy-matching-correspondence = {!!}

  is-retraction-map-inv-displayed-fibered-Σ-Decomposition :
    map-inv-displayed-fibered-Σ-Decomposition
      ( map-displayed-fibered-Σ-Decomposition fib-D) ＝ fib-D
  is-retraction-map-inv-displayed-fibered-Σ-Decomposition = {!!}

module _
  {l1 l : Level} {A : UU l1}
  (disp-D : displayed-Σ-Decomposition l l l l A)
  where

  private
    M = {!!}

    htpy-matching-correspondence :
      map-equiv
        ( equiv-Σ N id-equiv (inv-equiv ∘ t) ∘e
          matching-correspondence-displayed-fibered-Σ-Decomposition
            (fib-D)) ~
      map-equiv s
    htpy-matching-correspondence = {!!}

  is-section-map-inv-displayed-fibered-Σ-Decomposition :
    ( map-displayed-fibered-Σ-Decomposition
      {l1} {l} {l} {l} {l} {A} fib-D) ＝
    disp-D
  is-section-map-inv-displayed-fibered-Σ-Decomposition = {!!}

is-equiv-map-displayed-fibered-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  is-equiv
    ( map-displayed-fibered-Σ-Decomposition {l1} {l} {l} {l} {l} {A})
is-equiv-map-displayed-fibered-Σ-Decomposition = {!!}

equiv-displayed-fibered-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  fibered-Σ-Decomposition l l l l A ≃
  displayed-Σ-Decomposition l l l l A
equiv-displayed-fibered-Σ-Decomposition = {!!}
pr2 equiv-displayed-fibered-Σ-Decomposition = {!!}
```
