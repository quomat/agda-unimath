# Morphisms of coalgebras of polynomial endofunctors

```agda
module trees.morphisms-coalgebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import trees.coalgebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

A **morphism** of coalgebras of a polynomial endofunctor `P A B` consists of a
function `f : X → Y` between their underlying types, equipped with a homotopy
witnessing that the square

```text
              f
      X -------------> Y
      |                |
      |                |
      V                V
  P A B X ---------> P A B Y
           P A B f
```

commutes.

## Definitions

### Morphisms of coalgebras for polynomial endofunctors

```agda
hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B) →
  (Y : coalgebra-polynomial-endofunctor l4 A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-coalgebra-polynomial-endofunctor {A = A} {B} X Y = {!!}

map-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B) →
  (Y : coalgebra-polynomial-endofunctor l4 A B) →
  hom-coalgebra-polynomial-endofunctor X Y →
  type-coalgebra-polynomial-endofunctor X →
  type-coalgebra-polynomial-endofunctor Y
map-hom-coalgebra-polynomial-endofunctor X Y f = {!!}

structure-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B) →
  (Y : coalgebra-polynomial-endofunctor l4 A B) →
  (f : hom-coalgebra-polynomial-endofunctor X Y) →
  coherence-square-maps
    ( map-hom-coalgebra-polynomial-endofunctor X Y f)
    ( structure-coalgebra-polynomial-endofunctor X)
    ( structure-coalgebra-polynomial-endofunctor Y)
    ( map-polynomial-endofunctor A B
      ( map-hom-coalgebra-polynomial-endofunctor X Y f))
structure-hom-coalgebra-polynomial-endofunctor X Y f = {!!}
```

## Properties

### The identity type of morphisms of coalgebras of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B)
  (Y : coalgebra-polynomial-endofunctor l4 A B)
  (f : hom-coalgebra-polynomial-endofunctor X Y)
  where

  htpy-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-coalgebra-polynomial-endofunctor g = {!!}

  refl-htpy-hom-coalgebra-polynomial-endofunctor :
    htpy-hom-coalgebra-polynomial-endofunctor f
  pr1 refl-htpy-hom-coalgebra-polynomial-endofunctor = {!!}

  htpy-eq-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    f ＝ g → htpy-hom-coalgebra-polynomial-endofunctor g
  htpy-eq-hom-coalgebra-polynomial-endofunctor .f refl = {!!}

  is-torsorial-htpy-hom-coalgebra-polynomial-endofunctor :
    is-torsorial htpy-hom-coalgebra-polynomial-endofunctor
  is-torsorial-htpy-hom-coalgebra-polynomial-endofunctor = {!!}

  is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    is-equiv (htpy-eq-hom-coalgebra-polynomial-endofunctor g)
  is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctor = {!!}

  extensionality-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    (f ＝ g) ≃ htpy-hom-coalgebra-polynomial-endofunctor g
  pr1 (extensionality-hom-coalgebra-polynomial-endofunctor g) = {!!}
  pr2 (extensionality-hom-coalgebra-polynomial-endofunctor g) = {!!}

  eq-htpy-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    htpy-hom-coalgebra-polynomial-endofunctor g → f ＝ g
  eq-htpy-hom-coalgebra-polynomial-endofunctor g = {!!}
```
