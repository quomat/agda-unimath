# Morphisms of algebras of polynomial endofunctors

```agda
module trees.morphisms-algebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import trees.algebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

A **morphism** of algebras of a polynomial endofunctor `P A B` consists of a map
`f : X → Y$ between the underlying types, equipped with a homotopy witnessing
that the square

```text
           P A B f
  P A B X ---------> P A B Y
      |                |
      |                |
      V                V
      X -------------> Y
               f
```

commutes.

## Definitions

### Morphisms of algebras for polynomial endofunctors

```agda
hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (Y : algebra-polynomial-endofunctor l4 A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-algebra-polynomial-endofunctor = {!!}

map-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (Y : algebra-polynomial-endofunctor l4 A B) →
  hom-algebra-polynomial-endofunctor X Y →
  type-algebra-polynomial-endofunctor X →
  type-algebra-polynomial-endofunctor Y
map-hom-algebra-polynomial-endofunctor = {!!}

structure-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (Y : algebra-polynomial-endofunctor l4 A B) →
  (f : hom-algebra-polynomial-endofunctor X Y) →
  ( ( map-hom-algebra-polynomial-endofunctor X Y f) ∘
    ( structure-algebra-polynomial-endofunctor X)) ~
  ( ( structure-algebra-polynomial-endofunctor Y) ∘
    ( map-polynomial-endofunctor A B
      ( map-hom-algebra-polynomial-endofunctor X Y f)))
structure-hom-algebra-polynomial-endofunctor = {!!}
```

## Properties

### The identity type of morphisms of algebras of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B)
  (Y : algebra-polynomial-endofunctor l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y)
  where

  htpy-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-algebra-polynomial-endofunctor = {!!}

  refl-htpy-hom-algebra-polynomial-endofunctor :
    htpy-hom-algebra-polynomial-endofunctor f
  refl-htpy-hom-algebra-polynomial-endofunctor = {!!}

  htpy-eq-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    f ＝ g → htpy-hom-algebra-polynomial-endofunctor g
  htpy-eq-hom-algebra-polynomial-endofunctor = {!!}

  is-torsorial-htpy-hom-algebra-polynomial-endofunctor :
    is-torsorial htpy-hom-algebra-polynomial-endofunctor
  is-torsorial-htpy-hom-algebra-polynomial-endofunctor = {!!}

  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    is-equiv (htpy-eq-hom-algebra-polynomial-endofunctor g)
  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor = {!!}

  extensionality-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    (f ＝ g) ≃ htpy-hom-algebra-polynomial-endofunctor g
  extensionality-hom-algebra-polynomial-endofunctor = {!!}

  eq-htpy-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    htpy-hom-algebra-polynomial-endofunctor g → f ＝ g
  eq-htpy-hom-algebra-polynomial-endofunctor = {!!}
```
