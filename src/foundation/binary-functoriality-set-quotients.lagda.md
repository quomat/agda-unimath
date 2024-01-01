# Binary functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.binary-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.exponents-set-quotients
open import foundation.function-extensionality
open import foundation.functoriality-set-quotients
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given three types `A`, `B`, and `C` equipped with equivalence relations `R`,
`S`, and `T`, respectively, any binary operation `f : A → B → C` such that for
any `x x' : A` such that `R x x'` holds, and for any `y y' : B` such that
`S y y'` holds, the relation `T (f x y) (f x' y')` holds extends uniquely to a
binary operation `g : A/R → B/S → C/T` such that `g (q x) (q y) = {!!}
all `x : A` and `y : B`.

## Definition

### Binary hom of equivalence relation

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5} (T : equivalence-relation l6 C)
  where

  preserves-sim-prop-binary-map-equivalence-relation :
    (A → B → C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  preserves-sim-prop-binary-map-equivalence-relation f = {!!}

  preserves-sim-binary-map-equivalence-relation :
    (A → B → C) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  preserves-sim-binary-map-equivalence-relation f = {!!}

  is-prop-preserves-sim-binary-map-equivalence-relation :
    (f : A → B → C) → is-prop (preserves-sim-binary-map-equivalence-relation f)
  is-prop-preserves-sim-binary-map-equivalence-relation f = {!!}

  binary-hom-equivalence-relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  binary-hom-equivalence-relation = {!!}

  map-binary-hom-equivalence-relation :
    (f : binary-hom-equivalence-relation) → A → B → C
  map-binary-hom-equivalence-relation = {!!}

  preserves-sim-binary-hom-equivalence-relation :
    (f : binary-hom-equivalence-relation) →
    preserves-sim-binary-map-equivalence-relation
      ( map-binary-hom-equivalence-relation f)
  preserves-sim-binary-hom-equivalence-relation = {!!}
```

## Properties

### Characterization of equality of `binary-hom-equivalence-relation`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5} (T : equivalence-relation l6 C)
  where

  binary-htpy-hom-equivalence-relation :
    (f g : binary-hom-equivalence-relation R S T) → UU (l1 ⊔ l3 ⊔ l5)
  binary-htpy-hom-equivalence-relation f g = {!!}

  refl-binary-htpy-hom-equivalence-relation :
    (f : binary-hom-equivalence-relation R S T) →
    binary-htpy-hom-equivalence-relation f f
  refl-binary-htpy-hom-equivalence-relation f = {!!}

  binary-htpy-eq-hom-equivalence-relation :
    (f g : binary-hom-equivalence-relation R S T) →
    (f ＝ g) → binary-htpy-hom-equivalence-relation f g
  binary-htpy-eq-hom-equivalence-relation f .f refl = {!!}

  is-torsorial-binary-htpy-hom-equivalence-relation :
    (f : binary-hom-equivalence-relation R S T) →
    is-torsorial (binary-htpy-hom-equivalence-relation f)
  is-torsorial-binary-htpy-hom-equivalence-relation f = {!!}

  is-equiv-binary-htpy-eq-hom-equivalence-relation :
    (f g : binary-hom-equivalence-relation R S T) →
    is-equiv (binary-htpy-eq-hom-equivalence-relation f g)
  is-equiv-binary-htpy-eq-hom-equivalence-relation f = {!!}

  extensionality-binary-hom-equivalence-relation :
    (f g : binary-hom-equivalence-relation R S T) →
    (f ＝ g) ≃ binary-htpy-hom-equivalence-relation f g
  pr1 (extensionality-binary-hom-equivalence-relation f g) = {!!}

  eq-binary-htpy-hom-equivalence-relation :
    (f g : binary-hom-equivalence-relation R S T) →
    binary-htpy-hom-equivalence-relation f g → f ＝ g
  eq-binary-htpy-hom-equivalence-relation f g = {!!}
```

### The type `binary-hom-equivalence-relation R S T` is equivalent to the type `hom-equivalence-relation R (equivalence-relation-hom-equivalence-relation S T)`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5} (T : equivalence-relation l6 C)
  where

  map-hom-binary-hom-equivalence-relation :
    binary-hom-equivalence-relation R S T → A → hom-equivalence-relation S T
  pr1 (map-hom-binary-hom-equivalence-relation f a) = {!!}

  preserves-sim-hom-binary-hom-equivalence-relation :
    (f : binary-hom-equivalence-relation R S T) →
    preserves-sim-equivalence-relation R
      ( equivalence-relation-hom-equivalence-relation S T)
      ( map-hom-binary-hom-equivalence-relation f)
  preserves-sim-hom-binary-hom-equivalence-relation f r b = {!!}

  hom-binary-hom-equivalence-relation :
    binary-hom-equivalence-relation R S T →
    hom-equivalence-relation R
      ( equivalence-relation-hom-equivalence-relation S T)
  pr1 (hom-binary-hom-equivalence-relation f) = {!!}

  map-binary-hom-hom-equivalence-relation :
    hom-equivalence-relation R
      ( equivalence-relation-hom-equivalence-relation S T) →
    A → B → C
  map-binary-hom-hom-equivalence-relation f x = {!!}

  preserves-sim-binary-hom-hom-equivalence-relation :
    (f :
      hom-equivalence-relation R
        ( equivalence-relation-hom-equivalence-relation S T)) →
    preserves-sim-binary-map-equivalence-relation R S T
      ( map-binary-hom-hom-equivalence-relation f)
  preserves-sim-binary-hom-hom-equivalence-relation f {x} {x'} {y} {y'} r s = {!!}

  binary-hom-hom-equivalence-relation :
    hom-equivalence-relation R
      ( equivalence-relation-hom-equivalence-relation S T) →
    binary-hom-equivalence-relation R S T
  pr1 (binary-hom-hom-equivalence-relation f) = {!!}

  is-section-binary-hom-hom-equivalence-relation :
    ( hom-binary-hom-equivalence-relation ∘
      binary-hom-hom-equivalence-relation) ~
    id
  is-section-binary-hom-hom-equivalence-relation f = {!!}

  is-retraction-binary-hom-hom-equivalence-relation :
    ( binary-hom-hom-equivalence-relation ∘
      hom-binary-hom-equivalence-relation) ~
    id
  is-retraction-binary-hom-hom-equivalence-relation f = {!!}

  is-equiv-hom-binary-hom-equivalence-relation :
    is-equiv hom-binary-hom-equivalence-relation
  is-equiv-hom-binary-hom-equivalence-relation = {!!}

  equiv-hom-binary-hom-equivalence-relation :
    binary-hom-equivalence-relation R S T ≃
    hom-equivalence-relation R
      ( equivalence-relation-hom-equivalence-relation S T)
  pr1 equiv-hom-binary-hom-equivalence-relation = {!!}
```

### Binary functoriality of types that satisfy the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (qR : reflecting-map-equivalence-relation R (type-Set QR))
  {B : UU l4} (S : equivalence-relation l5 B)
  (QS : Set l6) (qS : reflecting-map-equivalence-relation S (type-Set QS))
  {C : UU l7} (T : equivalence-relation l8 C)
  (QT : Set l9) (qT : reflecting-map-equivalence-relation T (type-Set QT))
  (UqR : is-set-quotient R QR qR)
  (UqS : is-set-quotient S QS qS)
  (UqT : is-set-quotient T QT qT)
  (f : binary-hom-equivalence-relation R S T)
  where

  private
    p :
      (x : A) (y : B) →
      map-reflecting-map-equivalence-relation T qT
        ( map-binary-hom-equivalence-relation R S T f x y) ＝
      inclusion-is-set-quotient-hom-equivalence-relation S QS qS UqS T QT qT UqT
        ( quotient-hom-equivalence-relation-Set S T)
        ( reflecting-map-quotient-map-hom-equivalence-relation S T)
        ( is-set-quotient-set-quotient-hom-equivalence-relation S T)
        ( quotient-map-hom-equivalence-relation S T
          ( map-hom-binary-hom-equivalence-relation R S T f x))
        ( map-reflecting-map-equivalence-relation S qS y)
    p x y = {!!}

  unique-binary-map-is-set-quotient :
    is-contr
      ( Σ ( type-Set QR → type-Set QS → type-Set QT)
          ( λ h →
            (x : A) (y : B) →
            ( h ( map-reflecting-map-equivalence-relation R qR x)
                ( map-reflecting-map-equivalence-relation S qS y)) ＝
            ( map-reflecting-map-equivalence-relation T qT
              ( map-binary-hom-equivalence-relation R S T f x y))))
  unique-binary-map-is-set-quotient = {!!}

  binary-map-is-set-quotient : hom-Set QR (hom-set-Set QS QT)
  binary-map-is-set-quotient = {!!}

  compute-binary-map-is-set-quotient :
    (x : A) (y : B) →
    binary-map-is-set-quotient
      ( map-reflecting-map-equivalence-relation R qR x)
      ( map-reflecting-map-equivalence-relation S qS y) ＝
    map-reflecting-map-equivalence-relation
      T qT (map-binary-hom-equivalence-relation R S T f x y)
  compute-binary-map-is-set-quotient = {!!}
```

### Binary functoriality of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5} (T : equivalence-relation l6 C)
  (f : binary-hom-equivalence-relation R S T)
  where

  unique-binary-map-set-quotient :
    is-contr
      ( Σ ( set-quotient R → set-quotient S → set-quotient T)
          ( λ h →
            (x : A) (y : B) →
            ( h (quotient-map R x) (quotient-map S y)) ＝
            ( quotient-map T
              ( map-binary-hom-equivalence-relation R S T f x y))))
  unique-binary-map-set-quotient = {!!}

  binary-map-set-quotient : set-quotient R → set-quotient S → set-quotient T
  binary-map-set-quotient = {!!}

  compute-binary-map-set-quotient :
    (x : A) (y : B) →
    ( binary-map-set-quotient (quotient-map R x) (quotient-map S y)) ＝
    ( quotient-map T (map-binary-hom-equivalence-relation R S T f x y))
  compute-binary-map-set-quotient = {!!}
```
