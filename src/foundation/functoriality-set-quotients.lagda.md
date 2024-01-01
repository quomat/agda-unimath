# Functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.logical-equivalences
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

### Maps preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  preserves-sim-prop-equivalence-relation : (f : A → B) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-sim-prop-equivalence-relation f = {!!}

  preserves-sim-equivalence-relation : (f : A → B) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-sim-equivalence-relation f = {!!}

  is-prop-preserves-sim-equivalence-relation :
    (f : A → B) → is-prop (preserves-sim-equivalence-relation f)
  is-prop-preserves-sim-equivalence-relation f = {!!}

  hom-equivalence-relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-equivalence-relation = {!!}

  map-hom-equivalence-relation : hom-equivalence-relation → A → B
  map-hom-equivalence-relation = {!!}

  preserves-sim-hom-equivalence-relation :
    (f : hom-equivalence-relation) {x y : A} →
    sim-equivalence-relation R x y →
    sim-equivalence-relation
      ( S)
      ( map-hom-equivalence-relation f x)
      ( map-hom-equivalence-relation f y)
  preserves-sim-hom-equivalence-relation = {!!}

id-hom-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  hom-equivalence-relation R R
pr1 (id-hom-equivalence-relation R) = {!!}
pr2 (id-hom-equivalence-relation R) = {!!}
```

### Equivalences preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  equiv-equivalence-relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-equivalence-relation = {!!}

  equiv-equiv-equivalence-relation : equiv-equivalence-relation → A ≃ B
  equiv-equiv-equivalence-relation = {!!}

  map-equiv-equivalence-relation : equiv-equivalence-relation → A → B
  map-equiv-equivalence-relation e = {!!}

  map-inv-equiv-equivalence-relation : equiv-equivalence-relation → B → A
  map-inv-equiv-equivalence-relation e = {!!}

  is-equiv-map-equiv-equivalence-relation :
    (e : equiv-equivalence-relation) →
    is-equiv (map-equiv-equivalence-relation e)
  is-equiv-map-equiv-equivalence-relation e = {!!}

  equiv-sim-equiv-equivalence-relation :
    (e : equiv-equivalence-relation) {x y : A} →
    sim-equivalence-relation R x y ↔
    sim-equivalence-relation
      ( S)
      ( map-equiv-equivalence-relation e x)
      ( map-equiv-equivalence-relation e y)
  equiv-sim-equiv-equivalence-relation = {!!}

  preserves-sim-equiv-equivalence-relation :
    (e : equiv-equivalence-relation) {x y : A} →
    sim-equivalence-relation R x y →
    sim-equivalence-relation
      ( S)
      ( map-equiv-equivalence-relation e x)
      ( map-equiv-equivalence-relation e y)
  preserves-sim-equiv-equivalence-relation e = {!!}

  hom-equiv-equivalence-relation :
    equiv-equivalence-relation → hom-equivalence-relation R S
  pr1 (hom-equiv-equivalence-relation e) = {!!}

id-equiv-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) →
  equiv-equivalence-relation R R
pr1 (id-equiv-equivalence-relation R) = {!!}
pr1 (pr2 (id-equiv-equivalence-relation R)) = {!!}
pr2 (pr2 (id-equiv-equivalence-relation R)) = {!!}
```

### Maps between types satisfying the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (f : reflecting-map-equivalence-relation R (type-Set QR))
  {B : UU l4} (S : equivalence-relation l5 B)
  (QS : Set l6) (g : reflecting-map-equivalence-relation S (type-Set QS))
  where

  unique-map-is-set-quotient :
    is-set-quotient R QR f → is-set-quotient S QS g →
    (h : hom-equivalence-relation R S) →
    is-contr
      ( Σ ( type-Set QR → type-Set QS)
          ( coherence-square-maps
            ( map-hom-equivalence-relation R S h)
            ( map-reflecting-map-equivalence-relation R f)
            ( map-reflecting-map-equivalence-relation S g)))
  unique-map-is-set-quotient Uf Ug h = {!!}

  map-is-set-quotient :
    is-set-quotient R QR f → is-set-quotient S QS g →
    (h : hom-equivalence-relation R S) →
    type-Set QR → type-Set QS
  map-is-set-quotient Uf Ug h = {!!}

  coherence-square-map-is-set-quotient :
    (Uf : is-set-quotient R QR f) →
    (Ug : is-set-quotient S QS g) →
    (h : hom-equivalence-relation R S) →
    coherence-square-maps
      ( map-hom-equivalence-relation R S h)
      ( map-reflecting-map-equivalence-relation R f)
      ( map-reflecting-map-equivalence-relation S g)
      ( map-is-set-quotient Uf Ug h)
  coherence-square-map-is-set-quotient Uf Ug h = {!!}
```

### Functoriality of the set quotient

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  unique-map-set-quotient :
    (h : hom-equivalence-relation R S) →
    is-contr
      ( Σ ( set-quotient R → set-quotient S)
          ( coherence-square-maps
            ( map-hom-equivalence-relation R S h)
            ( quotient-map R)
            ( quotient-map S)))
  unique-map-set-quotient = {!!}

  map-set-quotient :
    (h : hom-equivalence-relation R S) → set-quotient R → set-quotient S
  map-set-quotient = {!!}

  coherence-square-map-set-quotient :
    (h : hom-equivalence-relation R S) →
    coherence-square-maps
      ( map-hom-equivalence-relation R S h)
      ( quotient-map R)
      ( quotient-map S)
      ( map-set-quotient h)
  coherence-square-map-set-quotient = {!!}
```

## Properties

### Composition of reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5}
  where

  comp-reflecting-map-equivalence-relation :
    reflecting-map-equivalence-relation S C → hom-equivalence-relation R S →
    reflecting-map-equivalence-relation R C
  pr1 (comp-reflecting-map-equivalence-relation g f) = {!!}
```

### Characterizing equality of `hom-equivalence-relation`

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  htpy-hom-equivalence-relation :
    (f g : hom-equivalence-relation R S) → UU (l1 ⊔ l3)
  htpy-hom-equivalence-relation f g = {!!}

  refl-htpy-hom-equivalence-relation :
    (f : hom-equivalence-relation R S) → htpy-hom-equivalence-relation f f
  refl-htpy-hom-equivalence-relation f = {!!}

  htpy-eq-hom-equivalence-relation :
    (f g : hom-equivalence-relation R S) →
    (f ＝ g) → htpy-hom-equivalence-relation f g
  htpy-eq-hom-equivalence-relation f .f refl = {!!}

  is-torsorial-htpy-hom-equivalence-relation :
    (f : hom-equivalence-relation R S) →
    is-torsorial (htpy-hom-equivalence-relation f)
  is-torsorial-htpy-hom-equivalence-relation f = {!!}

  is-equiv-htpy-eq-hom-equivalence-relation :
    (f g : hom-equivalence-relation R S) →
    is-equiv (htpy-eq-hom-equivalence-relation f g)
  is-equiv-htpy-eq-hom-equivalence-relation f = {!!}

  extensionality-hom-equivalence-relation :
    (f g : hom-equivalence-relation R S) →
    (f ＝ g) ≃ htpy-hom-equivalence-relation f g
  pr1 (extensionality-hom-equivalence-relation f g) = {!!}

  eq-htpy-hom-equivalence-relation :
    (f g : hom-equivalence-relation R S) →
    htpy-hom-equivalence-relation f g → (f ＝ g)
  eq-htpy-hom-equivalence-relation f g = {!!}
```

### Functoriality of set quotients preserves equivalences

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (f : reflecting-map-equivalence-relation R (type-Set QR))
  {B : UU l4} (S : equivalence-relation l5 B)
  (QS : Set l6) (g : reflecting-map-equivalence-relation S (type-Set QS))
  where

  unique-equiv-is-set-quotient :
    is-set-quotient R QR f → is-set-quotient S QS g →
    (h : equiv-equivalence-relation R S) →
    is-contr
      ( Σ ( type-Set QR ≃ type-Set QS)
          ( λ h' →
            coherence-square-maps
              ( map-equiv-equivalence-relation R S h)
              ( map-reflecting-map-equivalence-relation R f)
              ( map-reflecting-map-equivalence-relation S g)
              ( map-equiv h')))
  unique-equiv-is-set-quotient Uf Ug h = {!!}

  equiv-is-set-quotient :
    is-set-quotient R QR f →
    is-set-quotient S QS g →
    (h : equiv-equivalence-relation R S) → type-Set QR ≃ type-Set QS
  equiv-is-set-quotient Uf Ug h = {!!}

  coherence-square-equiv-is-set-quotient :
    (Uf : is-set-quotient R QR f) →
    (Ug : is-set-quotient S QS g) →
    (h : equiv-equivalence-relation R S) →
    coherence-square-maps (map-equiv-equivalence-relation R S h)
      ( map-reflecting-map-equivalence-relation R f)
      ( map-reflecting-map-equivalence-relation S g)
      ( map-equiv (equiv-is-set-quotient Uf Ug h))
  coherence-square-equiv-is-set-quotient Uf Ug h = {!!}
```

### Functoriality of set quotients preserves identity maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (f : reflecting-map-equivalence-relation R (type-Set QR))
  where

  id-map-is-set-quotient :
    (Uf : is-set-quotient R QR f) →
    map-is-set-quotient R QR f R QR f Uf Uf (id-hom-equivalence-relation R) ~ id
  id-map-is-set-quotient Uf x = {!!}

  id-equiv-is-set-quotient :
    (Uf : is-set-quotient R QR f) →
    htpy-equiv
      ( equiv-is-set-quotient R QR f R QR f Uf Uf
        ( id-equiv-equivalence-relation R))
      ( id-equiv)
  id-equiv-is-set-quotient Uf x = {!!}
```
