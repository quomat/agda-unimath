# Exponents of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.exponents-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-set-quotients
open import foundation.postcomposition-functions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a type `A` equipped with an equivalence relation `R` and a type `X`, the
set quotient

```text
  (X → A) / ~
```

where `f ~ g := {!!}
embedding for every `X`, `A`, and `R` if and only if the axiom of choice holds.

Consequently, we get embeddings

```text
  ((hom-equivalence-relation R S) / ~) ↪ ((A/R) → (B/S))
```

for any two equivalence relations `R` on `A` and `S` on `B`.

## Definitions

### The canonical equivalence relation on `X → A`

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} (R : equivalence-relation l3 A)
  where

  rel-function-type : Relation-Prop (l1 ⊔ l3) (X → A)
  rel-function-type = {!!}

  sim-function-type : (f g : X → A) → UU (l1 ⊔ l3)
  sim-function-type = {!!}

  refl-sim-function-type : is-reflexive sim-function-type
  refl-sim-function-type = {!!}

  symmetric-sim-function-type : is-symmetric sim-function-type
  symmetric-sim-function-type = {!!}

  transitive-sim-function-type : is-transitive sim-function-type
  transitive-sim-function-type = {!!}

  equivalence-relation-function-type : equivalence-relation (l1 ⊔ l3) (X → A)
  equivalence-relation-function-type = {!!}

  map-exponent-reflecting-map-equivalence-relation :
    {l4 : Level} {B : UU l4} →
    reflecting-map-equivalence-relation R B → (X → A) → (X → B)
  map-exponent-reflecting-map-equivalence-relation = {!!}

  reflects-exponent-reflecting-map-equivalence-relation :
    {l4 : Level} {B : UU l4} (q : reflecting-map-equivalence-relation R B) →
    reflects-equivalence-relation equivalence-relation-function-type
      ( map-exponent-reflecting-map-equivalence-relation q)
  reflects-exponent-reflecting-map-equivalence-relation = {!!}

  exponent-reflecting-map-equivalence-relation :
    {l4 : Level} {B : UU l4} →
    reflecting-map-equivalence-relation R B →
    reflecting-map-equivalence-relation
      ( equivalence-relation-function-type)
      ( X → B)
  exponent-reflecting-map-equivalence-relation = {!!}

  module _
    {l4 l5 : Level}
    (Q : Set l4)
    (q :
      reflecting-map-equivalence-relation
        ( equivalence-relation-function-type)
        ( type-Set Q))
    (Uq : is-set-quotient equivalence-relation-function-type Q q)
    (QR : Set l5) (qR : reflecting-map-equivalence-relation R (type-Set QR))
    (UqR : is-set-quotient R QR qR)
    where

    unique-inclusion-is-set-quotient-equivalence-relation-function-type :
      is-contr
        ( Σ ( type-Set Q → (X → type-Set QR))
            ( λ h →
              ( h) ∘
              ( map-reflecting-map-equivalence-relation
                ( equivalence-relation-function-type)
                ( q))
              ~
              ( map-exponent-reflecting-map-equivalence-relation qR)))
    unique-inclusion-is-set-quotient-equivalence-relation-function-type = {!!}

    map-inclusion-is-set-quotient-equivalence-relation-function-type :
      type-Set Q → (X → type-Set QR)
    map-inclusion-is-set-quotient-equivalence-relation-function-type = {!!}

    triangle-inclusion-is-set-quotient-equivalence-relation-function-type :
      ( ( map-inclusion-is-set-quotient-equivalence-relation-function-type) ∘
        ( map-reflecting-map-equivalence-relation
          ( equivalence-relation-function-type)
          ( q))) ~
      ( map-exponent-reflecting-map-equivalence-relation qR)
    triangle-inclusion-is-set-quotient-equivalence-relation-function-type = {!!}
```

### An equivalence relation on relation preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  rel-hom-equivalence-relation :
    Relation-Prop (l1 ⊔ l4) (hom-equivalence-relation R S)
  rel-hom-equivalence-relation = {!!}

  sim-hom-equivalence-relation :
    (f g : hom-equivalence-relation R S) → UU (l1 ⊔ l4)
  sim-hom-equivalence-relation = {!!}

  refl-sim-hom-equivalence-relation : is-reflexive sim-hom-equivalence-relation
  refl-sim-hom-equivalence-relation = {!!}

  symmetric-sim-hom-equivalence-relation :
    is-symmetric sim-hom-equivalence-relation
  symmetric-sim-hom-equivalence-relation = {!!}

  transitive-sim-hom-equivalence-relation :
    is-transitive sim-hom-equivalence-relation
  transitive-sim-hom-equivalence-relation = {!!}

  equivalence-relation-hom-equivalence-relation :
    equivalence-relation (l1 ⊔ l4) (hom-equivalence-relation R S)
  equivalence-relation-hom-equivalence-relation = {!!}
```

### The universal reflecting map from `hom-equivalence-relation R S` to `A/R → B/S`

#### First variant using only the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (qR : reflecting-map-equivalence-relation R (type-Set QR))
  (UqR : is-set-quotient R QR qR)
  {B : UU l4} (S : equivalence-relation l5 B)
  (QS : Set l6) (qS : reflecting-map-equivalence-relation S (type-Set QS))
  (UqS : is-set-quotient S QS qS)
  where

  universal-map-is-set-quotient-hom-equivalence-relation :
    hom-equivalence-relation R S → hom-Set QR QS
  universal-map-is-set-quotient-hom-equivalence-relation = {!!}

  reflects-universal-map-is-set-quotient-hom-equivalence-relation :
    reflects-equivalence-relation
      ( equivalence-relation-hom-equivalence-relation R S)
      ( universal-map-is-set-quotient-hom-equivalence-relation)
  reflects-universal-map-is-set-quotient-hom-equivalence-relation = {!!}

  universal-reflecting-map-is-set-quotient-hom-equivalence-relation :
    reflecting-map-equivalence-relation
      ( equivalence-relation-hom-equivalence-relation R S)
      ( hom-Set QR QS)
  universal-reflecting-map-is-set-quotient-hom-equivalence-relation = {!!}
```

#### Second variant using the designated set quotients

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  universal-reflecting-map-set-quotient-hom-equivalence-relation :
    reflecting-map-equivalence-relation
      ( equivalence-relation-hom-equivalence-relation R S)
      ( set-quotient R → set-quotient S)
  universal-reflecting-map-set-quotient-hom-equivalence-relation = {!!}

  universal-map-set-quotient-hom-equivalence-relation :
    hom-equivalence-relation R S → set-quotient R → set-quotient S
  universal-map-set-quotient-hom-equivalence-relation = {!!}

  reflects-universal-map-set-quotient-hom-equivalence-relation :
    reflects-equivalence-relation
      ( equivalence-relation-hom-equivalence-relation R S)
      ( universal-map-set-quotient-hom-equivalence-relation)
  reflects-universal-map-set-quotient-hom-equivalence-relation = {!!}
```

## Properties

### The inclusion of the quotient `(X → A)/~` into `X → A/R` is an embedding

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : UU l1)
  {A : UU l2} (R : equivalence-relation l3 A)
  (Q : Set l4)
  (q :
    reflecting-map-equivalence-relation
      ( equivalence-relation-function-type X R)
      ( type-Set Q))
  (Uq : is-set-quotient (equivalence-relation-function-type X R) Q q)
  (QR : Set l5) (qR : reflecting-map-equivalence-relation R (type-Set QR))
  (UqR : is-set-quotient R QR qR)
  where

  is-emb-inclusion-is-set-quotient-equivalence-relation-function-type :
    is-emb
      ( map-inclusion-is-set-quotient-equivalence-relation-function-type
        X R Q q Uq QR qR UqR)
  is-emb-inclusion-is-set-quotient-equivalence-relation-function-type = {!!}
```

### The extension of the universal map from `hom-equivalence-relation R S` to `A/R → B/S` to the quotient is an embedding

#### First variant using only the universal property of the set quotient

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  (QR : Set l3) (qR : reflecting-map-equivalence-relation R (type-Set QR))
  (UR : is-set-quotient R QR qR)
  {B : UU l4} (S : equivalence-relation l5 B)
  (QS : Set l6) (qS : reflecting-map-equivalence-relation S (type-Set QS))
  (US : is-set-quotient S QS qS)
  (QH : Set l7)
  (qH :
    reflecting-map-equivalence-relation
      ( equivalence-relation-hom-equivalence-relation R S)
      ( type-Set QH))
  (UH :
    is-set-quotient (equivalence-relation-hom-equivalence-relation R S) QH qH)
  where

  unique-inclusion-is-set-quotient-hom-equivalence-relation :
    is-contr
      ( Σ ( hom-Set QH (hom-set-Set QR QS))
          ( λ μ →
            ( μ ∘
              map-reflecting-map-equivalence-relation
                ( equivalence-relation-hom-equivalence-relation R S)
                ( qH)) ~
            ( universal-map-is-set-quotient-hom-equivalence-relation
                R QR qR UR S QS qS US)))
  unique-inclusion-is-set-quotient-hom-equivalence-relation = {!!}

  inclusion-is-set-quotient-hom-equivalence-relation :
    hom-Set QH (hom-set-Set QR QS)
  inclusion-is-set-quotient-hom-equivalence-relation = {!!}

  triangle-inclusion-is-set-quotient-hom-equivalence-relation :
    ( inclusion-is-set-quotient-hom-equivalence-relation ∘
      map-reflecting-map-equivalence-relation
        ( equivalence-relation-hom-equivalence-relation R S)
        ( qH)) ~
    ( universal-map-is-set-quotient-hom-equivalence-relation
        R QR qR UR S QS qS US)
  triangle-inclusion-is-set-quotient-hom-equivalence-relation = {!!}

  is-emb-inclusion-is-set-quotient-hom-equivalence-relation :
    is-emb inclusion-is-set-quotient-hom-equivalence-relation
  is-emb-inclusion-is-set-quotient-hom-equivalence-relation = {!!}

  emb-inclusion-is-set-quotient-hom-equivalence-relation :
    type-Set QH ↪ hom-Set QR QS
  emb-inclusion-is-set-quotient-hom-equivalence-relation = {!!}
```

#### Second variant using the official set quotients

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  quotient-hom-equivalence-relation-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-hom-equivalence-relation-Set = {!!}

  set-quotient-hom-equivalence-relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  set-quotient-hom-equivalence-relation = {!!}

  is-set-set-quotient-hom-equivalence-relation :
    is-set set-quotient-hom-equivalence-relation
  is-set-set-quotient-hom-equivalence-relation = {!!}

  reflecting-map-quotient-map-hom-equivalence-relation :
    reflecting-map-equivalence-relation
      ( equivalence-relation-hom-equivalence-relation R S)
      ( set-quotient-hom-equivalence-relation)
  reflecting-map-quotient-map-hom-equivalence-relation = {!!}

  quotient-map-hom-equivalence-relation :
    hom-equivalence-relation R S → set-quotient-hom-equivalence-relation
  quotient-map-hom-equivalence-relation = {!!}

  is-set-quotient-set-quotient-hom-equivalence-relation :
    is-set-quotient
      ( equivalence-relation-hom-equivalence-relation R S)
      ( quotient-hom-equivalence-relation-Set)
      ( reflecting-map-quotient-map-hom-equivalence-relation)
  is-set-quotient-set-quotient-hom-equivalence-relation = {!!}

  unique-inclusion-set-quotient-hom-equivalence-relation :
    is-contr
      ( Σ ( set-quotient-hom-equivalence-relation →
            set-quotient R → set-quotient S)
          ( λ μ →
            μ ∘
            quotient-map (equivalence-relation-hom-equivalence-relation R S) ~
            universal-map-set-quotient-hom-equivalence-relation R S))
  unique-inclusion-set-quotient-hom-equivalence-relation = {!!}

  inclusion-set-quotient-hom-equivalence-relation :
    set-quotient (equivalence-relation-hom-equivalence-relation R S) →
    set-quotient R → set-quotient S
  inclusion-set-quotient-hom-equivalence-relation = {!!}

  triangle-inclusion-set-quotient-hom-equivalence-relation :
    ( inclusion-set-quotient-hom-equivalence-relation ∘
      quotient-map (equivalence-relation-hom-equivalence-relation R S)) ~
    ( universal-map-set-quotient-hom-equivalence-relation R S)
  triangle-inclusion-set-quotient-hom-equivalence-relation = {!!}

  is-emb-inclusion-set-quotient-hom-equivalence-relation :
    is-emb inclusion-set-quotient-hom-equivalence-relation
  is-emb-inclusion-set-quotient-hom-equivalence-relation = {!!}

  emb-inclusion-set-quotient-hom-equivalence-relation :
    set-quotient (equivalence-relation-hom-equivalence-relation R S) ↪
    ( set-quotient R → set-quotient S)
  emb-inclusion-set-quotient-hom-equivalence-relation = {!!}
```
