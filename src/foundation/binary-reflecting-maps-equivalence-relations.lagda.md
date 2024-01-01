# Binary reflecting maps of equivalence relations

```agda
module foundation.binary-reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Consider two types `A` and `B` equipped with equivalence relations `R` and `S`.
A binary reflecting map from `A` to `B` to `X` is a binary map `f : A → B → X`
such that for any to `R`-related elements `x` and `x'` in `A` and any two
`S`-related elements `y` and `y'` in `B` we have `f x y ＝ f x' y'` in `X`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (R : equivalence-relation l3 A) (S : equivalence-relation l4 B)
  where

  binary-reflects-equivalence-relation :
    {X : UU l5} (f : A → B → X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflects-equivalence-relation = {!!}

  binary-reflecting-map-equivalence-relation :
    (X : UU l5) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflecting-map-equivalence-relation = {!!}

  map-binary-reflecting-map-equivalence-relation :
    {X : UU l5} → binary-reflecting-map-equivalence-relation X → A → B → X
  map-binary-reflecting-map-equivalence-relation = {!!}

  reflects-binary-reflecting-map-equivalence-relation :
    {X : UU l5} (f : binary-reflecting-map-equivalence-relation X) →
    binary-reflects-equivalence-relation
      ( map-binary-reflecting-map-equivalence-relation f)
  reflects-binary-reflecting-map-equivalence-relation = {!!}

  is-prop-binary-reflects-equivalence-relation :
    (X : Set l5) (f : A → B → type-Set X) →
    is-prop (binary-reflects-equivalence-relation f)
  is-prop-binary-reflects-equivalence-relation = {!!}

  binary-reflects-prop-equivalence-relation :
    (X : Set l5) (f : A → B → type-Set X) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflects-prop-equivalence-relation = {!!}
```

### Characterizing the identity type of binary reflecting maps into sets

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  (C : Set l5) (f : binary-reflecting-map-equivalence-relation R S (type-Set C))
  where

  htpy-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    UU (l1 ⊔ l3 ⊔ l5)
  htpy-binary-reflecting-map-equivalence-relation = {!!}

  refl-htpy-binary-reflecting-map-equivalence-relation :
    htpy-binary-reflecting-map-equivalence-relation f
  refl-htpy-binary-reflecting-map-equivalence-relation = {!!}

  htpy-eq-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    (f ＝ g) → htpy-binary-reflecting-map-equivalence-relation g
  htpy-eq-binary-reflecting-map-equivalence-relation = {!!}

  is-torsorial-htpy-binary-reflecting-map-equivalence-relation :
    is-torsorial (htpy-binary-reflecting-map-equivalence-relation)
  is-torsorial-htpy-binary-reflecting-map-equivalence-relation = {!!}

  is-equiv-htpy-eq-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    is-equiv (htpy-eq-binary-reflecting-map-equivalence-relation g)
  is-equiv-htpy-eq-binary-reflecting-map-equivalence-relation = {!!}

  extensionality-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    (f ＝ g) ≃ htpy-binary-reflecting-map-equivalence-relation g
  extensionality-binary-reflecting-map-equivalence-relation = {!!}

  eq-htpy-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    htpy-binary-reflecting-map-equivalence-relation g → (f ＝ g)
  eq-htpy-binary-reflecting-map-equivalence-relation = {!!}
```
