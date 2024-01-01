# Decidable equivalence relations

```agda
module foundation.decidable-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-relations
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.images
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.slice
open import foundation.surjective-maps
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A decidable equivalence relation on a type `X` is an equivalence relation `R` on
`X` such that `R x y` is a decidable proposition for each `x y : X`.

## Definitions

### Decidable equivalence relations

```agda
is-decidable-equivalence-relation :
  {l1 l2 : Level} → {A : UU l1} → equivalence-relation l2 A → UU (l1 ⊔ l2)
is-decidable-equivalence-relation = {!!}

Decidable-equivalence-relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-equivalence-relation = {!!}

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-equivalence-relation l2 X)
  where

  decidable-relation-Decidable-equivalence-relation :
    Decidable-Relation l2 X
  decidable-relation-Decidable-equivalence-relation = {!!}

  relation-Decidable-equivalence-relation : X → X → Prop l2
  relation-Decidable-equivalence-relation = {!!}

  sim-Decidable-equivalence-relation : X → X → UU l2
  sim-Decidable-equivalence-relation = {!!}

  is-prop-sim-Decidable-equivalence-relation :
    (x y : X) → is-prop (sim-Decidable-equivalence-relation x y)
  is-prop-sim-Decidable-equivalence-relation = {!!}

  is-decidable-sim-Decidable-equivalence-relation :
    (x y : X) → is-decidable (sim-Decidable-equivalence-relation x y)
  is-decidable-sim-Decidable-equivalence-relation = {!!}

  is-equivalence-relation-Decidable-equivalence-relation :
    is-equivalence-relation relation-Decidable-equivalence-relation
  is-equivalence-relation-Decidable-equivalence-relation = {!!}

  equivalence-relation-Decidable-equivalence-relation :
    equivalence-relation l2 X
  equivalence-relation-Decidable-equivalence-relation = {!!}

  refl-Decidable-equivalence-relation :
    is-reflexive sim-Decidable-equivalence-relation
  refl-Decidable-equivalence-relation = {!!}

  symmetric-Decidable-equivalence-relation :
    is-symmetric sim-Decidable-equivalence-relation
  symmetric-Decidable-equivalence-relation = {!!}

  equiv-symmetric-Decidable-equivalence-relation :
    {x y : X} →
    sim-Decidable-equivalence-relation x y ≃
    sim-Decidable-equivalence-relation y x
  equiv-symmetric-Decidable-equivalence-relation = {!!}

  transitive-Decidable-equivalence-relation :
    is-transitive sim-Decidable-equivalence-relation
  transitive-Decidable-equivalence-relation = {!!}

equiv-equivalence-relation-is-decidable-Dec-equivalence-relation :
  {l1 l2 : Level} {X : UU l1} →
  Decidable-equivalence-relation l2 X ≃
  Σ ( equivalence-relation l2 X)
    ( λ R → is-decidable-equivalence-relation R)
equiv-equivalence-relation-is-decidable-Dec-equivalence-relation = {!!}
pr2 equiv-equivalence-relation-is-decidable-Dec-equivalence-relation = {!!}
```

### Equivalence classes of decidable equivalence relations

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-equivalence-relation l2 X)
  where

  is-equivalence-class-Decidable-equivalence-relation :
    decidable-subtype l2 X → UU (l1 ⊔ lsuc l2)
  is-equivalence-class-Decidable-equivalence-relation = {!!}

  equivalence-class-Decidable-equivalence-relation : UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-equivalence-relation = {!!}

  class-Decidable-equivalence-relation :
    X → equivalence-class-Decidable-equivalence-relation
  class-Decidable-equivalence-relation = {!!}

  emb-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation ↪ decidable-subtype l2 X
  emb-equivalence-class-Decidable-equivalence-relation = {!!}

  decidable-subtype-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation → decidable-subtype l2 X
  decidable-subtype-equivalence-class-Decidable-equivalence-relation = {!!}

  subtype-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation → subtype l2 X
  subtype-equivalence-class-Decidable-equivalence-relation = {!!}

  is-in-subtype-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation → X → UU l2
  is-in-subtype-equivalence-class-Decidable-equivalence-relation = {!!}

  is-prop-is-in-subtype-equivalence-class-Decidable-equivalence-relation :
    (P : equivalence-class-Decidable-equivalence-relation) (x : X) →
    is-prop (is-in-subtype-equivalence-class-Decidable-equivalence-relation P x)
  is-prop-is-in-subtype-equivalence-class-Decidable-equivalence-relation = {!!}

  is-set-equivalence-class-Decidable-equivalence-relation :
    is-set equivalence-class-Decidable-equivalence-relation
  is-set-equivalence-class-Decidable-equivalence-relation = {!!}

  equivalence-class-Decidable-equivalence-relation-Set : Set (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-equivalence-relation-Set = {!!}

  unit-im-equivalence-class-Decidable-equivalence-relation :
    hom-slice
      ( decidable-relation-Decidable-equivalence-relation R)
      ( decidable-subtype-equivalence-class-Decidable-equivalence-relation)
  unit-im-equivalence-class-Decidable-equivalence-relation = {!!}

  is-image-equivalence-class-Decidable-equivalence-relation :
    is-image
      ( decidable-relation-Decidable-equivalence-relation R)
      ( emb-equivalence-class-Decidable-equivalence-relation)
      ( unit-im-equivalence-class-Decidable-equivalence-relation)
  is-image-equivalence-class-Decidable-equivalence-relation = {!!}

  is-surjective-class-Decidable-equivalence-relation :
    is-surjective class-Decidable-equivalence-relation
  is-surjective-class-Decidable-equivalence-relation = {!!}
```

## Properties

### We characterize the identity type of the equivalence classes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A) (a : A)
  where

  abstract
    center-total-subtype-equivalence-class-Decidable-equivalence-relation :
      Σ ( equivalence-class-Decidable-equivalence-relation R)
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-equivalence-relation R P a)
    center-total-subtype-equivalence-class-Decidable-equivalence-relation = {!!}

    contraction-total-subtype-equivalence-class-Decidable-equivalence-relation :
      ( t :
        Σ ( equivalence-class-Decidable-equivalence-relation R)
          ( λ P →
            is-in-subtype-equivalence-class-Decidable-equivalence-relation
              R P a)) →
      center-total-subtype-equivalence-class-Decidable-equivalence-relation ＝ t
    contraction-total-subtype-equivalence-class-Decidable-equivalence-relation = {!!}

    is-torsorial-subtype-equivalence-class-Decidable-equivalence-relation :
      is-torsorial
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-equivalence-relation R P a)
    is-torsorial-subtype-equivalence-class-Decidable-equivalence-relation = {!!}

  related-eq-quotient-Decidable-equivalence-relation :
    (q : equivalence-class-Decidable-equivalence-relation R) →
      class-Decidable-equivalence-relation R a ＝ q →
    is-in-subtype-equivalence-class-Decidable-equivalence-relation R q a
  related-eq-quotient-Decidable-equivalence-relation = {!!}

  abstract
    is-equiv-related-eq-quotient-Decidable-equivalence-relation :
      (q : equivalence-class-Decidable-equivalence-relation R) →
      is-equiv (related-eq-quotient-Decidable-equivalence-relation q)
    is-equiv-related-eq-quotient-Decidable-equivalence-relation = {!!}

  abstract
    effective-quotient-Decidable-equivalence-relation' :
      (q : equivalence-class-Decidable-equivalence-relation R) →
      ( class-Decidable-equivalence-relation R a ＝ q) ≃
      ( is-in-subtype-equivalence-class-Decidable-equivalence-relation R q a)
    effective-quotient-Decidable-equivalence-relation' = {!!}

  abstract
    eq-effective-quotient-Decidable-equivalence-relation' :
      (q : equivalence-class-Decidable-equivalence-relation R) →
      is-in-subtype-equivalence-class-Decidable-equivalence-relation R q a →
      class-Decidable-equivalence-relation R a ＝ q
    eq-effective-quotient-Decidable-equivalence-relation' = {!!}
```

### The quotient map into the large set quotient is effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  abstract
    is-effective-class-Decidable-equivalence-relation :
      is-effective
        ( equivalence-relation-Decidable-equivalence-relation R)
        ( class-Decidable-equivalence-relation R)
    is-effective-class-Decidable-equivalence-relation = {!!}

  abstract
    apply-effectiveness-class-Decidable-equivalence-relation :
      {x y : A} →
      ( class-Decidable-equivalence-relation R x ＝
        class-Decidable-equivalence-relation R y) →
      sim-Decidable-equivalence-relation R x y
    apply-effectiveness-class-Decidable-equivalence-relation = {!!}

  abstract
    apply-effectiveness-class-Decidable-equivalence-relation' :
      {x y : A} → sim-Decidable-equivalence-relation R x y →
      class-Decidable-equivalence-relation R x ＝
      class-Decidable-equivalence-relation R y
    apply-effectiveness-class-Decidable-equivalence-relation' = {!!}
```

### The quotient map into the large set quotient is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  is-surjective-and-effective-class-Decidable-equivalence-relation :
    is-surjective-and-effective
      ( equivalence-relation-Decidable-equivalence-relation R)
      ( class-Decidable-equivalence-relation R)
  is-surjective-and-effective-class-Decidable-equivalence-relation = {!!}
```

### The quotient map into the large set quotient is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  quotient-reflecting-map-equivalence-class-Decidable-equivalence-relation :
    reflecting-map-equivalence-relation
      ( equivalence-relation-Decidable-equivalence-relation R)
      ( equivalence-class-Decidable-equivalence-relation R)
  quotient-reflecting-map-equivalence-class-Decidable-equivalence-relation = {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  transitive-is-in-subtype-equivalence-class-Decidable-equivalence-relation :
    (P : equivalence-class-Decidable-equivalence-relation R) (a b : A) →
    is-in-subtype-equivalence-class-Decidable-equivalence-relation R P a →
    sim-Decidable-equivalence-relation R a b →
    is-in-subtype-equivalence-class-Decidable-equivalence-relation R P b
  transitive-is-in-subtype-equivalence-class-Decidable-equivalence-relation = {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-decidable-is-in-equivalence-class-is-decidable :
    ((a b : A) → is-decidable (sim-equivalence-relation R a b)) →
    (T : equivalence-class R) →
    (a : A) →
    is-decidable (is-in-equivalence-class R T a)
  is-decidable-is-in-equivalence-class-is-decidable = {!!}
```

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a type with decidable equality

```agda
has-decidable-equality-type-Surjection-Into-Set :
  {l1 : Level} {A : UU l1} (surj : Surjection-Into-Set l1 A) →
  ( is-decidable-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set surj)) →
  has-decidable-equality (type-Surjection-Into-Set surj)
has-decidable-equality-type-Surjection-Into-Set = {!!}

is-decidable-equivalence-relation-Surjection-Into-Set :
  {l1 : Level} {A : UU l1} (surj : Surjection-Into-Set l1 A) →
  has-decidable-equality (type-Surjection-Into-Set surj) →
  is-decidable-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set surj)
is-decidable-equivalence-relation-Surjection-Into-Set = {!!}

equiv-Surjection-Into-Set-Decidable-equivalence-relation :
  {l1 : Level} (A : UU l1) →
  Decidable-equivalence-relation l1 A ≃
  Σ (UU l1) (λ X → (A ↠ X) × has-decidable-equality X)
equiv-Surjection-Into-Set-Decidable-equivalence-relation = {!!}
```
