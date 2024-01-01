# Equivalence classes

```agda
module foundation.equivalence-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.inhabited-subtypes
open import foundation.locally-small-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.slice
open import foundation.small-types
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-image
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An equivalence class of an equivalence relation `R` on `A` is a subtype of `A`
that is merely equivalent to a subtype of the form `R x`. The type of
equivalence classes of an equivalence relation satisfies the universal property
of the set quotient.

## Definition

### The condition on subtypes of `A` of being an equivalence class

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-equivalence-class-Prop : subtype l2 A → Prop (l1 ⊔ l2)
  is-equivalence-class-Prop = {!!}

  is-equivalence-class : subtype l2 A → UU (l1 ⊔ l2)
  is-equivalence-class = {!!}

  is-prop-is-equivalence-class :
    (P : subtype l2 A) → is-prop (is-equivalence-class P)
  is-prop-is-equivalence-class = {!!}
```

### The condition on inhabited subtypes of `A` of being an equivalence class

```agda
  is-equivalence-class-inhabited-subtype-equivalence-relation :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-equivalence-class-inhabited-subtype-equivalence-relation = {!!}
```

### The type of equivalence classes

```agda
  equivalence-class : UU (l1 ⊔ lsuc l2)
  equivalence-class = {!!}

  class : A → equivalence-class
  class = {!!}

  emb-equivalence-class : equivalence-class ↪ subtype l2 A
  emb-equivalence-class = {!!}

  subtype-equivalence-class : equivalence-class → subtype l2 A
  subtype-equivalence-class = {!!}

  is-equivalence-class-equivalence-class :
    (C : equivalence-class) → is-equivalence-class (subtype-equivalence-class C)
  is-equivalence-class-equivalence-class = {!!}

  is-inhabited-subtype-equivalence-class :
    (C : equivalence-class) → is-inhabited-subtype (subtype-equivalence-class C)
  is-inhabited-subtype-equivalence-class = {!!}

  inhabited-subtype-equivalence-class :
    (C : equivalence-class) → inhabited-subtype l2 A
  inhabited-subtype-equivalence-class = {!!}

  is-in-equivalence-class : equivalence-class → (A → UU l2)
  is-in-equivalence-class = {!!}

  abstract
    is-prop-is-in-equivalence-class :
      (x : equivalence-class) (a : A) →
      is-prop (is-in-equivalence-class x a)
    is-prop-is-in-equivalence-class = {!!}

  is-in-equivalence-class-Prop : equivalence-class → (A → Prop l2)
  is-in-equivalence-class-Prop = {!!}

  abstract
    is-set-equivalence-class : is-set equivalence-class
    is-set-equivalence-class = {!!}

  equivalence-class-Set : Set (l1 ⊔ lsuc l2)
  equivalence-class-Set = {!!}

  unit-im-equivalence-class :
    hom-slice (prop-equivalence-relation R) subtype-equivalence-class
  unit-im-equivalence-class = {!!}

  is-surjective-class : is-surjective class
  is-surjective-class = {!!}

  is-image-equivalence-class :
    is-image
      ( prop-equivalence-relation R)
      ( emb-equivalence-class)
      ( unit-im-equivalence-class)
  is-image-equivalence-class = {!!}
```

## Properties

### Characterization of equality of equivalence classes

#### Equivalence classes are equal if they contain the same elements

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  has-same-elements-equivalence-class :
    (C D : equivalence-class R) → UU (l1 ⊔ l2)
  has-same-elements-equivalence-class = {!!}

  refl-has-same-elements-equivalence-class :
    (C : equivalence-class R) → has-same-elements-equivalence-class C C
  refl-has-same-elements-equivalence-class = {!!}

  is-torsorial-has-same-elements-equivalence-class :
    (C : equivalence-class R) →
    is-torsorial (has-same-elements-equivalence-class C)
  is-torsorial-has-same-elements-equivalence-class = {!!}

  has-same-elements-eq-equivalence-class :
    (C D : equivalence-class R) → (C ＝ D) →
    has-same-elements-equivalence-class C D
  has-same-elements-eq-equivalence-class = {!!}

  is-equiv-has-same-elements-eq-equivalence-class :
    (C D : equivalence-class R) →
    is-equiv (has-same-elements-eq-equivalence-class C D)
  is-equiv-has-same-elements-eq-equivalence-class = {!!}

  extensionality-equivalence-class :
    (C D : equivalence-class R) →
    (C ＝ D) ≃ has-same-elements-equivalence-class C D
  extensionality-equivalence-class = {!!}

  eq-has-same-elements-equivalence-class :
    (C D : equivalence-class R) →
    has-same-elements-equivalence-class C D → C ＝ D
  eq-has-same-elements-equivalence-class = {!!}
```

#### Equivalence classes are equal if there exists an element contained in both

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  share-common-element-equivalence-class-Prop :
    (C D : equivalence-class R) → Prop (l1 ⊔ l2)
  share-common-element-equivalence-class-Prop = {!!}

  share-common-element-equivalence-class :
    (C D : equivalence-class R) → UU (l1 ⊔ l2)
  share-common-element-equivalence-class = {!!}

  abstract
    eq-share-common-element-equivalence-class :
      (C D : equivalence-class R) →
      share-common-element-equivalence-class C D → C ＝ D
    eq-share-common-element-equivalence-class = {!!}

  eq-class-equivalence-class :
    (C : equivalence-class R) {a : A} →
    is-in-equivalence-class R C a → class R a ＝ C
  eq-class-equivalence-class = {!!}
```

### The type of equivalence classes containing a fixed element `a : A` is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) (a : A)
  where

  center-total-is-in-equivalence-class :
    Σ (equivalence-class R) (λ P → is-in-equivalence-class R P a)
  center-total-is-in-equivalence-class = {!!}

  contraction-total-is-in-equivalence-class :
    ( t :
      Σ ( equivalence-class R)
        ( λ C → is-in-equivalence-class R C a)) →
    center-total-is-in-equivalence-class ＝ t
  contraction-total-is-in-equivalence-class = {!!}

  is-torsorial-is-in-equivalence-class :
    is-torsorial (λ P → is-in-equivalence-class R P a)
  is-torsorial-is-in-equivalence-class = {!!}

  is-in-equivalence-class-eq-equivalence-class :
    (q : equivalence-class R) → class R a ＝ q →
    is-in-equivalence-class R q a
  is-in-equivalence-class-eq-equivalence-class = {!!}

  abstract
    is-equiv-is-in-equivalence-class-eq-equivalence-class :
      (q : equivalence-class R) →
      is-equiv (is-in-equivalence-class-eq-equivalence-class q)
    is-equiv-is-in-equivalence-class-eq-equivalence-class = {!!}
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  abstract
    effective-quotient' :
      (a : A) (q : equivalence-class R) →
      ( class R a ＝ q) ≃
      ( is-in-equivalence-class R q a)
    effective-quotient' = {!!}

  abstract
    eq-effective-quotient' :
      (a : A) (q : equivalence-class R) → is-in-equivalence-class R q a →
      class R a ＝ q
    eq-effective-quotient' = {!!}

  abstract
    is-effective-class :
      is-effective R (class R)
    is-effective-class = {!!}

  abstract
    apply-effectiveness-class :
      {x y : A} → class R x ＝ class R y → sim-equivalence-relation R x y
    apply-effectiveness-class = {!!}

  abstract
    apply-effectiveness-class' :
      {x y : A} → sim-equivalence-relation R x y → class R x ＝ class R y
    apply-effectiveness-class' = {!!}
```

### The map `class` into the type of equivalence classes is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-surjective-and-effective-class :
    is-surjective-and-effective R (class R)
  is-surjective-and-effective-class = {!!}
```

### The map `class` into the type of equivalence classes is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  quotient-reflecting-map-equivalence-class :
    reflecting-map-equivalence-relation R (equivalence-class R)
  quotient-reflecting-map-equivalence-class = {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  transitive-is-in-equivalence-class :
    (P : equivalence-class R) (a b : A) →
    is-in-equivalence-class R P a → sim-equivalence-relation R a b →
    is-in-equivalence-class R P b
  transitive-is-in-equivalence-class = {!!}
```

### The type of equivalence classes is locally small

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-locally-small-equivalence-class :
    is-locally-small (l1 ⊔ l2) (equivalence-class R)
  is-locally-small-equivalence-class = {!!}
```

### The type of equivalence classes is small

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-small-equivalence-class : is-small (l1 ⊔ l2) (equivalence-class R)
  is-small-equivalence-class = {!!}

  equivalence-class-Small-Type : Small-Type (l1 ⊔ l2) (l1 ⊔ lsuc l2)
  equivalence-class-Small-Type = {!!}

  small-equivalence-class : UU (l1 ⊔ l2)
  small-equivalence-class = {!!}
```
