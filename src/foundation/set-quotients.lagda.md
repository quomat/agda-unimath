# Set quotients

```agda
module foundation.set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.embeddings
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.slice
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-image
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.small-types
open import foundation-core.subtypes
open import foundation-core.whiskering-homotopies
```

</details>

## Definitions

### Set quotients

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  set-quotient : UU (l1 ⊔ l2)
  set-quotient = {!!}

  compute-set-quotient : equivalence-class R ≃ set-quotient
  compute-set-quotient = {!!}

  set-quotient-equivalence-class : equivalence-class R → set-quotient
  set-quotient-equivalence-class = {!!}

  equivalence-class-set-quotient : set-quotient → equivalence-class R
  equivalence-class-set-quotient = {!!}

  is-section-equivalence-class-set-quotient :
    (set-quotient-equivalence-class ∘ equivalence-class-set-quotient) ~ id
  is-section-equivalence-class-set-quotient = {!!}

  is-retraction-equivalence-class-set-quotient :
    (equivalence-class-set-quotient ∘ set-quotient-equivalence-class) ~ id
  is-retraction-equivalence-class-set-quotient = {!!}

  emb-equivalence-class-set-quotient : set-quotient ↪ equivalence-class R
  emb-equivalence-class-set-quotient = {!!}

  emb-set-quotient-equivalence-class : equivalence-class R ↪ set-quotient
  emb-set-quotient-equivalence-class = {!!}

  quotient-map : A → set-quotient
  quotient-map = {!!}

  is-surjective-quotient-map : is-surjective quotient-map
  is-surjective-quotient-map = {!!}

  surjection-quotient-map : A ↠ set-quotient
  pr1 surjection-quotient-map = {!!}

  emb-subtype-set-quotient : set-quotient ↪ subtype l2 A
  emb-subtype-set-quotient = {!!}

  subtype-set-quotient : set-quotient → subtype l2 A
  subtype-set-quotient = {!!}

  is-inhabited-subtype-set-quotient :
    (x : set-quotient) → is-inhabited-subtype (subtype-set-quotient x)
  is-inhabited-subtype-set-quotient = {!!}

  inhabited-subtype-set-quotient : set-quotient → inhabited-subtype l2 A
  inhabited-subtype-set-quotient = {!!}

  is-in-equivalence-class-set-quotient :
    (x : set-quotient) → A → UU l2
  is-in-equivalence-class-set-quotient = {!!}

  is-prop-is-in-equivalence-class-set-quotient :
    (x : set-quotient) (a : A) →
    is-prop (is-in-equivalence-class-set-quotient x a)
  is-prop-is-in-equivalence-class-set-quotient = {!!}

  is-in-equivalence-class-set-quotient-Prop :
    (x : set-quotient) → (A → Prop l2)
  is-in-equivalence-class-set-quotient-Prop = {!!}

  is-set-set-quotient : is-set set-quotient
  is-set-set-quotient = {!!}

  quotient-Set : Set (l1 ⊔ l2)
  pr1 quotient-Set = {!!}

  unit-im-set-quotient :
    hom-slice (prop-equivalence-relation R) subtype-set-quotient
  unit-im-set-quotient = {!!}

  is-image-set-quotient :
    is-image
      ( prop-equivalence-relation R)
      ( emb-subtype-set-quotient)
      ( unit-im-set-quotient)
  is-image-set-quotient = {!!}
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-effective-quotient-map : is-effective R (quotient-map R)
  is-effective-quotient-map x y = {!!}

  apply-effectiveness-quotient-map :
    {x y : A} → quotient-map R x ＝ quotient-map R y →
    sim-equivalence-relation R x y
  apply-effectiveness-quotient-map = {!!}

  apply-effectiveness-quotient-map' :
    {x y : A} → sim-equivalence-relation R x y →
    quotient-map R x ＝ quotient-map R y
  apply-effectiveness-quotient-map' = {!!}

  is-surjective-and-effective-quotient-map :
    is-surjective-and-effective R (quotient-map R)
  is-surjective-and-effective-quotient-map = {!!}

  reflecting-map-quotient-map :
    reflecting-map-equivalence-relation R (set-quotient R)
  reflecting-map-quotient-map = {!!}
```

### The set quotient of `R` is a set quotient of `R`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-set-quotient-set-quotient :
    is-set-quotient R (quotient-Set R) (reflecting-map-quotient-map R)
  is-set-quotient-set-quotient = {!!}

  inv-precomp-set-quotient :
    {l : Level} (X : Set l) →
    reflecting-map-equivalence-relation R (type-Set X) →
    hom-Set (quotient-Set R) X
  inv-precomp-set-quotient = {!!}

  is-section-inv-precomp-set-quotient :
    {l : Level} (X : Set l) →
    (f : reflecting-map-equivalence-relation R (type-Set X)) →
    (a : A) →
    inv-precomp-set-quotient X f (quotient-map R a) ＝
      map-reflecting-map-equivalence-relation R f a
  is-section-inv-precomp-set-quotient = {!!}

  is-retraction-inv-precomp-set-quotient :
    {l : Level} (X : Set l) (f : hom-Set (quotient-Set R) X) →
    inv-precomp-set-quotient X
      ( precomp-Set-Quotient R
        ( quotient-Set R)
        ( reflecting-map-quotient-map R)
        ( X)
        ( f)) ＝
    f
  is-retraction-inv-precomp-set-quotient = {!!}
```

### Induction into propositions on the set quotient

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  equiv-induction-set-quotient :
    {l : Level} (P : set-quotient R → Prop l) →
    ((y : set-quotient R) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (quotient-map R x)))
  equiv-induction-set-quotient = {!!}

  induction-set-quotient :
    {l : Level} (P : set-quotient R → Prop l) →
    ((x : A) → type-Prop (P (quotient-map R x))) →
    ((y : set-quotient R) → type-Prop (P y))
  induction-set-quotient = {!!}
```

### Double induction for set quotients

#### The most general case

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  (P : set-quotient R → set-quotient S → Prop l5)
  where

  equiv-double-induction-set-quotient :
    ((x : set-quotient R) (y : set-quotient S) → type-Prop (P x y)) ≃
    ( (x : A) (y : B) →
      type-Prop (P (quotient-map R x) (quotient-map S y)))
  equiv-double-induction-set-quotient = {!!}

  double-induction-set-quotient :
    ( (x : A) (y : B) →
      type-Prop (P (quotient-map R x) (quotient-map S y))) →
    (x : set-quotient R) (y : set-quotient S) → type-Prop (P x y)
  double-induction-set-quotient = {!!}
```

#### Double induction over a single set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (P : (x y : set-quotient R) → Prop l3)
  where

  equiv-double-induction-set-quotient' :
    ((x y : set-quotient R) → type-Prop (P x y)) ≃
    ((x y : A) → type-Prop (P (quotient-map R x) (quotient-map R y)))
  equiv-double-induction-set-quotient' = {!!}

  double-induction-set-quotient' :
    ( (x y : A) →
      type-Prop (P (quotient-map R x) (quotient-map R y))) →
    (x y : set-quotient R) → type-Prop (P x y)
  double-induction-set-quotient' = {!!}
```

### Triple induction for set quotients

#### The most general case

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5} (T : equivalence-relation l6 C)
  (P : set-quotient R → set-quotient S → set-quotient T → Prop l7)
  where

  equiv-triple-induction-set-quotient :
    ( (x : set-quotient R) (y : set-quotient S) (z : set-quotient T) →
      type-Prop (P x y z)) ≃
    ( (x : A) (y : B) (z : C) →
      type-Prop
        ( P (quotient-map R x) (quotient-map S y) (quotient-map T z)))
  equiv-triple-induction-set-quotient = {!!}

  triple-induction-set-quotient :
    ( (x : A) (y : B) (z : C) →
      type-Prop
        ( P ( quotient-map R x)
            ( quotient-map S y)
            ( quotient-map T z))) →
    ( x : set-quotient R) (y : set-quotient S)
    ( z : set-quotient T) → type-Prop (P x y z)
  triple-induction-set-quotient = {!!}
```

#### Triple induction over a single set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (P : (x y z : set-quotient R) → Prop l3)
  where

  equiv-triple-induction-set-quotient' :
    ((x y z : set-quotient R) → type-Prop (P x y z)) ≃
    ( (x y z : A) →
      type-Prop
        ( P (quotient-map R x) (quotient-map R y) (quotient-map R z)))
  equiv-triple-induction-set-quotient' = {!!}

  triple-induction-set-quotient' :
    ( (x y z : A) →
      type-Prop
        ( P ( quotient-map R x)
            ( quotient-map R y)
            ( quotient-map R z))) →
    ( x y z : set-quotient R) → type-Prop (P x y z)
  triple-induction-set-quotient' = {!!}
```

### Every set quotient is equivalent to the set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (Uf : is-set-quotient R B f)
  where

  equiv-uniqueness-set-quotient-set-quotient :
    set-quotient R ≃ type-Set B
  equiv-uniqueness-set-quotient-set-quotient = {!!}
```
